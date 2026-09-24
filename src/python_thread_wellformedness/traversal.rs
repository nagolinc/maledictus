//! Walks source functions and tracks local nominal/thread types across statement scopes.

use std::collections::BTreeSet;

use rustpython_parser::ast;

use super::bindings::target_bound_names;
use super::calls::{annotation_class, annotation_is_thread, callee_is_thread};
use super::expressions::validate_expression;
use super::{Bindings, Candidate, Catalog, FunctionContext};

pub(super) fn validate_function(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    catalog: &Catalog,
    candidates: &mut Vec<Candidate>,
    enclosing_class: Option<&str>,
) {
    let mut context = FunctionContext::default();
    for argument in function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .chain(function.args.kwonlyargs.iter())
    {
        context.local_names.insert(argument.def.arg.to_string());
        if annotation_is_thread(argument.def.annotation.as_deref(), bindings) {
            context.thread_locals.insert(argument.def.arg.to_string());
        } else if let Some(class) = annotation_class(argument.def.annotation.as_deref(), catalog) {
            context
                .nominal_locals
                .insert(argument.def.arg.to_string(), class.to_owned());
        }
    }
    if let Some(receiver) = function.args.args.first()
        && let Some(class) = enclosing_class
    {
        context
            .nominal_locals
            .insert(receiver.def.arg.to_string(), class.to_owned());
    }
    collect_function_locals(&function.body, &mut context.local_names);
    validate_statements(&function.body, bindings, catalog, &mut context, candidates);
}

fn collect_function_locals(statements: &[ast::Stmt], names: &mut BTreeSet<String>) {
    for statement in statements {
        match statement {
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    names.extend(target_bound_names(target));
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                names.extend(target_bound_names(&assignment.target));
            }
            ast::Stmt::For(loop_) => {
                names.extend(target_bound_names(&loop_.target));
                collect_function_locals(&loop_.body, names);
                collect_function_locals(&loop_.orelse, names);
            }
            ast::Stmt::If(branch) => {
                collect_function_locals(&branch.body, names);
                collect_function_locals(&branch.orelse, names);
            }
            ast::Stmt::While(loop_) => {
                collect_function_locals(&loop_.body, names);
                collect_function_locals(&loop_.orelse, names);
            }
            ast::Stmt::Try(try_) => {
                collect_function_locals(&try_.body, names);
                collect_function_locals(&try_.orelse, names);
                collect_function_locals(&try_.finalbody, names);
                for handler in &try_.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    if let Some(name) = &handler.name {
                        names.insert(name.to_string());
                    }
                    collect_function_locals(&handler.body, names);
                }
            }
            ast::Stmt::With(with_) => {
                for item in &with_.items {
                    if let Some(target) = &item.optional_vars {
                        names.extend(target_bound_names(target));
                    }
                }
                collect_function_locals(&with_.body, names);
            }
            ast::Stmt::FunctionDef(nested) => {
                names.insert(nested.name.to_string());
            }
            ast::Stmt::ClassDef(nested) => {
                names.insert(nested.name.to_string());
            }
            _ => {}
        }
    }
}

fn validate_statements(
    statements: &[ast::Stmt],
    bindings: &Bindings,
    catalog: &Catalog,
    context: &mut FunctionContext,
    candidates: &mut Vec<Candidate>,
) {
    for statement in statements {
        validate_statement_expressions(statement, bindings, catalog, context, candidates);
        match statement {
            ast::Stmt::Assign(assignment) => {
                if let [ast::Expr::Name(target)] = assignment.targets.as_slice() {
                    update_assignment_type(
                        target.id.as_str(),
                        &assignment.value,
                        bindings,
                        catalog,
                        context,
                    );
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                if let ast::Expr::Name(target) = assignment.target.as_ref() {
                    if annotation_is_thread(Some(&assignment.annotation), bindings) {
                        context.thread_locals.insert(target.id.to_string());
                    } else if let Some(class) =
                        annotation_class(Some(&assignment.annotation), catalog)
                    {
                        context
                            .nominal_locals
                            .insert(target.id.to_string(), class.to_owned());
                    }
                }
            }
            ast::Stmt::If(branch) => {
                let mut body = context.clone();
                validate_statements(&branch.body, bindings, catalog, &mut body, candidates);
                let mut orelse = context.clone();
                validate_statements(&branch.orelse, bindings, catalog, &mut orelse, candidates);
            }
            ast::Stmt::While(loop_) => {
                let mut body = context.clone();
                validate_statements(&loop_.body, bindings, catalog, &mut body, candidates);
                let mut orelse = context.clone();
                validate_statements(&loop_.orelse, bindings, catalog, &mut orelse, candidates);
            }
            ast::Stmt::For(loop_) => {
                let mut body = context.clone();
                validate_statements(&loop_.body, bindings, catalog, &mut body, candidates);
                let mut orelse = context.clone();
                validate_statements(&loop_.orelse, bindings, catalog, &mut orelse, candidates);
            }
            ast::Stmt::Try(try_) => {
                let mut body = context.clone();
                validate_statements(&try_.body, bindings, catalog, &mut body, candidates);
                for handler in &try_.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    let mut handler_context = context.clone();
                    validate_statements(
                        &handler.body,
                        bindings,
                        catalog,
                        &mut handler_context,
                        candidates,
                    );
                }
                let mut orelse = context.clone();
                validate_statements(&try_.orelse, bindings, catalog, &mut orelse, candidates);
                let mut finalbody = context.clone();
                validate_statements(
                    &try_.finalbody,
                    bindings,
                    catalog,
                    &mut finalbody,
                    candidates,
                );
            }
            ast::Stmt::With(with_) => {
                let mut body = context.clone();
                validate_statements(&with_.body, bindings, catalog, &mut body, candidates);
            }
            _ => {}
        }
    }
}

fn update_assignment_type(
    target: &str,
    value: &ast::Expr,
    bindings: &Bindings,
    catalog: &Catalog,
    context: &mut FunctionContext,
) {
    context.thread_locals.remove(target);
    context.nominal_locals.remove(target);
    let ast::Expr::Call(call) = value else {
        return;
    };
    if callee_is_thread(&call.func, bindings, context) {
        context.thread_locals.insert(target.to_owned());
    } else if let ast::Expr::Name(class) = call.func.as_ref()
        && catalog.classes.contains(class.id.as_str())
        && !context.local_names.contains(class.id.as_str())
    {
        context
            .nominal_locals
            .insert(target.to_owned(), class.id.to_string());
    }
}

fn validate_statement_expressions(
    statement: &ast::Stmt,
    bindings: &Bindings,
    catalog: &Catalog,
    context: &FunctionContext,
    candidates: &mut Vec<Candidate>,
) {
    match statement {
        ast::Stmt::Assign(assignment) => validate_expression(
            &assignment.value,
            bindings,
            catalog,
            context,
            candidates,
            false,
            false,
        ),
        ast::Stmt::AnnAssign(assignment) => {
            if let Some(value) = &assignment.value {
                validate_expression(value, bindings, catalog, context, candidates, false, false);
            }
        }
        ast::Stmt::AugAssign(assignment) => validate_expression(
            &assignment.value,
            bindings,
            catalog,
            context,
            candidates,
            false,
            false,
        ),
        ast::Stmt::Expr(expression) => validate_expression(
            &expression.value,
            bindings,
            catalog,
            context,
            candidates,
            false,
            false,
        ),
        ast::Stmt::Return(returned) => {
            if let Some(value) = &returned.value {
                validate_expression(value, bindings, catalog, context, candidates, false, false);
            }
        }
        ast::Stmt::Assert(assertion) => validate_expression(
            &assertion.test,
            bindings,
            catalog,
            context,
            candidates,
            false,
            false,
        ),
        ast::Stmt::If(branch) => validate_expression(
            &branch.test,
            bindings,
            catalog,
            context,
            candidates,
            false,
            false,
        ),
        ast::Stmt::While(loop_) => validate_expression(
            &loop_.test,
            bindings,
            catalog,
            context,
            candidates,
            false,
            false,
        ),
        ast::Stmt::For(loop_) => validate_expression(
            &loop_.iter,
            bindings,
            catalog,
            context,
            candidates,
            false,
            false,
        ),
        ast::Stmt::With(with_) => {
            for item in &with_.items {
                validate_expression(
                    &item.context_expr,
                    bindings,
                    catalog,
                    context,
                    candidates,
                    false,
                    false,
                );
            }
        }
        _ => {}
    }
}
