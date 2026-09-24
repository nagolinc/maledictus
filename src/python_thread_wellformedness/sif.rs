//! Source-bound concurrency restrictions for Nagini's sequential secure-information-flow profile.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_ast::Ranged;
use rustpython_parser::ast;

use super::bindings::{statement_bound_names, target_bound_names};
use super::{CONCURRENCY_IN_SIF, Candidate};
use crate::python_contract_positions::InformationFlowVerificationProfile;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ConcurrencyKind {
    Lock,
    Thread,
}

#[derive(Clone, Default)]
struct TypeBindings {
    active_types: BTreeMap<String, ConcurrencyKind>,
    active_classes: BTreeMap<String, String>,
    lock_modules: BTreeSet<String>,
    thread_modules: BTreeSet<String>,
    declared_classes: BTreeMap<String, ConcurrencyKind>,
    class_fields: BTreeMap<String, BTreeMap<String, ConcurrencyKind>>,
}

#[derive(Clone, Default)]
struct FunctionTypes {
    local_names: BTreeSet<String>,
    values: BTreeMap<String, ConcurrencyKind>,
    nominal_values: BTreeMap<String, String>,
}

pub(super) fn validate_sif_concurrency(
    suite: &ast::Suite,
    profile: InformationFlowVerificationProfile,
    candidates: &mut Vec<Candidate>,
) {
    if !profile.forbids_concurrency() {
        return;
    }
    let bindings = collect_type_bindings(suite);
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                validate_function(function, None, &bindings, candidates);
            }
            ast::Stmt::ClassDef(class) => {
                for statement in &class.body {
                    if let ast::Stmt::FunctionDef(function) = statement {
                        validate_function(
                            function,
                            Some(class.name.as_str()),
                            &bindings,
                            candidates,
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

fn collect_type_bindings(suite: &ast::Suite) -> TypeBindings {
    let mut bindings = TypeBindings::default();
    for statement in suite {
        match statement {
            ast::Stmt::Import(import) => {
                for alias in &import.names {
                    let local = alias.asname.as_ref().map_or_else(
                        || alias.name.as_str().split('.').next().unwrap_or_default(),
                        |name| name.as_str(),
                    );
                    clear_active_binding(&mut bindings, local);
                    if alias.asname.is_some() {
                        match alias.name.as_str() {
                            "nagini_contracts.lock" => {
                                bindings.lock_modules.insert(local.to_owned());
                            }
                            "nagini_contracts.thread" => {
                                bindings.thread_modules.insert(local.to_owned());
                            }
                            _ => {}
                        }
                    }
                }
            }
            ast::Stmt::ImportFrom(import) => {
                let module = import.module.as_ref().map(|name| name.as_str());
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        continue;
                    }
                    let local = alias
                        .asname
                        .as_ref()
                        .map_or(alias.name.as_str(), |name| name.as_str());
                    clear_active_binding(&mut bindings, local);
                    match (module, alias.name.as_str()) {
                        (Some("nagini_contracts.lock"), "Lock") => {
                            bindings
                                .active_types
                                .insert(local.to_owned(), ConcurrencyKind::Lock);
                        }
                        (Some("nagini_contracts.thread"), "Thread") => {
                            bindings
                                .active_types
                                .insert(local.to_owned(), ConcurrencyKind::Thread);
                        }
                        (Some("nagini_contracts"), "lock") => {
                            bindings.lock_modules.insert(local.to_owned());
                        }
                        (Some("nagini_contracts"), "thread") => {
                            bindings.thread_modules.insert(local.to_owned());
                        }
                        _ => {}
                    }
                }
            }
            ast::Stmt::ClassDef(class) => {
                clear_active_binding(&mut bindings, class.name.as_str());
                let kinds = class
                    .bases
                    .iter()
                    .filter_map(|base| resolve_type(base, &bindings))
                    .collect::<BTreeSet<_>>();
                let mut fields = class
                    .bases
                    .iter()
                    .filter_map(|base| resolve_source_class(base, &bindings))
                    .filter_map(|base| bindings.class_fields.get(base))
                    .flat_map(|fields| fields.iter().map(|(name, kind)| (name.clone(), *kind)))
                    .collect::<BTreeMap<_, _>>();
                fields.extend(collect_declared_fields(class, &bindings));
                bindings.class_fields.insert(class.name.to_string(), fields);
                bindings
                    .active_classes
                    .insert(class.name.to_string(), class.name.to_string());
                if kinds.len() == 1 {
                    let kind = *kinds
                        .first()
                        .expect("one source class kind was established");
                    bindings
                        .declared_classes
                        .insert(class.name.to_string(), kind);
                    bindings.active_types.insert(class.name.to_string(), kind);
                }
            }
            _ => {
                for name in statement_bound_names(statement) {
                    clear_active_binding(&mut bindings, &name);
                }
            }
        }
    }
    bindings
}

fn clear_active_binding(bindings: &mut TypeBindings, name: &str) {
    bindings.active_types.remove(name);
    bindings.active_classes.remove(name);
    bindings.lock_modules.remove(name);
    bindings.thread_modules.remove(name);
}

fn resolve_source_class<'a>(expression: &ast::Expr, bindings: &'a TypeBindings) -> Option<&'a str> {
    match expression {
        ast::Expr::Subscript(subscript) => resolve_source_class(&subscript.value, bindings),
        ast::Expr::Name(name) => bindings
            .active_classes
            .get(name.id.as_str())
            .map(String::as_str),
        _ => None,
    }
}

fn collect_declared_fields(
    class: &ast::StmtClassDef,
    bindings: &TypeBindings,
) -> BTreeMap<String, ConcurrencyKind> {
    let mut fields = BTreeMap::new();
    for statement in &class.body {
        match statement {
            ast::Stmt::AnnAssign(assignment) => {
                if let ast::Expr::Name(field) = assignment.target.as_ref()
                    && let Some(kind) = resolve_type(&assignment.annotation, bindings)
                {
                    fields.insert(field.id.to_string(), kind);
                }
            }
            ast::Stmt::FunctionDef(function) => {
                let receiver = function
                    .args
                    .posonlyargs
                    .first()
                    .or_else(|| function.args.args.first())
                    .map(|argument| argument.def.arg.as_str());
                if let Some(receiver) = receiver {
                    collect_annotated_receiver_fields(
                        &function.body,
                        receiver,
                        bindings,
                        &mut fields,
                    );
                }
            }
            _ => {}
        }
    }
    fields
}

fn collect_annotated_receiver_fields(
    statements: &[ast::Stmt],
    receiver: &str,
    bindings: &TypeBindings,
    fields: &mut BTreeMap<String, ConcurrencyKind>,
) {
    for statement in statements {
        let ast::Stmt::AnnAssign(assignment) = statement else {
            continue;
        };
        let ast::Expr::Attribute(field) = assignment.target.as_ref() else {
            continue;
        };
        if matches!(field.value.as_ref(), ast::Expr::Name(owner)
            if owner.id.as_str() == receiver)
            && let Some(kind) = resolve_type(&assignment.annotation, bindings)
        {
            fields.insert(field.attr.to_string(), kind);
        }
    }
}

fn resolve_type(expression: &ast::Expr, bindings: &TypeBindings) -> Option<ConcurrencyKind> {
    match expression {
        ast::Expr::Subscript(subscript) => resolve_type(&subscript.value, bindings),
        ast::Expr::Name(name) => bindings.active_types.get(name.id.as_str()).copied(),
        ast::Expr::Attribute(attribute) => {
            let ast::Expr::Name(module) = attribute.value.as_ref() else {
                return None;
            };
            match attribute.attr.as_str() {
                "Lock" if bindings.lock_modules.contains(module.id.as_str()) => {
                    Some(ConcurrencyKind::Lock)
                }
                "Thread" if bindings.thread_modules.contains(module.id.as_str()) => {
                    Some(ConcurrencyKind::Thread)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn validate_function(
    function: &ast::StmtFunctionDef,
    enclosing_class: Option<&str>,
    bindings: &TypeBindings,
    candidates: &mut Vec<Candidate>,
) {
    let mut types = FunctionTypes::default();
    for argument in function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .chain(function.args.kwonlyargs.iter())
    {
        let name = argument.def.arg.to_string();
        types.local_names.insert(name.clone());
        if let Some(kind) = argument
            .def
            .annotation
            .as_deref()
            .and_then(|annotation| resolve_type(annotation, bindings))
        {
            types.values.insert(name, kind);
        } else if let Some(class) = argument
            .def
            .annotation
            .as_deref()
            .and_then(|annotation| resolve_source_class(annotation, bindings))
        {
            types.nominal_values.insert(name, class.to_owned());
        }
    }
    if let Some(class) = enclosing_class
        && let Some(receiver) = function.args.args.first()
    {
        let receiver = receiver.def.arg.to_string();
        types
            .nominal_values
            .insert(receiver.clone(), class.to_owned());
        if let Some(kind) = bindings.declared_classes.get(class).copied() {
            types.values.insert(receiver, kind);
        }
    }
    collect_function_locals(&function.body, &mut types.local_names);
    validate_statements(&function.body, bindings, &mut types, candidates);
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
                names.extend(target_bound_names(&assignment.target))
            }
            ast::Stmt::AugAssign(assignment) => {
                names.extend(target_bound_names(&assignment.target))
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
            ast::Stmt::With(with_) => collect_function_locals(&with_.body, names),
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
    bindings: &TypeBindings,
    types: &mut FunctionTypes,
    candidates: &mut Vec<Candidate>,
) {
    for statement in statements {
        validate_statement_expressions(statement, bindings, types, candidates);
        match statement {
            ast::Stmt::Assign(assignment) => {
                if let [ast::Expr::Name(target)] = assignment.targets.as_slice() {
                    update_assigned_type(target.id.as_str(), &assignment.value, bindings, types);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                if let ast::Expr::Name(target) = assignment.target.as_ref() {
                    types.values.remove(target.id.as_str());
                    types.nominal_values.remove(target.id.as_str());
                    if let Some(kind) = resolve_type(&assignment.annotation, bindings) {
                        types.values.insert(target.id.to_string(), kind);
                    } else if let Some(class) =
                        resolve_source_class(&assignment.annotation, bindings)
                    {
                        types
                            .nominal_values
                            .insert(target.id.to_string(), class.to_owned());
                    }
                }
            }
            ast::Stmt::AugAssign(assignment) => {
                if let ast::Expr::Name(target) = assignment.target.as_ref() {
                    types.values.remove(target.id.as_str());
                    types.nominal_values.remove(target.id.as_str());
                }
            }
            ast::Stmt::If(branch) => {
                let mut body = types.clone();
                validate_statements(&branch.body, bindings, &mut body, candidates);
                let mut orelse = types.clone();
                validate_statements(&branch.orelse, bindings, &mut orelse, candidates);
                types.values = must_join(&body.values, &orelse.values);
                types.nominal_values = must_join(&body.nominal_values, &orelse.nominal_values);
            }
            ast::Stmt::While(loop_) => {
                let mut body = types.clone();
                validate_statements(&loop_.body, bindings, &mut body, candidates);
                let mut orelse = types.clone();
                validate_statements(&loop_.orelse, bindings, &mut orelse, candidates);
            }
            ast::Stmt::For(loop_) => {
                let mut body = types.clone();
                validate_statements(&loop_.body, bindings, &mut body, candidates);
                let mut orelse = types.clone();
                validate_statements(&loop_.orelse, bindings, &mut orelse, candidates);
            }
            ast::Stmt::Try(try_) => {
                let mut body = types.clone();
                validate_statements(&try_.body, bindings, &mut body, candidates);
                for handler in &try_.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    let mut branch = types.clone();
                    validate_statements(&handler.body, bindings, &mut branch, candidates);
                }
                let mut orelse = types.clone();
                validate_statements(&try_.orelse, bindings, &mut orelse, candidates);
                let mut finalbody = types.clone();
                validate_statements(&try_.finalbody, bindings, &mut finalbody, candidates);
            }
            ast::Stmt::With(with_) => {
                let mut body = types.clone();
                validate_statements(&with_.body, bindings, &mut body, candidates);
            }
            _ => {}
        }
    }
}

fn update_assigned_type(
    target: &str,
    value: &ast::Expr,
    bindings: &TypeBindings,
    types: &mut FunctionTypes,
) {
    types.values.remove(target);
    types.nominal_values.remove(target);
    let ast::Expr::Call(call) = value else {
        return;
    };
    if let Some(kind) = resolve_constructor(&call.func, bindings, types) {
        types.values.insert(target.to_owned(), kind);
    } else if let Some(class) = resolve_source_constructor(&call.func, bindings, types) {
        types
            .nominal_values
            .insert(target.to_owned(), class.to_owned());
    }
}

fn must_join<K, V>(left: &BTreeMap<K, V>, right: &BTreeMap<K, V>) -> BTreeMap<K, V>
where
    K: Clone + Ord,
    V: Clone + PartialEq,
{
    left.iter()
        .filter_map(|(name, left_value)| {
            right
                .get(name)
                .filter(|right_value| *right_value == left_value)
                .map(|_| (name.clone(), left_value.clone()))
        })
        .collect()
}

fn resolve_constructor(
    expression: &ast::Expr,
    bindings: &TypeBindings,
    types: &FunctionTypes,
) -> Option<ConcurrencyKind> {
    match expression {
        ast::Expr::Name(name) if types.local_names.contains(name.id.as_str()) => None,
        _ => resolve_type(expression, bindings),
    }
}

fn resolve_source_constructor<'a>(
    expression: &ast::Expr,
    bindings: &'a TypeBindings,
    types: &FunctionTypes,
) -> Option<&'a str> {
    match expression {
        ast::Expr::Name(name) if types.local_names.contains(name.id.as_str()) => None,
        _ => resolve_source_class(expression, bindings),
    }
}

fn validate_statement_expressions(
    statement: &ast::Stmt,
    bindings: &TypeBindings,
    types: &FunctionTypes,
    candidates: &mut Vec<Candidate>,
) {
    match statement {
        ast::Stmt::Assign(assignment) => {
            validate_expression(&assignment.value, bindings, types, candidates)
        }
        ast::Stmt::AnnAssign(assignment) => {
            if let Some(value) = &assignment.value {
                validate_expression(value, bindings, types, candidates);
            }
        }
        ast::Stmt::AugAssign(assignment) => {
            validate_expression(&assignment.value, bindings, types, candidates);
        }
        ast::Stmt::Expr(expression) => {
            validate_expression(&expression.value, bindings, types, candidates)
        }
        ast::Stmt::Return(returned) => {
            if let Some(value) = &returned.value {
                validate_expression(value, bindings, types, candidates);
            }
        }
        ast::Stmt::Assert(assertion) => {
            validate_expression(&assertion.test, bindings, types, candidates)
        }
        ast::Stmt::If(branch) => validate_expression(&branch.test, bindings, types, candidates),
        ast::Stmt::While(loop_) => validate_expression(&loop_.test, bindings, types, candidates),
        ast::Stmt::For(loop_) => validate_expression(&loop_.iter, bindings, types, candidates),
        ast::Stmt::With(with_) => {
            for item in &with_.items {
                validate_expression(&item.context_expr, bindings, types, candidates);
            }
        }
        _ => {}
    }
}

fn validate_expression(
    expression: &ast::Expr,
    bindings: &TypeBindings,
    types: &FunctionTypes,
    candidates: &mut Vec<Candidate>,
) {
    match expression {
        ast::Expr::Call(call) => {
            if let ast::Expr::Attribute(method) = call.func.as_ref()
                && let Some(kind) = resolve_value_kind(&method.value, bindings, types)
                && matches!(
                    (kind, method.attr.as_str()),
                    (ConcurrencyKind::Lock, "acquire" | "release")
                        | (ConcurrencyKind::Thread, "start")
                )
            {
                candidates.push(Candidate {
                    code: CONCURRENCY_IN_SIF,
                    message: "concurrency primitives are not available in secure information-flow verification",
                    byte_offset: u32::from(call.range().start()),
                });
            }
            validate_expression(&call.func, bindings, types, candidates);
            for argument in &call.args {
                validate_expression(argument, bindings, types, candidates);
            }
            for keyword in &call.keywords {
                validate_expression(&keyword.value, bindings, types, candidates);
            }
        }
        ast::Expr::BoolOp(operation) => {
            for value in &operation.values {
                validate_expression(value, bindings, types, candidates);
            }
        }
        ast::Expr::BinOp(operation) => {
            validate_expression(&operation.left, bindings, types, candidates);
            validate_expression(&operation.right, bindings, types, candidates);
        }
        ast::Expr::UnaryOp(operation) => {
            validate_expression(&operation.operand, bindings, types, candidates);
        }
        ast::Expr::Compare(comparison) => {
            validate_expression(&comparison.left, bindings, types, candidates);
            for comparator in &comparison.comparators {
                validate_expression(comparator, bindings, types, candidates);
            }
        }
        ast::Expr::IfExp(branch) => {
            validate_expression(&branch.test, bindings, types, candidates);
            validate_expression(&branch.body, bindings, types, candidates);
            validate_expression(&branch.orelse, bindings, types, candidates);
        }
        ast::Expr::Attribute(attribute) => {
            validate_expression(&attribute.value, bindings, types, candidates);
        }
        ast::Expr::Subscript(subscript) => {
            validate_expression(&subscript.value, bindings, types, candidates);
            validate_expression(&subscript.slice, bindings, types, candidates);
        }
        ast::Expr::Tuple(tuple) => {
            for value in &tuple.elts {
                validate_expression(value, bindings, types, candidates);
            }
        }
        ast::Expr::List(list) => {
            for value in &list.elts {
                validate_expression(value, bindings, types, candidates);
            }
        }
        _ => {}
    }
}

fn resolve_value_kind(
    expression: &ast::Expr,
    bindings: &TypeBindings,
    types: &FunctionTypes,
) -> Option<ConcurrencyKind> {
    match expression {
        ast::Expr::Name(name) => types.values.get(name.id.as_str()).copied(),
        ast::Expr::Attribute(field) => {
            let ast::Expr::Name(owner) = field.value.as_ref() else {
                return None;
            };
            let class = types.nominal_values.get(owner.id.as_str())?;
            // Field provenance is populated solely from exact source annotations on this class
            // or its source-resolved bases; a matching attribute spelling alone proves nothing.
            bindings
                .class_fields
                .get(class)?
                .get(field.attr.as_str())
                .copied()
        }
        _ => None,
    }
}
