//! Resolves final import bindings and builds the source method catalog used by thread checks.

use rustpython_parser::ast;

use super::{Bindings, Catalog, FunctionInfo, ThreadSymbol};

pub(super) fn collect_final_bindings(suite: &ast::Suite) -> Bindings {
    let mut bindings = Bindings::default();
    for statement in suite {
        match statement {
            ast::Stmt::Import(import) => {
                for alias in &import.names {
                    let local = alias.asname.as_ref().map_or_else(
                        || alias.name.as_str().split('.').next().unwrap_or_default(),
                        |name| name.as_str(),
                    );
                    clear_binding(&mut bindings, local);
                    match alias.name.as_str() {
                        "nagini_contracts.thread" if alias.asname.is_some() => {
                            bindings.thread_modules.insert(local.to_owned());
                        }
                        "nagini_contracts.contracts" if alias.asname.is_some() => {
                            bindings.contract_modules.insert(local.to_owned());
                        }
                        "nagini_contracts.obligations" if alias.asname.is_some() => {
                            bindings.obligation_modules.insert(local.to_owned());
                        }
                        _ => {}
                    }
                }
            }
            ast::Stmt::ImportFrom(import) => {
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        match import.module.as_ref().map(|name| name.as_str()) {
                            Some("nagini_contracts.contracts") => bindings.contracts_star = true,
                            Some("nagini_contracts.obligations") => {
                                bindings.obligations_star = true
                            }
                            _ => {}
                        }
                        continue;
                    }
                    let local = alias
                        .asname
                        .as_ref()
                        .map_or(alias.name.as_str(), |name| name.as_str());
                    clear_binding(&mut bindings, local);
                    match import.module.as_ref().map(|name| name.as_str()) {
                        Some("nagini_contracts.thread") => {
                            let symbol = match alias.name.as_str() {
                                "Thread" => Some(ThreadSymbol::Thread),
                                "getMethod" => Some(ThreadSymbol::GetMethod),
                                "getOld" => Some(ThreadSymbol::GetOld),
                                "arg" => Some(ThreadSymbol::Arg),
                                _ => None,
                            };
                            if let Some(symbol) = symbol {
                                bindings.thread_names.insert(local.to_owned(), symbol);
                            }
                        }
                        Some("nagini_contracts.contracts") => match alias.name.as_str() {
                            "Pure" => {
                                bindings.pure_names.insert(local.to_owned());
                            }
                            "Predicate" => {
                                bindings.predicate_names.insert(local.to_owned());
                            }
                            "Ensures" => {
                                bindings.ensures_names.insert(local.to_owned());
                            }
                            _ => {}
                        },
                        Some("nagini_contracts.obligations") => {
                            bindings.obligation_names.insert(local.to_owned());
                        }
                        _ => {}
                    }
                }
            }
            _ => {
                for name in statement_bound_names(statement) {
                    clear_binding(&mut bindings, &name);
                }
            }
        }
    }
    bindings
}

fn clear_binding(bindings: &mut Bindings, name: &str) {
    bindings.thread_names.remove(name);
    bindings.thread_modules.remove(name);
    bindings.pure_names.remove(name);
    bindings.predicate_names.remove(name);
    bindings.ensures_names.remove(name);
    bindings.contract_modules.remove(name);
    bindings.obligation_names.remove(name);
    bindings.obligation_modules.remove(name);
}

pub(super) fn statement_bound_names(statement: &ast::Stmt) -> Vec<String> {
    match statement {
        ast::Stmt::FunctionDef(function) => vec![function.name.to_string()],
        ast::Stmt::AsyncFunctionDef(function) => vec![function.name.to_string()],
        ast::Stmt::ClassDef(class) => vec![class.name.to_string()],
        ast::Stmt::Assign(assignment) => assignment
            .targets
            .iter()
            .flat_map(target_bound_names)
            .collect(),
        ast::Stmt::AnnAssign(assignment) => target_bound_names(&assignment.target),
        ast::Stmt::AugAssign(assignment) => target_bound_names(&assignment.target),
        _ => Vec::new(),
    }
}

pub(super) fn target_bound_names(expression: &ast::Expr) -> Vec<String> {
    match expression {
        ast::Expr::Name(name) => vec![name.id.to_string()],
        ast::Expr::Tuple(tuple) => tuple.elts.iter().flat_map(target_bound_names).collect(),
        ast::Expr::List(list) => list.elts.iter().flat_map(target_bound_names).collect(),
        ast::Expr::Starred(starred) => target_bound_names(&starred.value),
        _ => Vec::new(),
    }
}

pub(super) fn collect_catalog(suite: &ast::Suite, bindings: &Bindings) -> Catalog {
    let mut catalog = Catalog::default();
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                catalog.functions.insert(
                    function.name.to_string(),
                    function_info(function, bindings, false),
                );
            }
            ast::Stmt::ClassDef(class) => {
                catalog.classes.insert(class.name.to_string());
                let methods = class
                    .body
                    .iter()
                    .filter_map(|statement| {
                        let ast::Stmt::FunctionDef(function) = statement else {
                            return None;
                        };
                        Some((
                            function.name.to_string(),
                            function_info(function, bindings, true),
                        ))
                    })
                    .collect();
                catalog.methods.insert(class.name.to_string(), methods);
            }
            _ => {}
        }
    }
    catalog
}

fn function_info(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    method: bool,
) -> FunctionInfo {
    let positional = function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .collect::<Vec<_>>();
    let skipped_receiver = usize::from(method && !positional.is_empty());
    let positional_count = positional.len().saturating_sub(skipped_receiver);
    let required_count = positional
        .iter()
        .skip(skipped_receiver)
        .filter(|argument| argument.default.is_none())
        .count();
    FunctionInfo {
        pure: function
            .decorator_list
            .iter()
            .any(|decorator| is_contract_name(decorator, bindings, "Pure")),
        predicate: function
            .decorator_list
            .iter()
            .any(|decorator| is_contract_name(decorator, bindings, "Predicate")),
        positional_count,
        required_count,
        has_obligation_postcondition: function.body.iter().any(|statement| {
            let ast::Stmt::Expr(expression) = statement else {
                return false;
            };
            let ast::Expr::Call(call) = expression.value.as_ref() else {
                return false;
            };
            is_contract_callee(&call.func, bindings, "Ensures")
                && call
                    .args
                    .iter()
                    .any(|argument| expression_contains_obligation_call(argument, bindings))
        }),
    }
}

fn is_contract_name(expression: &ast::Expr, bindings: &Bindings, expected: &str) -> bool {
    match expression {
        ast::Expr::Name(name) => match expected {
            "Pure" => {
                (bindings.contracts_star && name.id.as_str() == "Pure")
                    || bindings.pure_names.contains(name.id.as_str())
            }
            "Predicate" => {
                (bindings.contracts_star && name.id.as_str() == "Predicate")
                    || bindings.predicate_names.contains(name.id.as_str())
            }
            _ => false,
        },
        ast::Expr::Attribute(attribute) => {
            attribute.attr.as_str() == expected
                && matches!(attribute.value.as_ref(), ast::Expr::Name(module)
                    if bindings.contract_modules.contains(module.id.as_str()))
        }
        _ => false,
    }
}

fn is_contract_callee(expression: &ast::Expr, bindings: &Bindings, expected: &str) -> bool {
    match expression {
        ast::Expr::Name(name) if expected == "Ensures" => {
            (bindings.contracts_star && name.id.as_str() == "Ensures")
                || bindings.ensures_names.contains(name.id.as_str())
        }
        ast::Expr::Attribute(attribute) => {
            attribute.attr.as_str() == expected
                && matches!(attribute.value.as_ref(), ast::Expr::Name(module)
                    if bindings.contract_modules.contains(module.id.as_str()))
        }
        _ => false,
    }
}

fn expression_contains_obligation_call(expression: &ast::Expr, bindings: &Bindings) -> bool {
    match expression {
        ast::Expr::Call(call) => {
            let obligation = match call.func.as_ref() {
                ast::Expr::Name(name) => {
                    (bindings.obligations_star && is_builtin_obligation_name(name.id.as_str()))
                        || bindings.obligation_names.contains(name.id.as_str())
                }
                ast::Expr::Attribute(attribute) => {
                    matches!(attribute.value.as_ref(), ast::Expr::Name(module)
                        if bindings.obligation_modules.contains(module.id.as_str()))
                }
                _ => false,
            };
            obligation
                || expression_contains_obligation_call(&call.func, bindings)
                || call
                    .args
                    .iter()
                    .any(|argument| expression_contains_obligation_call(argument, bindings))
                || call
                    .keywords
                    .iter()
                    .any(|keyword| expression_contains_obligation_call(&keyword.value, bindings))
        }
        ast::Expr::BoolOp(operation) => operation
            .values
            .iter()
            .any(|value| expression_contains_obligation_call(value, bindings)),
        ast::Expr::BinOp(operation) => {
            expression_contains_obligation_call(&operation.left, bindings)
                || expression_contains_obligation_call(&operation.right, bindings)
        }
        ast::Expr::UnaryOp(operation) => {
            expression_contains_obligation_call(&operation.operand, bindings)
        }
        ast::Expr::Compare(comparison) => {
            expression_contains_obligation_call(&comparison.left, bindings)
                || comparison
                    .comparators
                    .iter()
                    .any(|value| expression_contains_obligation_call(value, bindings))
        }
        ast::Expr::Attribute(attribute) => {
            expression_contains_obligation_call(&attribute.value, bindings)
        }
        _ => false,
    }
}

fn is_builtin_obligation_name(name: &str) -> bool {
    matches!(
        name,
        "Level" | "MustInvoke" | "MustRelease" | "MustTerminate" | "WaitLevel" | "WaitLevelBelow"
    )
}
