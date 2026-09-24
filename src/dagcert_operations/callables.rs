//! Closed source-provider analysis for callable-valued Dagcert operation inputs.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_parser::ast::Ranged;
use rustpython_parser::{Parse, ast};

use super::OperationFailure;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CallablePrimitiveType {
    Int,
    Float,
    Bool,
    Str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallableContract {
    pub parameters: Vec<CallablePrimitiveType>,
    pub return_type: CallablePrimitiveType,
    pub raised_exceptions: BTreeSet<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedCallableBinding {
    pub operation: String,
    pub input_record: String,
    pub field: String,
    pub provider_description: String,
    pub source_provider: Option<SourceCallableProvider>,
    pub contract: CallableContract,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceCallableProvider {
    pub path: String,
    pub symbol: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ProviderValueType {
    Int,
    Float,
    Bool,
    Str,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct ProviderStatementEffects {
    all_paths_terminate: bool,
    raised_exceptions: BTreeSet<String>,
}

/// Extract the complete primitive signature and exit set of one source-owned callback.
///
/// This accepts only the executable subset whose returns and raises are checked below. A Python
/// annotation is never treated as evidence that an unexamined body is total.
pub fn analyze_source_callable(
    source: &str,
    path: &str,
    symbol: &str,
) -> Result<CallableContract, OperationFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| OperationFailure {
        code: "frontend.python.dagcert.callable-provider-parse-error",
        message: error.to_string(),
        byte_offset: None,
    })?;
    if suite
        .iter()
        .any(|statement| declaration_name(statement).is_some_and(modeled_builtin_exception))
    {
        return failure(
            "frontend.python.dagcert.callable-provider-exception-shadowed",
            "source callback module shadows a modeled builtin exception class",
        );
    }
    if suite.iter().any(
        |statement| matches!(statement, ast::Stmt::AsyncFunctionDef(function) if function.name.as_str() == symbol),
    ) {
        return failure(
            "frontend.python.dagcert.callable-provider-async",
            format!("source callback {symbol:?} is async and cannot satisfy a synchronous field"),
        );
    }
    let matches = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) if function.name.as_str() == symbol => Some(function),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [function] = matches.as_slice() else {
        return failure(
            if matches.is_empty() {
                "frontend.python.dagcert.callable-provider-symbol-missing"
            } else {
                "frontend.python.dagcert.callable-provider-symbol-duplicate"
            },
            format!(
                "source callback provider {symbol:?} must resolve to exactly one top-level function"
            ),
        );
    };
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || function.args.vararg.is_some()
        || function.args.kwarg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function
            .args
            .posonlyargs
            .iter()
            .chain(&function.args.args)
            .any(|parameter| parameter.default.is_some())
    {
        return failure(
            "frontend.python.dagcert.callable-provider-signature-unsupported",
            format!(
                "source callback {symbol:?} must be nongeneric, undecorated, synchronous, and nonvariadic without defaults"
            ),
        );
    }
    let mut environment = BTreeMap::new();
    let mut parameters = Vec::new();
    for parameter in function.args.posonlyargs.iter().chain(&function.args.args) {
        let annotation = parameter
            .def
            .annotation
            .as_deref()
            .ok_or_else(|| OperationFailure {
                code: "frontend.python.dagcert.callable-provider-type-missing",
                message: format!(
                    "source callback {symbol:?} parameter {:?} has no annotation",
                    parameter.def.arg
                ),
                byte_offset: Some(parameter.def.range.start().into()),
            })?;
        let parameter_type = primitive_annotation(annotation)?;
        environment.insert(
            parameter.def.arg.to_string(),
            provider_type(&parameter_type),
        );
        parameters.push(parameter_type);
    }
    let return_annotation = function
        .returns
        .as_deref()
        .ok_or_else(|| OperationFailure {
            code: "frontend.python.dagcert.callable-provider-type-missing",
            message: format!("source callback {symbol:?} has no return annotation"),
            byte_offset: Some(function.range.start().into()),
        })?;
    let return_type = primitive_annotation(return_annotation)?;
    let effects = analyze_statements(&function.body, &environment, &provider_type(&return_type))?;
    if !effects.all_paths_terminate {
        return failure(
            "frontend.python.dagcert.callable-provider-not-total",
            format!("source callback {symbol:?} has a reachable missing-return path"),
        );
    }
    Ok(CallableContract {
        parameters,
        return_type,
        raised_exceptions: effects.raised_exceptions,
    })
}

fn primitive_annotation(annotation: &ast::Expr) -> Result<CallablePrimitiveType, OperationFailure> {
    let ast::Expr::Name(name) = annotation else {
        return located_failure(
            "frontend.python.dagcert.callable-provider-type-unsupported",
            "source callback annotations must be direct primitive names",
            annotation,
        );
    };
    match name.id.as_str() {
        "int" => Ok(CallablePrimitiveType::Int),
        "float" => Ok(CallablePrimitiveType::Float),
        "bool" => Ok(CallablePrimitiveType::Bool),
        "str" => Ok(CallablePrimitiveType::Str),
        _ => located_failure(
            "frontend.python.dagcert.callable-provider-type-unsupported",
            format!(
                "source callback annotation {:?} is outside the primitive callback fragment",
                name.id
            ),
            annotation,
        ),
    }
}

fn provider_type(value_type: &CallablePrimitiveType) -> ProviderValueType {
    match value_type {
        CallablePrimitiveType::Int => ProviderValueType::Int,
        CallablePrimitiveType::Float => ProviderValueType::Float,
        CallablePrimitiveType::Bool => ProviderValueType::Bool,
        CallablePrimitiveType::Str => ProviderValueType::Str,
    }
}

fn analyze_statements(
    statements: &[ast::Stmt],
    environment: &BTreeMap<String, ProviderValueType>,
    expected_return: &ProviderValueType,
) -> Result<ProviderStatementEffects, OperationFailure> {
    let mut terminated = false;
    let mut exceptions = BTreeSet::new();
    for (index, statement) in statements.iter().enumerate() {
        if index == 0 && is_docstring(statement) {
            continue;
        }
        if terminated {
            return failure(
                "frontend.python.dagcert.callable-provider-unreachable",
                "source callback contains a statement after every path has terminated",
            );
        }
        match statement {
            ast::Stmt::Return(returned) => {
                let Some(expression) = returned.value.as_deref() else {
                    return failure(
                        "frontend.python.dagcert.callable-provider-return-missing",
                        "source callback must return its annotated primitive type",
                    );
                };
                let actual = infer_expression(expression, environment)?;
                if &actual != expected_return {
                    return located_failure(
                        "frontend.python.dagcert.callable-provider-return-type-mismatch",
                        format!("source callback returns {actual:?}, expected {expected_return:?}"),
                        expression,
                    );
                }
                terminated = true;
            }
            ast::Stmt::Raise(raised) => {
                if raised.cause.is_some() {
                    return failure(
                        "frontend.python.dagcert.callable-provider-raise-unsupported",
                        "source callback exception chaining is outside this effect fragment",
                    );
                }
                let Some(exception) = raised.exc.as_deref() else {
                    return failure(
                        "frontend.python.dagcert.callable-provider-reraise-unsupported",
                        "source callback cannot re-raise outside a modeled handler",
                    );
                };
                exceptions.insert(direct_exception_constructor(exception)?);
                terminated = true;
            }
            ast::Stmt::If(branch) => {
                if infer_expression(&branch.test, environment)? != ProviderValueType::Bool {
                    return located_failure(
                        "frontend.python.dagcert.callable-provider-condition-type-mismatch",
                        "source callback branch condition must be bool",
                        &branch.test,
                    );
                }
                let then_effects = analyze_statements(&branch.body, environment, expected_return)?;
                let else_effects = if branch.orelse.is_empty() {
                    ProviderStatementEffects::default()
                } else {
                    analyze_statements(&branch.orelse, environment, expected_return)?
                };
                exceptions.extend(then_effects.raised_exceptions);
                exceptions.extend(else_effects.raised_exceptions);
                terminated = then_effects.all_paths_terminate && else_effects.all_paths_terminate;
            }
            _ => {
                return failure(
                    "frontend.python.dagcert.callable-provider-statement-unsupported",
                    format!(
                        "source callback contains an unmodeled effectful statement {statement:?}"
                    ),
                );
            }
        }
    }
    Ok(ProviderStatementEffects {
        all_paths_terminate: terminated,
        raised_exceptions: exceptions,
    })
}

fn infer_expression(
    expression: &ast::Expr,
    environment: &BTreeMap<String, ProviderValueType>,
) -> Result<ProviderValueType, OperationFailure> {
    match expression {
        ast::Expr::Name(name) => {
            environment
                .get(name.id.as_str())
                .cloned()
                .ok_or_else(|| OperationFailure {
                    code: "frontend.python.dagcert.callable-provider-name-unbound",
                    message: format!(
                        "source callback expression reads unbound name {:?}",
                        name.id
                    ),
                    byte_offset: Some(name.range.start().into()),
                })
        }
        ast::Expr::Constant(constant) => match constant.value {
            ast::Constant::Int(_) => Ok(ProviderValueType::Int),
            ast::Constant::Float(_) => Ok(ProviderValueType::Float),
            ast::Constant::Bool(_) => Ok(ProviderValueType::Bool),
            ast::Constant::Str(_) => Ok(ProviderValueType::Str),
            _ => unsupported_expression(expression),
        },
        ast::Expr::UnaryOp(operation) => {
            let operand = infer_expression(&operation.operand, environment)?;
            match operation.op {
                ast::UnaryOp::Not if operand == ProviderValueType::Bool => {
                    Ok(ProviderValueType::Bool)
                }
                ast::UnaryOp::UAdd | ast::UnaryOp::USub
                    if matches!(operand, ProviderValueType::Int | ProviderValueType::Float) =>
                {
                    Ok(operand)
                }
                _ => unsupported_expression(expression),
            }
        }
        ast::Expr::BinOp(operation) => {
            let left = infer_expression(&operation.left, environment)?;
            let right = infer_expression(&operation.right, environment)?;
            match operation.op {
                ast::Operator::Add
                    if left == right
                        && matches!(
                            left,
                            ProviderValueType::Int
                                | ProviderValueType::Float
                                | ProviderValueType::Str
                        ) =>
                {
                    Ok(left)
                }
                ast::Operator::Sub | ast::Operator::Mult
                    if left == right
                        && matches!(left, ProviderValueType::Int | ProviderValueType::Float) =>
                {
                    Ok(left)
                }
                _ => located_failure(
                    "frontend.python.dagcert.callable-provider-partial-operator",
                    "source callback contains a partial or unsupported operator",
                    expression,
                ),
            }
        }
        ast::Expr::Compare(comparison)
            if comparison.ops.len() == 1 && comparison.comparators.len() == 1 =>
        {
            let left = infer_expression(&comparison.left, environment)?;
            let right = infer_expression(&comparison.comparators[0], environment)?;
            if left != right {
                return located_failure(
                    "frontend.python.dagcert.callable-provider-comparison-type-mismatch",
                    "source callback comparison operands have different types",
                    expression,
                );
            }
            match comparison.ops[0] {
                ast::CmpOp::Eq | ast::CmpOp::NotEq => Ok(ProviderValueType::Bool),
                ast::CmpOp::Lt | ast::CmpOp::LtE | ast::CmpOp::Gt | ast::CmpOp::GtE
                    if matches!(
                        left,
                        ProviderValueType::Int | ProviderValueType::Float | ProviderValueType::Str
                    ) =>
                {
                    Ok(ProviderValueType::Bool)
                }
                _ => unsupported_expression(expression),
            }
        }
        _ => unsupported_expression(expression),
    }
}

fn direct_exception_constructor(expression: &ast::Expr) -> Result<String, OperationFailure> {
    let (name, arguments) = match expression {
        ast::Expr::Name(name) => (name.id.as_str(), None),
        ast::Expr::Call(call) if call.keywords.is_empty() => {
            let ast::Expr::Name(name) = call.func.as_ref() else {
                return unsupported_exception_constructor(expression);
            };
            (name.id.as_str(), Some(call.args.as_slice()))
        }
        _ => return unsupported_exception_constructor(expression),
    };
    if !modeled_builtin_exception(name) {
        return unsupported_exception_constructor(expression);
    }
    if let Some(arguments) = arguments
        && !arguments.iter().all(
            |argument| matches!(argument, ast::Expr::Constant(constant) if matches!(constant.value, ast::Constant::Str(_))),
        )
    {
        return unsupported_exception_constructor(expression);
    }
    Ok(name.to_owned())
}

fn is_docstring(statement: &ast::Stmt) -> bool {
    matches!(
        statement,
        ast::Stmt::Expr(expression)
            if matches!(expression.value.as_ref(), ast::Expr::Constant(value)
                if matches!(value.value, ast::Constant::Str(_)))
    )
}

fn declaration_name(statement: &ast::Stmt) -> Option<&str> {
    match statement {
        ast::Stmt::ClassDef(class) => Some(class.name.as_str()),
        ast::Stmt::FunctionDef(function) => Some(function.name.as_str()),
        ast::Stmt::AsyncFunctionDef(function) => Some(function.name.as_str()),
        _ => None,
    }
}

fn modeled_builtin_exception(name: &str) -> bool {
    matches!(
        name,
        "BaseException"
            | "Exception"
            | "ValueError"
            | "TypeError"
            | "LookupError"
            | "IndexError"
            | "KeyError"
            | "ArithmeticError"
            | "ZeroDivisionError"
            | "RuntimeError"
            | "SystemExit"
            | "KeyboardInterrupt"
            | "GeneratorExit"
    )
}

fn unsupported_expression<T>(expression: &ast::Expr) -> Result<T, OperationFailure> {
    located_failure(
        "frontend.python.dagcert.callable-provider-expression-unsupported",
        "source callback expression is not proved total in the provider fragment",
        expression,
    )
}

fn unsupported_exception_constructor<T>(expression: &ast::Expr) -> Result<T, OperationFailure> {
    located_failure(
        "frontend.python.dagcert.callable-provider-exception-unsupported",
        "source callback raises an exception whose class or constructor effects are not modeled",
        expression,
    )
}

fn located_failure<T>(
    code: &'static str,
    message: impl Into<String>,
    expression: &ast::Expr,
) -> Result<T, OperationFailure> {
    Err(OperationFailure {
        code,
        message: message.into(),
        byte_offset: Some(expression.range().start().into()),
    })
}

fn failure<T>(code: &'static str, message: impl Into<String>) -> Result<T, OperationFailure> {
    Err(OperationFailure {
        code,
        message: message.into(),
        byte_offset: None,
    })
}
