//! Python source frontend.
//!
//! This module parses real source, extracts source-owned types and proves only explicitly bounded
//! fragments. Anything outside those fragments is retained as an effect or refused; it is never
//! silently treated as exception-free.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_parser::{Parse, ast};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum TypeRef {
    Named {
        name: String,
    },
    Generic {
        name: String,
        arguments: Vec<TypeRef>,
    },
    Callable {
        parameters: Vec<TypeRef>,
        result: Box<TypeRef>,
    },
    Union {
        alternatives: Vec<TypeRef>,
    },
    Unknown {
        source: String,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Parameter {
    pub name: String,
    pub type_ref: TypeRef,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct FunctionDecl {
    pub qualified_name: String,
    pub parameters: Vec<Parameter>,
    pub return_type: TypeRef,
    pub byte_offset: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct FieldDecl {
    pub name: String,
    pub type_ref: TypeRef,
    pub byte_offset: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ClassDecl {
    pub name: String,
    pub dataclass: bool,
    pub fields: Vec<FieldDecl>,
    pub methods: Vec<FunctionDecl>,
    pub byte_offset: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum FeatureUse {
    Slice {
        owner: String,
        target: String,
        target_type: TypeRef,
        has_lower: bool,
        has_upper: bool,
        has_step: bool,
        byte_offset: u32,
    },
    CallableFieldCall {
        owner: String,
        field: String,
        callable_type: TypeRef,
        argument_types: Vec<TypeRef>,
        type_compatible: bool,
        byte_offset: u32,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct PythonDiagnostic {
    pub code: String,
    pub message: String,
    pub owner: String,
    pub byte_offset: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EffectCertainty {
    Certain,
    Potential,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ExceptionalEffect {
    pub owner: String,
    pub exception_type: Option<String>,
    pub origin: String,
    pub certainty: EffectCertainty,
    pub escapes: bool,
    pub byte_offset: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct PythonModule {
    pub path: String,
    pub functions: Vec<FunctionDecl>,
    pub classes: Vec<ClassDecl>,
    pub features: Vec<FeatureUse>,
    pub exceptional_effects: Vec<ExceptionalEffect>,
    pub type_diagnostics: Vec<PythonDiagnostic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FragmentFailure {
    pub code: &'static str,
    pub message: String,
}

/// Prove the first executable Python fragment directly from source.
///
/// The fragment is intentionally semantic, not file-name based: a module may contain only fully
/// annotated, undecorated synchronous functions whose body is exactly one return of a parameter,
/// primitive literal, or safe builtin slice. Those operations have no exceptional exit after
/// Python has entered the function. Anything else is refused.
pub fn prove_closed_fragment(
    source: &str,
    path: &str,
    requested_symbols: &[String],
) -> Result<Vec<FunctionDecl>, FragmentFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| FragmentFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    let mut functions = Vec::new();
    for statement in &suite {
        let ast::Stmt::FunctionDef(function) = statement else {
            return Err(FragmentFailure {
                code: "frontend.python.fragment.unsupported-module-statement",
                message: format!(
                    "closed-total-functions/v0 accepts only top-level function definitions; found {statement:?}"
                ),
            });
        };
        let declaration = function_decl(function, None);
        check_closed_function(function, &declaration)?;
        functions.push(declaration);
    }
    if functions.is_empty() {
        return Err(FragmentFailure {
            code: "frontend.python.fragment.empty-module",
            message: "a module with no functions is not a proof".to_owned(),
        });
    }
    for symbol in requested_symbols {
        if !functions
            .iter()
            .any(|function| function.qualified_name == *symbol)
        {
            return Err(FragmentFailure {
                code: "frontend.python.symbol.missing",
                message: format!("requested symbol {symbol:?} is not a top-level function"),
            });
        }
    }
    Ok(functions)
}

/// Prove a narrow but production-relevant totality pattern for dependency-injected callables.
///
/// A method in this fragment calls a callable-valued dataclass field inside `try`, returns the
/// callable's declared result on success, and converts every exceptional exit (`except:` or
/// `except BaseException:`) to a same-typed literal/parameter return. This is intentionally strict:
/// accepting broader control flow without proving it would recreate the unchecked-wrapper hole
/// Maledictus exists to close.
pub fn prove_caught_callable_fragment(
    source: &str,
    path: &str,
    requested_symbols: &[String],
) -> Result<Vec<FunctionDecl>, FragmentFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| FragmentFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    let mut methods = Vec::new();
    for statement in &suite {
        match statement {
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import.module.as_ref().is_some_and(|module| {
                        matches!(module.as_str(), "dataclasses" | "typing")
                    }) => {}
            ast::Stmt::ClassDef(class) => check_caught_callable_class(class, &mut methods)?,
            _ => {
                return Err(FragmentFailure {
                    code: "frontend.python.callable-boundary.module-statement-unsupported",
                    message: format!(
                        "caught-callable fragment accepts only dataclasses, typing imports, and class definitions; found {statement:?}"
                    ),
                });
            }
        }
    }
    if methods.is_empty() {
        return Err(FragmentFailure {
            code: "frontend.python.callable-boundary.empty-module",
            message: "module contains no caught callable boundary methods".to_owned(),
        });
    }
    for symbol in requested_symbols {
        if !methods
            .iter()
            .any(|method| method.qualified_name == *symbol)
        {
            return Err(FragmentFailure {
                code: "frontend.python.symbol.missing",
                message: format!("requested symbol {symbol:?} is not a verified callable boundary"),
            });
        }
    }
    Ok(methods)
}

fn check_caught_callable_class(
    class: &ast::StmtClassDef,
    methods: &mut Vec<FunctionDecl>,
) -> Result<(), FragmentFailure> {
    if class.decorator_list.len() != 1
        || !class.decorator_list.iter().all(|decorator| {
            matches!(
                dotted_name(decorator).as_deref(),
                Some("dataclass" | "dataclasses.dataclass")
            )
        })
        || !class.type_params.is_empty()
        || !class.bases.is_empty()
        || !class.keywords.is_empty()
    {
        return fragment_failure(
            "frontend.python.callable-boundary.class-shape-unsupported",
            class.name.as_str(),
            "class must be a non-generic @dataclass without explicit bases",
        );
    }

    let mut fields = BTreeMap::new();
    for statement in &class.body {
        match statement {
            ast::Stmt::AnnAssign(assignment) => {
                let ast::Expr::Name(name) = assignment.target.as_ref() else {
                    return fragment_failure(
                        "frontend.python.callable-boundary.field-unsupported",
                        class.name.as_str(),
                        "callable fields must be simple annotated names",
                    );
                };
                if assignment.value.is_some() {
                    return fragment_failure(
                        "frontend.python.callable-boundary.field-unsupported",
                        class.name.as_str(),
                        "callable fields cannot have default expressions in this fragment",
                    );
                }
                let field_type = parse_type(&assignment.annotation);
                if !matches!(field_type, TypeRef::Callable { .. }) {
                    return fragment_failure(
                        "frontend.python.callable-boundary.field-unsupported",
                        class.name.as_str(),
                        "every dataclass field must be an explicitly typed Callable",
                    );
                }
                fields.insert(name.id.to_string(), field_type);
            }
            ast::Stmt::FunctionDef(_) => {}
            _ => {
                return fragment_failure(
                    "frontend.python.callable-boundary.class-statement-unsupported",
                    class.name.as_str(),
                    "class body may contain only callable field declarations and verified methods",
                );
            }
        }
    }
    if fields.is_empty() {
        return fragment_failure(
            "frontend.python.callable-boundary.field-unsupported",
            class.name.as_str(),
            "every dataclass field must be an explicitly typed Callable without a default",
        );
    }

    for statement in &class.body {
        match statement {
            ast::Stmt::AnnAssign(_) => {}
            ast::Stmt::FunctionDef(function) => {
                let declaration = function_decl(function, Some(class.name.as_str()));
                check_caught_callable_method(function, &declaration, &fields)?;
                methods.push(declaration);
            }
            _ => {
                return fragment_failure(
                    "frontend.python.callable-boundary.class-statement-unsupported",
                    class.name.as_str(),
                    "class body may contain only callable field declarations and verified methods",
                );
            }
        }
    }
    Ok(())
}

fn check_caught_callable_method(
    function: &ast::StmtFunctionDef,
    declaration: &FunctionDecl,
    fields: &BTreeMap<String, TypeRef>,
) -> Result<(), FragmentFailure> {
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || function.args.vararg.is_some()
        || function.args.kwarg.is_some()
        || !function.args.posonlyargs.is_empty()
        || !function.args.kwonlyargs.is_empty()
        || function.args.args.is_empty()
        || function.args.args[0].def.arg.as_str() != "self"
        || function
            .args
            .args
            .iter()
            .any(|argument| argument.default.is_some())
    {
        return fragment_failure(
            "frontend.python.callable-boundary.signature-unsupported",
            &declaration.qualified_name,
            "method must have an undecorated (self, typed...) signature without defaults",
        );
    }
    if matches!(declaration.return_type, TypeRef::Unknown { .. })
        || declaration
            .parameters
            .iter()
            .skip(1)
            .any(|parameter| matches!(parameter.type_ref, TypeRef::Unknown { .. }))
    {
        return fragment_failure(
            "frontend.python.callable-boundary.type-unsupported",
            &declaration.qualified_name,
            "all non-self parameters and the return value require explicit supported types",
        );
    }

    let [ast::Stmt::Try(try_statement)] = function.body.as_slice() else {
        return fragment_failure(
            "frontend.python.callable-boundary.body-unsupported",
            &declaration.qualified_name,
            "body must be exactly one try/except that closes the callable exception channel",
        );
    };
    if !try_statement.orelse.is_empty()
        || !try_statement.finalbody.is_empty()
        || try_statement.handlers.len() != 1
    {
        return fragment_failure(
            "frontend.python.callable-boundary.try-shape-unsupported",
            &declaration.qualified_name,
            "try must have one exhaustive handler and no else/finally",
        );
    }
    let ast::ExceptHandler::ExceptHandler(handler) = &try_statement.handlers[0];
    let catches_all = handler.type_.is_none()
        || matches!(handler.type_.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == "BaseException");
    if !catches_all || handler.name.is_some() {
        return fragment_failure(
            "frontend.python.callable-boundary.handler-not-exhaustive",
            &declaration.qualified_name,
            "unknown callable effects require `except:` or `except BaseException:`",
        );
    }

    let [ast::Stmt::Return(success)] = try_statement.body.as_slice() else {
        return fragment_failure(
            "frontend.python.callable-boundary.success-unsupported",
            &declaration.qualified_name,
            "try body must directly return one callable field invocation",
        );
    };
    let Some(ast::Expr::Call(call)) = success.value.as_deref() else {
        return fragment_failure(
            "frontend.python.callable-boundary.success-unsupported",
            &declaration.qualified_name,
            "try body must directly return one callable field invocation",
        );
    };
    let ast::Expr::Attribute(attribute) = call.func.as_ref() else {
        return fragment_failure(
            "frontend.python.callable-boundary.call-target-unsupported",
            &declaration.qualified_name,
            "call target must be self.<callable-field>",
        );
    };
    if !matches!(attribute.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "self")
        || !call.keywords.is_empty()
    {
        return fragment_failure(
            "frontend.python.callable-boundary.call-target-unsupported",
            &declaration.qualified_name,
            "call target must be self.<callable-field> with positional arguments",
        );
    }
    let Some(TypeRef::Callable { parameters, result }) = fields.get(attribute.attr.as_str()) else {
        return fragment_failure(
            "frontend.python.callable-boundary.field-unresolved",
            &declaration.qualified_name,
            "called attribute is not a declared Callable field",
        );
    };
    let locals = parameter_types(declaration);
    let argument_types: Vec<_> = call
        .args
        .iter()
        .map(|argument| infer_boundary_value_type(argument, &locals))
        .collect();
    if parameters != &argument_types {
        return fragment_failure(
            "frontend.python.callable-boundary.argument-type-mismatch",
            &declaration.qualified_name,
            &format!("expected {parameters:?}, found {argument_types:?}"),
        );
    }
    if result.as_ref() != &declaration.return_type {
        return fragment_failure(
            "frontend.python.callable-boundary.return-type-mismatch",
            &declaration.qualified_name,
            "callable result does not match method return annotation",
        );
    }

    let [ast::Stmt::Return(failure)] = handler.body.as_slice() else {
        return fragment_failure(
            "frontend.python.callable-boundary.failure-unsupported",
            &declaration.qualified_name,
            "handler must directly return a typed literal or parameter",
        );
    };
    let failure_type = match failure.value.as_deref() {
        Some(expression) => infer_boundary_value_type(expression, &locals),
        None => TypeRef::Named {
            name: "None".to_owned(),
        },
    };
    if failure_type != declaration.return_type {
        return fragment_failure(
            "frontend.python.callable-boundary.failure-type-mismatch",
            &declaration.qualified_name,
            &format!(
                "handler returns {failure_type:?}, not {:?}",
                declaration.return_type
            ),
        );
    }
    Ok(())
}

fn infer_boundary_value_type(
    expression: &ast::Expr,
    locals: &BTreeMap<String, TypeRef>,
) -> TypeRef {
    match expression {
        ast::Expr::Name(name) if name.id.as_str() != "self" => locals
            .get(name.id.as_str())
            .cloned()
            .unwrap_or_else(|| TypeRef::Unknown {
                source: format!("unresolved boundary name {}", name.id),
            }),
        ast::Expr::Constant(constant) => match constant.value {
            ast::Constant::None => TypeRef::Named {
                name: "None".to_owned(),
            },
            ast::Constant::Bool(_) => TypeRef::Named {
                name: "bool".to_owned(),
            },
            ast::Constant::Int(_) => TypeRef::Named {
                name: "int".to_owned(),
            },
            ast::Constant::Str(_) => TypeRef::Named {
                name: "str".to_owned(),
            },
            _ => TypeRef::Unknown {
                source: "unsupported boundary literal".to_owned(),
            },
        },
        _ => TypeRef::Unknown {
            source: "boundary value must be a parameter or primitive literal".to_owned(),
        },
    }
}

fn check_closed_function(
    function: &ast::StmtFunctionDef,
    declaration: &FunctionDecl,
) -> Result<(), FragmentFailure> {
    if !function.decorator_list.is_empty() || !function.type_params.is_empty() {
        return fragment_failure(
            "frontend.python.fragment.decorator-or-type-parameter",
            &declaration.qualified_name,
            "decorators and type parameters are outside closed-total-functions+safe-builtin-slices/v1",
        );
    }
    if function.args.vararg.is_some() || function.args.kwarg.is_some() {
        return fragment_failure(
            "frontend.python.fragment.variadic",
            &declaration.qualified_name,
            "variadic functions are outside closed-total-functions+safe-builtin-slices/v1",
        );
    }
    if function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .chain(function.args.kwonlyargs.iter())
        .any(|argument| argument.default.is_some())
    {
        return fragment_failure(
            "frontend.python.fragment.default-argument",
            &declaration.qualified_name,
            "default argument expressions are evaluated outside the function proof",
        );
    }
    if declaration
        .parameters
        .iter()
        .any(|parameter| !closed_primitive_type(&parameter.type_ref))
        || !closed_primitive_type(&declaration.return_type)
    {
        return fragment_failure(
            "frontend.python.fragment.type-unsupported",
            &declaration.qualified_name,
            "every parameter and return must have a supported explicit closed-fragment type",
        );
    }
    let [ast::Stmt::Return(return_statement)] = function.body.as_slice() else {
        return fragment_failure(
            "frontend.python.fragment.body-unsupported",
            &declaration.qualified_name,
            "the body must be exactly one return statement",
        );
    };
    let actual_type = match return_statement.value.as_deref() {
        Some(expression) => infer_closed_expression(expression, declaration)?,
        None => TypeRef::Named {
            name: "None".to_owned(),
        },
    };
    if actual_type != declaration.return_type {
        return fragment_failure(
            "frontend.python.return-type-mismatch",
            &declaration.qualified_name,
            &format!(
                "declared return {:?}, but the returned expression has type {:?}",
                declaration.return_type, actual_type
            ),
        );
    }
    Ok(())
}

fn infer_closed_expression(
    expression: &ast::Expr,
    declaration: &FunctionDecl,
) -> Result<TypeRef, FragmentFailure> {
    match expression {
        ast::Expr::Name(name) => declaration
            .parameters
            .iter()
            .find(|parameter| parameter.name == name.id.as_str())
            .map(|parameter| parameter.type_ref.clone())
            .ok_or_else(|| FragmentFailure {
                code: "frontend.python.name.unresolved",
                message: format!(
                    "function {:?} returns unresolved name {:?}",
                    declaration.qualified_name, name.id
                ),
            }),
        ast::Expr::Constant(constant) => match constant.value {
            ast::Constant::None => Ok(TypeRef::Named {
                name: "None".to_owned(),
            }),
            ast::Constant::Bool(_) => Ok(TypeRef::Named {
                name: "bool".to_owned(),
            }),
            ast::Constant::Int(_) => Ok(TypeRef::Named {
                name: "int".to_owned(),
            }),
            ast::Constant::Str(_) => Ok(TypeRef::Named {
                name: "str".to_owned(),
            }),
            _ => fragment_failure(
                "frontend.python.fragment.literal-unsupported",
                &declaration.qualified_name,
                "only None, bool, int, and str literals are in the closed fragment",
            ),
        },
        ast::Expr::Subscript(subscript) => {
            let target_type = infer_closed_expression(&subscript.value, declaration)?;
            if !closed_slice_target(&target_type) {
                return fragment_failure(
                    "frontend.python.slice.target-unsupported",
                    &declaration.qualified_name,
                    "only builtin list[T] and str values can be sliced in this fragment",
                );
            }
            let ast::Expr::Slice(slice) = subscript.slice.as_ref() else {
                return fragment_failure(
                    "frontend.python.fragment.index-unsupported",
                    &declaration.qualified_name,
                    "indexed subscription can raise IndexError; only slicing is supported",
                );
            };
            check_slice_bound(slice.lower.as_deref(), declaration, "lower")?;
            check_slice_bound(slice.upper.as_deref(), declaration, "upper")?;
            check_slice_step(slice.step.as_deref(), declaration)?;
            Ok(target_type)
        }
        _ => fragment_failure(
            "frontend.python.fragment.expression-unsupported",
            &declaration.qualified_name,
            "returned expression is outside closed-total-functions/v0",
        ),
    }
}

fn closed_primitive_type(type_ref: &TypeRef) -> bool {
    matches!(
        type_ref,
        TypeRef::Named { name } if matches!(name.as_str(), "int" | "bool" | "str" | "None")
    ) || matches!(
        type_ref,
        TypeRef::Generic { name, arguments }
            if name == "list" && arguments.len() == 1 && closed_primitive_type(&arguments[0])
    )
}

fn closed_slice_target(type_ref: &TypeRef) -> bool {
    matches!(type_ref, TypeRef::Named { name } if name == "str")
        || matches!(type_ref, TypeRef::Generic { name, arguments } if name == "list" && arguments.len() == 1)
}

fn check_slice_bound(
    expression: Option<&ast::Expr>,
    declaration: &FunctionDecl,
    label: &str,
) -> Result<(), FragmentFailure> {
    let Some(expression) = expression else {
        return Ok(());
    };
    let type_ref = infer_closed_expression(expression, declaration)?;
    if matches!(type_ref, TypeRef::Named { ref name } if name == "int" || name == "None") {
        Ok(())
    } else {
        fragment_failure(
            "frontend.python.slice.bound-type",
            &declaration.qualified_name,
            &format!("slice {label} bound must be int or None, found {type_ref:?}"),
        )
    }
}

fn check_slice_step(
    expression: Option<&ast::Expr>,
    declaration: &FunctionDecl,
) -> Result<(), FragmentFailure> {
    let Some(expression) = expression else {
        return Ok(());
    };
    match expression {
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Int(value) if value.to_string() != "0" => Ok(()),
            ast::Constant::Int(_) => fragment_failure(
                "frontend.python.slice.zero-step",
                &declaration.qualified_name,
                "a zero slice step certainly raises ValueError",
            ),
            ast::Constant::None => Ok(()),
            _ => fragment_failure(
                "frontend.python.slice.step-type",
                &declaration.qualified_name,
                "slice step must be a statically nonzero int or None",
            ),
        },
        ast::Expr::Name(name)
            if declaration
                .parameters
                .iter()
                .any(|parameter| parameter.name == name.id.as_str()) =>
        {
            fragment_failure(
                "frontend.python.slice.step-may-be-zero",
                &declaration.qualified_name,
                "an unconstrained int slice step may be zero and raise ValueError",
            )
        }
        _ => fragment_failure(
            "frontend.python.slice.step-unsupported",
            &declaration.qualified_name,
            "slice step expression is outside the proved fragment",
        ),
    }
}

fn fragment_failure<T>(
    code: &'static str,
    function: &str,
    reason: &str,
) -> Result<T, FragmentFailure> {
    Err(FragmentFailure {
        code,
        message: format!("function {function:?}: {reason}"),
    })
}

pub fn analyze_module(source: &str, path: &str) -> Result<PythonModule, String> {
    let suite = ast::Suite::parse(source, path).map_err(|error| error.to_string())?;
    let mut module = PythonModule {
        path: path.to_owned(),
        functions: Vec::new(),
        classes: Vec::new(),
        features: Vec::new(),
        exceptional_effects: Vec::new(),
        type_diagnostics: Vec::new(),
    };

    for statement in &suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                let declaration = function_decl(function, None);
                let locals = parameter_types(&declaration);
                module.functions.push(declaration);
                collect_features(
                    &function.body,
                    function.name.as_str(),
                    &locals,
                    &BTreeMap::new(),
                    &CatchContext::default(),
                    &mut module.features,
                    &mut module.exceptional_effects,
                );
            }
            ast::Stmt::ClassDef(class) => collect_class(class, &mut module),
            _ => {}
        }
    }
    module.type_diagnostics = module
        .features
        .iter()
        .filter_map(|feature| match feature {
            FeatureUse::CallableFieldCall {
                owner,
                field,
                callable_type,
                argument_types,
                type_compatible: false,
                byte_offset,
            } => Some(PythonDiagnostic {
                code: "python.callable-field.argument-type-mismatch".to_owned(),
                message: format!(
                    "call to field {field:?} has arguments {argument_types:?}, incompatible with {callable_type:?}"
                ),
                owner: owner.clone(),
                byte_offset: *byte_offset,
            }),
            _ => None,
        })
        .collect();
    Ok(module)
}

fn collect_class(class: &ast::StmtClassDef, module: &mut PythonModule) {
    let dataclass = class.decorator_list.iter().any(|item| {
        dotted_name(item).is_some_and(|name| name == "dataclass" || name.ends_with(".dataclass"))
    });
    let mut fields = Vec::new();
    let mut methods = Vec::new();
    let mut field_types = BTreeMap::new();

    for statement in &class.body {
        match statement {
            ast::Stmt::AnnAssign(assignment) => {
                if let ast::Expr::Name(name) = assignment.target.as_ref() {
                    let type_ref = parse_type(&assignment.annotation);
                    field_types.insert(name.id.to_string(), type_ref.clone());
                    fields.push(FieldDecl {
                        name: name.id.to_string(),
                        type_ref,
                        byte_offset: assignment.range.start().into(),
                    });
                }
            }
            ast::Stmt::FunctionDef(function) => {
                methods.push(function_decl(function, Some(class.name.as_str())));
            }
            _ => {}
        }
    }

    for statement in &class.body {
        if let ast::Stmt::FunctionDef(function) = statement {
            let declaration = function_decl(function, Some(class.name.as_str()));
            let locals = parameter_types(&declaration);
            collect_features(
                &function.body,
                &format!("{}.{}", class.name, function.name),
                &locals,
                &field_types,
                &CatchContext::default(),
                &mut module.features,
                &mut module.exceptional_effects,
            );
        }
    }

    module.classes.push(ClassDecl {
        name: class.name.to_string(),
        dataclass,
        fields,
        methods,
        byte_offset: class.range.start().into(),
    });
}

fn function_decl(function: &ast::StmtFunctionDef, owner: Option<&str>) -> FunctionDecl {
    let mut parameters = Vec::new();
    for argument in function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .chain(function.args.kwonlyargs.iter())
    {
        parameters.push(parameter(&argument.def));
    }
    if let Some(argument) = function.args.vararg.as_deref() {
        parameters.push(parameter(argument));
    }
    if let Some(argument) = function.args.kwarg.as_deref() {
        parameters.push(parameter(argument));
    }
    FunctionDecl {
        qualified_name: owner
            .map(|owner| format!("{owner}.{}", function.name))
            .unwrap_or_else(|| function.name.to_string()),
        parameters,
        return_type: function
            .returns
            .as_deref()
            .map(parse_type)
            .unwrap_or_else(|| TypeRef::Unknown {
                source: "missing return annotation".to_owned(),
            }),
        byte_offset: function.range.start().into(),
    }
}

fn parameter(argument: &ast::Arg) -> Parameter {
    Parameter {
        name: argument.arg.to_string(),
        type_ref: argument
            .annotation
            .as_deref()
            .map(parse_type)
            .unwrap_or_else(|| TypeRef::Unknown {
                source: "missing parameter annotation".to_owned(),
            }),
    }
}

fn parse_type(expression: &ast::Expr) -> TypeRef {
    match expression {
        ast::Expr::Name(name) => TypeRef::Named {
            name: name.id.to_string(),
        },
        ast::Expr::Attribute(_) => TypeRef::Named {
            name: dotted_name(expression).unwrap_or_else(|| "<attribute>".to_owned()),
        },
        ast::Expr::Subscript(subscript) => {
            let name = dotted_name(&subscript.value).unwrap_or_else(|| "<generic>".to_owned());
            let arguments = subscript_arguments(&subscript.slice);
            if matches!(name.as_str(), "Callable" | "typing.Callable") && arguments.len() == 2 {
                let parameters = match &arguments[0] {
                    TypeRef::Generic { name, arguments } if name == "<type-list>" => {
                        arguments.clone()
                    }
                    other => vec![other.clone()],
                };
                TypeRef::Callable {
                    parameters,
                    result: Box::new(arguments[1].clone()),
                }
            } else if matches!(name.as_str(), "Union" | "typing.Union") {
                TypeRef::Union {
                    alternatives: arguments,
                }
            } else {
                TypeRef::Generic { name, arguments }
            }
        }
        ast::Expr::BinOp(operation) if matches!(operation.op, ast::Operator::BitOr) => {
            let mut alternatives = Vec::new();
            flatten_union(&operation.left, &mut alternatives);
            flatten_union(&operation.right, &mut alternatives);
            TypeRef::Union { alternatives }
        }
        ast::Expr::List(list) => TypeRef::Generic {
            name: "<type-list>".to_owned(),
            arguments: list.elts.iter().map(parse_type).collect(),
        },
        ast::Expr::Constant(constant) if matches!(constant.value, ast::Constant::None) => {
            TypeRef::Named {
                name: "None".to_owned(),
            }
        }
        _ => TypeRef::Unknown {
            source: format!("unsupported annotation node {expression:?}"),
        },
    }
}

fn subscript_arguments(expression: &ast::Expr) -> Vec<TypeRef> {
    match expression {
        ast::Expr::Tuple(tuple) => tuple.elts.iter().map(parse_type).collect(),
        ast::Expr::List(list) => vec![TypeRef::Generic {
            name: "<type-list>".to_owned(),
            arguments: list.elts.iter().map(parse_type).collect(),
        }],
        other => vec![parse_type(other)],
    }
}

fn flatten_union(expression: &ast::Expr, alternatives: &mut Vec<TypeRef>) {
    if let ast::Expr::BinOp(operation) = expression
        && matches!(operation.op, ast::Operator::BitOr)
    {
        flatten_union(&operation.left, alternatives);
        flatten_union(&operation.right, alternatives);
    } else {
        alternatives.push(parse_type(expression));
    }
}

fn dotted_name(expression: &ast::Expr) -> Option<String> {
    match expression {
        ast::Expr::Name(name) => Some(name.id.to_string()),
        ast::Expr::Attribute(attribute) => Some(format!(
            "{}.{}",
            dotted_name(&attribute.value)?,
            attribute.attr
        )),
        _ => None,
    }
}

fn parameter_types(declaration: &FunctionDecl) -> BTreeMap<String, TypeRef> {
    declaration
        .parameters
        .iter()
        .map(|parameter| (parameter.name.clone(), parameter.type_ref.clone()))
        .collect()
}

#[derive(Clone, Debug, Default)]
struct CatchContext {
    catches_all: bool,
    exception_names: BTreeSet<String>,
}

impl CatchContext {
    fn catches(&self, exception_type: Option<&str>) -> bool {
        if self.catches_all || self.exception_names.contains("BaseException") {
            return true;
        }
        let Some(exception_type) = exception_type else {
            return false;
        };
        self.exception_names.contains(exception_type)
            || (matches!(exception_type, "ValueError" | "TypeError" | "IndexError")
                && self.exception_names.contains("Exception"))
    }

    fn combined(&self, other: &Self) -> Self {
        Self {
            catches_all: self.catches_all || other.catches_all,
            exception_names: self
                .exception_names
                .union(&other.exception_names)
                .cloned()
                .collect(),
        }
    }
}

fn handler_context(handlers: &[ast::ExceptHandler]) -> CatchContext {
    let mut context = CatchContext::default();
    for handler in handlers {
        let ast::ExceptHandler::ExceptHandler(handler) = handler;
        match handler.type_.as_deref() {
            None => context.catches_all = true,
            Some(ast::Expr::Tuple(tuple)) => {
                for item in &tuple.elts {
                    if let Some(name) = dotted_name(item) {
                        context.exception_names.insert(name);
                    }
                }
            }
            Some(expression) => {
                if let Some(name) = dotted_name(expression) {
                    context.exception_names.insert(name);
                }
            }
        }
    }
    context
}

fn collect_features(
    statements: &[ast::Stmt],
    owner: &str,
    locals: &BTreeMap<String, TypeRef>,
    field_types: &BTreeMap<String, TypeRef>,
    catches: &CatchContext,
    features: &mut Vec<FeatureUse>,
    effects: &mut Vec<ExceptionalEffect>,
) {
    for statement in statements {
        walk_statement(
            statement,
            owner,
            locals,
            field_types,
            catches,
            features,
            effects,
        );
    }
}

fn walk_statement(
    statement: &ast::Stmt,
    owner: &str,
    locals: &BTreeMap<String, TypeRef>,
    field_types: &BTreeMap<String, TypeRef>,
    catches: &CatchContext,
    features: &mut Vec<FeatureUse>,
    effects: &mut Vec<ExceptionalEffect>,
) {
    match statement {
        ast::Stmt::Return(item) => {
            if let Some(value) = item.value.as_deref() {
                walk_expression(
                    value,
                    owner,
                    locals,
                    field_types,
                    catches,
                    features,
                    effects,
                );
            }
        }
        ast::Stmt::Assign(item) => {
            walk_expression(
                &item.value,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            for target in &item.targets {
                walk_expression(
                    target,
                    owner,
                    locals,
                    field_types,
                    catches,
                    features,
                    effects,
                );
            }
        }
        ast::Stmt::AnnAssign(item) => {
            if let Some(value) = item.value.as_deref() {
                walk_expression(
                    value,
                    owner,
                    locals,
                    field_types,
                    catches,
                    features,
                    effects,
                );
            }
        }
        ast::Stmt::Expr(item) => walk_expression(
            &item.value,
            owner,
            locals,
            field_types,
            catches,
            features,
            effects,
        ),
        ast::Stmt::If(item) => {
            walk_expression(
                &item.test,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            collect_features(
                &item.body,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            collect_features(
                &item.orelse,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
        }
        ast::Stmt::For(item) => {
            walk_expression(
                &item.iter,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            collect_features(
                &item.body,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            collect_features(
                &item.orelse,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
        }
        ast::Stmt::While(item) => {
            walk_expression(
                &item.test,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            collect_features(
                &item.body,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            collect_features(
                &item.orelse,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
        }
        ast::Stmt::Try(item) => {
            let body_catches = catches.combined(&handler_context(&item.handlers));
            collect_features(
                &item.body,
                owner,
                locals,
                field_types,
                &body_catches,
                features,
                effects,
            );
            for handler in &item.handlers {
                let ast::ExceptHandler::ExceptHandler(handler) = handler;
                collect_features(
                    &handler.body,
                    owner,
                    locals,
                    field_types,
                    catches,
                    features,
                    effects,
                );
            }
            collect_features(
                &item.orelse,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            collect_features(
                &item.finalbody,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
        }
        _ => {}
    }
}

fn walk_expression(
    expression: &ast::Expr,
    owner: &str,
    locals: &BTreeMap<String, TypeRef>,
    field_types: &BTreeMap<String, TypeRef>,
    catches: &CatchContext,
    features: &mut Vec<FeatureUse>,
    effects: &mut Vec<ExceptionalEffect>,
) {
    match expression {
        ast::Expr::Subscript(subscript) => {
            if let ast::Expr::Slice(slice) = subscript.slice.as_ref() {
                let target_type = dotted_name(&subscript.value)
                    .and_then(|name| locals.get(&name).cloned())
                    .unwrap_or_else(|| TypeRef::Unknown {
                        source: "slice target type is unresolved".to_owned(),
                    });
                features.push(FeatureUse::Slice {
                    owner: owner.to_owned(),
                    target: dotted_name(&subscript.value)
                        .unwrap_or_else(|| "<expression>".to_owned()),
                    target_type: target_type.clone(),
                    has_lower: slice.lower.is_some(),
                    has_upper: slice.upper.is_some(),
                    has_step: slice.step.is_some(),
                    byte_offset: subscript.range.start().into(),
                });
                let (exception_type, certainty) = slice_exception(slice, &target_type);
                if exception_type.is_some() || matches!(certainty, EffectCertainty::Unknown) {
                    effects.push(ExceptionalEffect {
                        owner: owner.to_owned(),
                        exception_type: exception_type.clone(),
                        origin: "slice".to_owned(),
                        certainty,
                        escapes: !catches.catches(exception_type.as_deref()),
                        byte_offset: subscript.range.start().into(),
                    });
                }
            }
            walk_expression(
                &subscript.value,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            walk_expression(
                &subscript.slice,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
        }
        ast::Expr::Call(call) => {
            if let ast::Expr::Attribute(attribute) = call.func.as_ref()
                && let ast::Expr::Name(receiver) = attribute.value.as_ref()
                && receiver.id.as_str() == "self"
                && let Some(callable_type @ TypeRef::Callable { .. }) =
                    field_types.get(attribute.attr.as_str())
            {
                let argument_types: Vec<TypeRef> = call
                    .args
                    .iter()
                    .map(|argument| infer_obvious_type(argument, locals, field_types))
                    .collect();
                let type_compatible = match callable_type {
                    TypeRef::Callable { parameters, .. } => {
                        call.keywords.is_empty()
                            && parameters.len() == argument_types.len()
                            && parameters
                                .iter()
                                .zip(&argument_types)
                                .all(|(expected, actual)| expected == actual)
                    }
                    _ => false,
                };
                features.push(FeatureUse::CallableFieldCall {
                    owner: owner.to_owned(),
                    field: attribute.attr.to_string(),
                    callable_type: callable_type.clone(),
                    argument_types,
                    type_compatible,
                    byte_offset: call.range.start().into(),
                });
                effects.push(ExceptionalEffect {
                    owner: owner.to_owned(),
                    exception_type: None,
                    origin: format!("callable-field:{}", attribute.attr),
                    certainty: EffectCertainty::Unknown,
                    escapes: !catches.catches(None),
                    byte_offset: call.range.start().into(),
                });
            }
            walk_expression(
                &call.func,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            for argument in &call.args {
                walk_expression(
                    argument,
                    owner,
                    locals,
                    field_types,
                    catches,
                    features,
                    effects,
                );
            }
            for keyword in &call.keywords {
                walk_expression(
                    &keyword.value,
                    owner,
                    locals,
                    field_types,
                    catches,
                    features,
                    effects,
                );
            }
        }
        ast::Expr::Attribute(attribute) => walk_expression(
            &attribute.value,
            owner,
            locals,
            field_types,
            catches,
            features,
            effects,
        ),
        ast::Expr::BinOp(operation) => {
            walk_expression(
                &operation.left,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
            walk_expression(
                &operation.right,
                owner,
                locals,
                field_types,
                catches,
                features,
                effects,
            );
        }
        ast::Expr::List(list) => {
            for item in &list.elts {
                walk_expression(item, owner, locals, field_types, catches, features, effects);
            }
        }
        ast::Expr::Tuple(tuple) => {
            for item in &tuple.elts {
                walk_expression(item, owner, locals, field_types, catches, features, effects);
            }
        }
        ast::Expr::Slice(slice) => {
            for item in [&slice.lower, &slice.upper, &slice.step]
                .into_iter()
                .filter_map(|item| item.as_deref())
            {
                walk_expression(item, owner, locals, field_types, catches, features, effects);
            }
        }
        _ => {}
    }
}

fn infer_obvious_type(
    expression: &ast::Expr,
    locals: &BTreeMap<String, TypeRef>,
    field_types: &BTreeMap<String, TypeRef>,
) -> TypeRef {
    match expression {
        ast::Expr::Name(name) => {
            locals
                .get(name.id.as_str())
                .cloned()
                .unwrap_or_else(|| TypeRef::Unknown {
                    source: format!("unresolved name {}", name.id),
                })
        }
        ast::Expr::Attribute(attribute) => {
            if matches!(attribute.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "self")
            {
                field_types
                    .get(attribute.attr.as_str())
                    .cloned()
                    .unwrap_or_else(|| TypeRef::Unknown {
                        source: format!("unresolved self field {}", attribute.attr),
                    })
            } else {
                TypeRef::Unknown {
                    source: "unresolved attribute".to_owned(),
                }
            }
        }
        ast::Expr::Constant(constant) => match constant.value {
            ast::Constant::None => TypeRef::Named {
                name: "None".to_owned(),
            },
            ast::Constant::Bool(_) => TypeRef::Named {
                name: "bool".to_owned(),
            },
            ast::Constant::Int(_) => TypeRef::Named {
                name: "int".to_owned(),
            },
            ast::Constant::Str(_) => TypeRef::Named {
                name: "str".to_owned(),
            },
            _ => TypeRef::Unknown {
                source: "unsupported literal".to_owned(),
            },
        },
        _ => TypeRef::Unknown {
            source: "expression type not yet inferred".to_owned(),
        },
    }
}

fn slice_exception(
    slice: &ast::ExprSlice,
    target_type: &TypeRef,
) -> (Option<String>, EffectCertainty) {
    let builtin_slice = matches!(
        target_type,
        TypeRef::Generic { name, .. } if matches!(name.as_str(), "list" | "List" | "tuple" | "Tuple")
    ) || matches!(
        target_type,
        TypeRef::Named { name } if matches!(name.as_str(), "str" | "bytes" | "bytearray")
    );
    if !builtin_slice {
        return (None, EffectCertainty::Unknown);
    }
    match slice.step.as_deref() {
        None => (None, EffectCertainty::Certain),
        Some(ast::Expr::Constant(constant)) => match &constant.value {
            ast::Constant::Int(value) if value.to_string() == "0" => {
                (Some("ValueError".to_owned()), EffectCertainty::Certain)
            }
            ast::Constant::Int(_) | ast::Constant::None => (None, EffectCertainty::Certain),
            _ => (Some("TypeError".to_owned()), EffectCertainty::Certain),
        },
        Some(ast::Expr::Name(_)) => (Some("ValueError".to_owned()), EffectCertainty::Potential),
        Some(_) => (None, EffectCertainty::Unknown),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn named(name: &str) -> TypeRef {
        TypeRef::Named {
            name: name.to_owned(),
        }
    }

    #[test]
    fn extracts_callable_valued_dataclass_field_and_call() {
        let module = analyze_module(
            "from dataclasses import dataclass\nfrom typing import Callable\n\n@dataclass\nclass Runner:\n    callback: Callable[[str, int], bool]\n\n    def run(self, value: str) -> bool:\n        return self.callback(value, 1)\n",
            "callback.py",
        )
        .unwrap();

        assert!(module.classes[0].dataclass);
        let callable = TypeRef::Callable {
            parameters: vec![named("str"), named("int")],
            result: Box::new(named("bool")),
        };
        assert_eq!(module.classes[0].fields[0].type_ref, callable);
        assert!(matches!(
            &module.features[0],
            FeatureUse::CallableFieldCall { field, callable_type, type_compatible: true, .. }
                if field == "callback" && callable_type == &callable
        ));
        assert!(module.type_diagnostics.is_empty());
    }

    #[test]
    fn proves_caught_callable_field_as_a_total_boundary() {
        let methods = prove_caught_callable_fragment(
            "from dataclasses import dataclass\nfrom typing import Callable\n\n@dataclass\nclass Runner:\n    callback: Callable[[str], bool]\n\n    def run(self, value: str) -> bool:\n        try:\n            return self.callback(value)\n        except BaseException:\n            return False\n",
            "callback.py",
            &["Runner.run".to_owned()],
        )
        .unwrap();
        assert_eq!(methods[0].qualified_name, "Runner.run");
    }

    #[test]
    fn caught_callable_fallback_must_preserve_the_declared_return_type() {
        let error = prove_caught_callable_fragment(
            "from dataclasses import dataclass\nfrom typing import Callable\n\n@dataclass\nclass Runner:\n    callback: Callable[[str], bool]\n\n    def run(self, value: str) -> bool:\n        try:\n            return self.callback(value)\n        except:\n            return 'failed'\n",
            "callback.py",
            &["Runner.run".to_owned()],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.callable-boundary.failure-type-mismatch"
        );
    }

    #[test]
    fn extracts_slice_bounds_and_step_without_crashing() {
        let module = analyze_module(
            "def middle(values: list[int], start: int, stop: int) -> list[int]:\n    return values[start:stop:2]\n",
            "slice.py",
        )
        .unwrap();

        assert!(matches!(
            &module.features[0],
            FeatureUse::Slice {
                target,
                has_lower: true,
                has_upper: true,
                has_step: true,
                ..
            } if target == "values"
        ));
        assert!(module.exceptional_effects.is_empty());
    }

    #[test]
    fn parses_pep604_union_types() {
        let module = analyze_module(
            "def choose(value: str | None) -> int | str:\n    return 1\n",
            "union.py",
        )
        .unwrap();
        assert_eq!(
            module.functions[0].parameters[0].type_ref,
            TypeRef::Union {
                alternatives: vec![named("str"), named("None")],
            }
        );
    }

    #[test]
    fn proves_closed_total_identity_and_literal_functions() {
        let functions = prove_closed_fragment(
            "def identity(value: str) -> str:\n    return value\n\ndef answer() -> int:\n    return 42\n",
            "closed.py",
            &["identity".to_owned(), "answer".to_owned()],
        )
        .unwrap();
        assert_eq!(functions.len(), 2);
    }

    #[test]
    fn refuses_return_type_mismatch() {
        let error = prove_closed_fragment(
            "def wrong() -> str:\n    return 42\n",
            "wrong.py",
            &["wrong".to_owned()],
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.python.return-type-mismatch");
    }

    #[test]
    fn refuses_calls_instead_of_treating_them_as_exception_free() {
        let error = prove_closed_fragment(
            "def unsafe(value: str) -> str:\n    return value.strip()\n",
            "unsafe.py",
            &["unsafe".to_owned()],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.fragment.expression-unsupported"
        );
    }

    #[test]
    fn proves_builtin_slice_with_safe_bounds_and_nonzero_step() {
        let functions = prove_closed_fragment(
            "def take(values: list[int], start: int, stop: int) -> list[int]:\n    return values[start:stop:2]\n",
            "take.py",
            &["take".to_owned()],
        )
        .unwrap();
        assert_eq!(functions[0].qualified_name, "take");
    }

    #[test]
    fn refuses_dynamic_slice_step_that_may_be_zero() {
        let error = prove_closed_fragment(
            "def take(values: list[int], step: int) -> list[int]:\n    return values[::step]\n",
            "take.py",
            &["take".to_owned()],
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.python.slice.step-may-be-zero");
    }

    #[test]
    fn refuses_certain_zero_slice_step() {
        let error = prove_closed_fragment(
            "def take(values: list[int]) -> list[int]:\n    return values[::0]\n",
            "take.py",
            &["take".to_owned()],
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.python.slice.zero-step");
    }

    #[test]
    fn models_dynamic_builtin_slice_step_as_potential_value_error() {
        let module = analyze_module(
            "def stride(values: list[int], step: int) -> list[int]:\n    return values[::step]\n",
            "stride.py",
        )
        .unwrap();
        assert!(matches!(
            &module.exceptional_effects[0],
            ExceptionalEffect {
                exception_type: Some(exception_type),
                certainty: EffectCertainty::Potential,
                escapes: true,
                ..
            } if exception_type == "ValueError"
        ));
    }

    #[test]
    fn models_zero_builtin_slice_step_as_certain_value_error() {
        let module = analyze_module(
            "def broken(values: list[int]) -> list[int]:\n    return values[::0]\n",
            "broken.py",
        )
        .unwrap();
        assert!(matches!(
            &module.exceptional_effects[0],
            ExceptionalEffect {
                exception_type: Some(exception_type),
                certainty: EffectCertainty::Certain,
                escapes: true,
                ..
            } if exception_type == "ValueError"
        ));
    }

    #[test]
    fn bare_except_closes_unknown_callable_field_effect() {
        let module = analyze_module(
            "from dataclasses import dataclass\nfrom typing import Callable\n\n@dataclass\nclass Runner:\n    callback: Callable[[str], bool]\n\n    def run(self, value: str) -> bool:\n        try:\n            return self.callback(value)\n        except:\n            return False\n",
            "caught.py",
        )
        .unwrap();
        assert!(matches!(
            &module.exceptional_effects[0],
            ExceptionalEffect {
                exception_type: None,
                certainty: EffectCertainty::Unknown,
                escapes: false,
                ..
            }
        ));
    }

    #[test]
    fn except_exception_does_not_lie_about_unknown_base_exception() {
        let module = analyze_module(
            "from dataclasses import dataclass\nfrom typing import Callable\n\n@dataclass\nclass Runner:\n    callback: Callable[[str], bool]\n\n    def run(self, value: str) -> bool:\n        try:\n            return self.callback(value)\n        except Exception:\n            return False\n",
            "partly-caught.py",
        )
        .unwrap();
        assert!(module.exceptional_effects[0].escapes);
    }

    #[test]
    fn rejects_wrong_argument_type_for_callable_valued_field() {
        let module = analyze_module(
            "from dataclasses import dataclass\nfrom typing import Callable\n\n@dataclass\nclass Runner:\n    callback: Callable[[str], bool]\n\n    def run(self, value: int) -> bool:\n        return self.callback(value)\n",
            "wrong-callback.py",
        )
        .unwrap();
        assert!(matches!(
            &module.features[0],
            FeatureUse::CallableFieldCall {
                type_compatible: false,
                ..
            }
        ));
        assert_eq!(
            module.type_diagnostics[0].code,
            "python.callable-field.argument-type-mismatch"
        );
    }
}
