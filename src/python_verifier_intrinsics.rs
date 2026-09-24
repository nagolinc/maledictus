//! Canonical verifier-library declarations whose meaning is supplied by the verifier.
//!
//! These declarations are not executable Python implementations and must never be converted
//! into ordinary source or checked-external call summaries.  A provider is admitted only after
//! its complete, pinned ABI has been checked structurally.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use rustpython_parser::{Parse, ast};

use crate::python_contracts::ContractFailure;

pub const CANONICAL_OBLIGATIONS_MODULE: &str = "nagini_contracts.obligations";

const CANONICAL_OBLIGATIONS_PATH: [&str; 3] = ["src", "nagini_contracts", "obligations.py"];

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum VerifierIntrinsicKind {
    Level,
    WaitLevel,
    MustRelease,
    MustTerminate,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum VerifierIntrinsicType {
    Bool,
    Int,
    Level,
    Nominal(String),
    Optional(Box<VerifierIntrinsicType>),
    Union(Vec<VerifierIntrinsicType>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifierIntrinsicParameter {
    pub name: String,
    pub value_type: VerifierIntrinsicType,
    pub has_default: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifierIntrinsicFunctionDescriptor {
    pub kind: VerifierIntrinsicKind,
    pub public_name: String,
    pub canonical_identity: String,
    pub parameters: Vec<VerifierIntrinsicParameter>,
    pub result: VerifierIntrinsicType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifierIntrinsicMethodDescriptor {
    pub public_name: String,
    pub canonical_identity: String,
    pub parameters: Vec<VerifierIntrinsicParameter>,
    pub result: VerifierIntrinsicType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifierIntrinsicClassDescriptor {
    pub public_name: String,
    pub canonical_identity: String,
    pub methods: BTreeMap<String, VerifierIntrinsicMethodDescriptor>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifierIntrinsicProvider {
    pub module: String,
    /// The provider's exact explicit `__all__`, used for canonical star-import binding.
    pub public_exports: BTreeSet<String>,
    pub classes: BTreeMap<String, VerifierIntrinsicClassDescriptor>,
    pub functions: BTreeMap<String, VerifierIntrinsicFunctionDescriptor>,
}

pub fn is_canonical_obligations_provider_path(
    suite_root: &Path,
    module: &str,
    provider_path: &Path,
) -> bool {
    module == CANONICAL_OBLIGATIONS_MODULE
        && provider_path
            == CANONICAL_OBLIGATIONS_PATH
                .iter()
                .fold(suite_root.to_path_buf(), |path, component| {
                    path.join(component)
                })
}

pub fn validate_canonical_obligations_provider(
    source: &str,
    path: &str,
) -> Result<VerifierIntrinsicProvider, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.verifier-intrinsic.parse-error",
        message: error.to_string(),
    })?;
    let [
        license_docstring,
        module_docstring,
        typing_import,
        thread_import,
        metadata,
        base_lock,
        level_type,
        wait_level,
        level,
        must_release,
        must_terminate,
        exports,
    ] = suite.as_slice()
    else {
        return intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-module-shape",
            "canonical obligations provider must contain exactly its declared ABI bindings",
        );
    };
    require_docstring_statement(license_docstring, "license")?;
    require_docstring_statement(module_docstring, "module")?;
    require_import(typing_import, "typing", "Union")?;
    require_import(thread_import, "nagini_contracts.thread", "Thread")?;
    require_obligation_metadata(metadata)?;

    require_empty_marker_class(base_lock, "BaseLock")?;
    let level_method = require_level_type_class(level_type)?;
    require_function(
        wait_level,
        FunctionAbi {
            name: "WaitLevel",
            parameters: &[],
            result: AnnotationAbi::Name("LevelType"),
        },
    )?;
    require_exports(exports)?;
    require_function(
        level,
        FunctionAbi {
            name: "Level",
            parameters: &[ParameterAbi {
                name: "l",
                annotation: AnnotationAbi::Union("BaseLock", "Thread"),
                default_none: false,
            }],
            result: AnnotationAbi::Name("LevelType"),
        },
    )?;
    require_function(
        must_release,
        FunctionAbi {
            name: "MustRelease",
            parameters: &[
                ParameterAbi {
                    name: "lock",
                    annotation: AnnotationAbi::Name("BaseLock"),
                    default_none: false,
                },
                ParameterAbi {
                    name: "measure",
                    annotation: AnnotationAbi::Name("int"),
                    default_none: true,
                },
            ],
            result: AnnotationAbi::Name("bool"),
        },
    )?;
    require_function(
        must_terminate,
        FunctionAbi {
            name: "MustTerminate",
            parameters: &[ParameterAbi {
                name: "measure",
                annotation: AnnotationAbi::Name("int"),
                default_none: false,
            }],
            result: AnnotationAbi::Name("bool"),
        },
    )?;

    Ok(build_provider(level_method))
}

fn build_provider(level_method: VerifierIntrinsicMethodDescriptor) -> VerifierIntrinsicProvider {
    let nominal = |name: &str| {
        VerifierIntrinsicType::Nominal(format!("{CANONICAL_OBLIGATIONS_MODULE}.{name}"))
    };
    let parameter = |name: &str, value_type, has_default| VerifierIntrinsicParameter {
        name: name.to_owned(),
        value_type,
        has_default,
    };
    let function = |kind, name: &str, parameters, result| {
        (
            name.to_owned(),
            VerifierIntrinsicFunctionDescriptor {
                kind,
                public_name: name.to_owned(),
                canonical_identity: format!("{CANONICAL_OBLIGATIONS_MODULE}.{name}"),
                parameters,
                result,
            },
        )
    };
    let functions = [
        function(
            VerifierIntrinsicKind::WaitLevel,
            "WaitLevel",
            Vec::new(),
            VerifierIntrinsicType::Level,
        ),
        function(
            VerifierIntrinsicKind::Level,
            "Level",
            vec![parameter(
                "l",
                VerifierIntrinsicType::Union(vec![
                    nominal("BaseLock"),
                    VerifierIntrinsicType::Nominal("nagini_contracts.thread.Thread".to_owned()),
                ]),
                false,
            )],
            VerifierIntrinsicType::Level,
        ),
        function(
            VerifierIntrinsicKind::MustRelease,
            "MustRelease",
            vec![
                parameter("lock", nominal("BaseLock"), false),
                parameter(
                    "measure",
                    VerifierIntrinsicType::Optional(Box::new(VerifierIntrinsicType::Int)),
                    true,
                ),
            ],
            VerifierIntrinsicType::Bool,
        ),
        function(
            VerifierIntrinsicKind::MustTerminate,
            "MustTerminate",
            vec![parameter("measure", VerifierIntrinsicType::Int, false)],
            VerifierIntrinsicType::Bool,
        ),
    ]
    .into_iter()
    .collect();
    let classes = [
        (
            "BaseLock".to_owned(),
            VerifierIntrinsicClassDescriptor {
                public_name: "BaseLock".to_owned(),
                canonical_identity: format!("{CANONICAL_OBLIGATIONS_MODULE}.BaseLock"),
                methods: BTreeMap::new(),
            },
        ),
        (
            "LevelType".to_owned(),
            VerifierIntrinsicClassDescriptor {
                public_name: "LevelType".to_owned(),
                canonical_identity: format!("{CANONICAL_OBLIGATIONS_MODULE}.LevelType"),
                methods: [("__lt__".to_owned(), level_method)].into_iter().collect(),
            },
        ),
    ]
    .into_iter()
    .collect();
    VerifierIntrinsicProvider {
        module: CANONICAL_OBLIGATIONS_MODULE.to_owned(),
        public_exports: [
            "MustRelease",
            "MustTerminate",
            "LevelType",
            "WaitLevel",
            "Level",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect(),
        classes,
        functions,
    }
}

#[derive(Clone, Copy)]
enum AnnotationAbi<'a> {
    Name(&'a str),
    Forward(&'a str),
    Union(&'a str, &'a str),
}

#[derive(Clone, Copy)]
struct ParameterAbi<'a> {
    name: &'a str,
    annotation: AnnotationAbi<'a>,
    default_none: bool,
}

#[derive(Clone, Copy)]
struct FunctionAbi<'a> {
    name: &'a str,
    parameters: &'a [ParameterAbi<'a>],
    result: AnnotationAbi<'a>,
}

fn require_function(
    statement: &ast::Stmt,
    expected: FunctionAbi<'_>,
) -> Result<(), ContractFailure> {
    let ast::Stmt::FunctionDef(function) = statement else {
        return intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-function-missing",
            format!(
                "canonical obligations provider is missing function {:?}",
                expected.name
            ),
        );
    };
    if function.name.as_str() != expected.name
        || !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || function.args.vararg.is_some()
        || function.args.kwarg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || !function.args.posonlyargs.is_empty()
        || function.args.args.len() != expected.parameters.len()
        || !annotation_matches(function.returns.as_deref(), expected.result)
        || !function
            .args
            .args
            .iter()
            .zip(expected.parameters)
            .all(|(actual, expected)| parameter_matches(actual, *expected))
    {
        return intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-signature-drift",
            format!(
                "canonical intrinsic function {:?} has ABI drift",
                expected.name
            ),
        );
    }
    require_declaration_only_body(&function.body, expected.name)
}

fn parameter_matches(actual: &ast::ArgWithDefault, expected: ParameterAbi<'_>) -> bool {
    actual.def.arg.as_str() == expected.name
        && annotation_matches(actual.def.annotation.as_deref(), expected.annotation)
        && if expected.default_none {
            actual.default.as_deref().is_some_and(is_none_literal)
        } else {
            actual.default.is_none()
        }
}

fn annotation_matches(expression: Option<&ast::Expr>, expected: AnnotationAbi<'_>) -> bool {
    match (expression, expected) {
        (Some(ast::Expr::Name(name)), AnnotationAbi::Name(expected)) => {
            name.id.as_str() == expected
        }
        (Some(ast::Expr::Constant(value)), AnnotationAbi::Forward(expected)) => {
            matches!(&value.value, ast::Constant::Str(value) if value == expected)
        }
        (Some(ast::Expr::Subscript(subscript)), AnnotationAbi::Union(left, right)) => {
            matches!(subscript.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Union")
                && matches!(subscript.slice.as_ref(), ast::Expr::Tuple(tuple)
                    if matches!(tuple.elts.as_slice(), [ast::Expr::Name(first), ast::Expr::Name(second)]
                        if first.id.as_str() == left && second.id.as_str() == right))
        }
        _ => false,
    }
}

fn require_level_type_class(
    statement: &ast::Stmt,
) -> Result<VerifierIntrinsicMethodDescriptor, ContractFailure> {
    let ast::Stmt::ClassDef(class) = statement else {
        return intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-class-missing",
            "canonical obligations provider is missing LevelType",
        );
    };
    if class.name.as_str() != "LevelType"
        || !class.bases.is_empty()
        || !class.keywords.is_empty()
        || !class.decorator_list.is_empty()
        || !class.type_params.is_empty()
    {
        return intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-class-drift",
            "canonical LevelType class has ABI drift",
        );
    }
    let [docstring, method] = class.body.as_slice() else {
        return intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-class-drift",
            "canonical LevelType must contain only its declaration-only __lt__ method",
        );
    };
    require_docstring_statement(docstring, "LevelType")?;
    let ast::Stmt::FunctionDef(method) = method else {
        return intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-method-missing",
            "canonical LevelType is missing __lt__",
        );
    };
    let expected_parameters = [
        ParameterAbi {
            name: "self",
            annotation: AnnotationAbi::Name(""),
            default_none: false,
        },
        ParameterAbi {
            name: "other",
            annotation: AnnotationAbi::Forward("LevelType"),
            default_none: false,
        },
    ];
    if method.name.as_str() != "__lt__"
        || !method.decorator_list.is_empty()
        || !method.type_params.is_empty()
        || method.args.vararg.is_some()
        || method.args.kwarg.is_some()
        || !method.args.kwonlyargs.is_empty()
        || !method.args.posonlyargs.is_empty()
        || method.args.args.len() != 2
        || method.args.args[0].def.arg.as_str() != "self"
        || method.args.args[0].def.annotation.is_some()
        || method.args.args[0].default.is_some()
        || !parameter_matches(&method.args.args[1], expected_parameters[1])
        || !annotation_matches(method.returns.as_deref(), AnnotationAbi::Name("bool"))
    {
        return intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-signature-drift",
            "canonical LevelType.__lt__ has ABI drift",
        );
    }
    require_declaration_only_body(&method.body, "LevelType.__lt__")?;
    let level = VerifierIntrinsicType::Level;
    Ok(VerifierIntrinsicMethodDescriptor {
        public_name: "__lt__".to_owned(),
        canonical_identity: format!("{CANONICAL_OBLIGATIONS_MODULE}.LevelType.__lt__"),
        parameters: vec![
            VerifierIntrinsicParameter {
                name: "self".to_owned(),
                value_type: level.clone(),
                has_default: false,
            },
            VerifierIntrinsicParameter {
                name: "other".to_owned(),
                value_type: level,
                has_default: false,
            },
        ],
        result: VerifierIntrinsicType::Bool,
    })
}

fn require_empty_marker_class(statement: &ast::Stmt, name: &str) -> Result<(), ContractFailure> {
    let ast::Stmt::ClassDef(class) = statement else {
        return intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-class-missing",
            format!("canonical obligations provider is missing class {name:?}"),
        );
    };
    if class.name.as_str() != name
        || !class.bases.is_empty()
        || !class.keywords.is_empty()
        || !class.decorator_list.is_empty()
        || !class.type_params.is_empty()
        || class.body.len() != 1
    {
        return intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-class-drift",
            format!("canonical marker class {name:?} has ABI drift"),
        );
    }
    require_docstring_statement(&class.body[0], name)
}

fn require_import(statement: &ast::Stmt, module: &str, name: &str) -> Result<(), ContractFailure> {
    let valid = matches!(statement, ast::Stmt::ImportFrom(import)
        if import.level.is_none_or(|level| level == 0_u32)
            && import.module.as_ref().is_some_and(|actual| actual.as_str() == module)
            && matches!(import.names.as_slice(), [alias]
                if alias.name.as_str() == name && alias.asname.is_none()));
    if valid {
        Ok(())
    } else {
        intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-import-drift",
            format!("canonical obligations provider must import {name} directly from {module}"),
        )
    }
}

fn require_obligation_metadata(statement: &ast::Stmt) -> Result<(), ContractFailure> {
    let valid = matches!(statement, ast::Stmt::Assign(assignment)
        if matches!(assignment.targets.as_slice(), [ast::Expr::Name(name)]
            if name.id.as_str() == "OBLIGATION_CONTRACT_FUNCS")
            && matches!(assignment.value.as_ref(), ast::Expr::List(list)
                if list.elts.len() == 4
                    && list.elts.iter().zip(["MustTerminate", "MustRelease", "Level", "WaitLevel"])
                        .all(|(item, expected)| matches!(item, ast::Expr::Constant(value)
                            if matches!(&value.value, ast::Constant::Str(actual) if actual == expected)))));
    if valid {
        Ok(())
    } else {
        intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-export-drift",
            "canonical OBLIGATION_CONTRACT_FUNCS export metadata has ABI drift",
        )
    }
}

fn require_exports(statement: &ast::Stmt) -> Result<(), ContractFailure> {
    let valid = matches!(statement, ast::Stmt::Assign(assignment)
        if matches!(assignment.targets.as_slice(), [ast::Expr::Name(name)]
            if name.id.as_str() == "__all__")
            && matches!(assignment.value.as_ref(), ast::Expr::Tuple(tuple)
                if tuple.elts.len() == 5
                    && tuple.elts.iter().zip(["MustRelease", "MustTerminate", "LevelType", "WaitLevel", "Level"])
                        .all(|(item, expected)| matches!(item, ast::Expr::Constant(value)
                            if matches!(&value.value, ast::Constant::Str(actual) if actual == expected)))));
    if valid {
        Ok(())
    } else {
        intrinsic_failure(
            "frontend.python.verifier-intrinsic.obligations-export-drift",
            "canonical obligations provider __all__ has ABI drift",
        )
    }
}

fn require_declaration_only_body(body: &[ast::Stmt], owner: &str) -> Result<(), ContractFailure> {
    if matches!(body, [statement] if is_docstring_statement(statement)) {
        Ok(())
    } else {
        intrinsic_failure(
            "frontend.python.verifier-intrinsic.executable-body-refused",
            format!("verifier intrinsic declaration {owner:?} must not contain executable code"),
        )
    }
}

fn require_docstring_statement(statement: &ast::Stmt, owner: &str) -> Result<(), ContractFailure> {
    if is_docstring_statement(statement) {
        Ok(())
    } else {
        intrinsic_failure(
            "frontend.python.verifier-intrinsic.declaration-docstring-missing",
            format!("verifier intrinsic declaration {owner:?} requires its declaration docstring"),
        )
    }
}

fn is_docstring_statement(statement: &ast::Stmt) -> bool {
    matches!(statement, ast::Stmt::Expr(expression)
        if matches!(expression.value.as_ref(), ast::Expr::Constant(constant)
            if matches!(constant.value, ast::Constant::Str(_))))
}

fn is_none_literal(expression: &ast::Expr) -> bool {
    matches!(expression, ast::Expr::Constant(constant) if constant.value == ast::Constant::None)
}

fn intrinsic_failure<T>(
    code: &'static str,
    message: impl Into<String>,
) -> Result<T, ContractFailure> {
    Err(ContractFailure {
        code,
        message: message.into(),
    })
}
