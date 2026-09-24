//! Fail-closed TypeScript frontend driven by the pinned real TypeScript compiler.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde::Deserialize;
use sha2::{Digest, Sha256};

use crate::kernel::{ExitEffect, check_exit_effects};
use crate::protocol::{TypeScriptToolchainIdentity, VerifiedLeafInterface, VerifiedLeafParameter};

const TYPESCRIPT_VERSION: &str = "5.9.3";
pub const TYPESCRIPT_FRAGMENT: &str = "strict-typescript-closed-total-functions/v11";
pub const JAVASCRIPT_FRAGMENT: &str = "strict-javascript-jsdoc-closed-total-functions/v11";

#[derive(Clone, Copy, Debug)]
enum SourceLanguage {
    JavaScript,
    TypeScript,
}

impl SourceLanguage {
    fn name(self) -> &'static str {
        match self {
            Self::JavaScript => "javascript",
            Self::TypeScript => "typescript",
        }
    }

    fn schema(self) -> &'static str {
        match self {
            Self::JavaScript => "maledictus-javascript-closed-verification/v8",
            Self::TypeScript => "maledictus-typescript-closed-verification/v8",
        }
    }

    fn code(self, suffix: &str) -> String {
        format!("frontend.{}.{suffix}", self.name())
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TypeScriptFunction {
    pub name: String,
    pub exported: bool,
    pub execution: TypeScriptExecution,
    pub parameters: Vec<TypeScriptParameter>,
    pub return_type: String,
    pub calls: Vec<String>,
    pub outcome_graph: TypeScriptOutcomeGraph,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum TypeScriptExecution {
    Synchronous,
    Asynchronous,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct RecordField {
    pub name: String,
    pub type_name: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct TypeScriptClass {
    pub name: String,
    pub fields: Vec<RecordField>,
    pub constructor: String,
    pub methods: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum TypeScriptParameterDescriptor {
    Primitive {
        type_name: String,
    },
    ReadonlyArray {
        element_type: String,
    },
    ReadonlyTuple {
        element_types: Vec<String>,
    },
    Record {
        fields: Vec<RecordField>,
    },
    Callback {
        parameter_types: Vec<String>,
        return_type: String,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct TypeScriptParameter {
    pub name: String,
    pub descriptor: TypeScriptParameterDescriptor,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum TypeScriptArgumentDescriptor {
    Primitive {
        type_name: String,
    },
    ReadonlyArray {
        element_type: String,
    },
    ReadonlyTuple {
        element_types: Vec<String>,
    },
    SourceRecord {
        fields: Vec<RecordField>,
    },
    SourceCallback {
        function: String,
        parameter_types: Vec<String>,
        return_type: String,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct TypeScriptSwitchLabel {
    pub type_name: String,
    pub value: serde_json::Value,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TypeScriptSwitchCase {
    pub label: TypeScriptSwitchLabel,
    pub body: TypeScriptOutcomeGraph,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum TypeScriptOutcomeGraph {
    Fallthrough,
    Return {
        type_name: String,
    },
    Raise {
        exception_type: String,
        line: u32,
        column: u32,
    },
    Call {
        callee: String,
        arguments: Vec<TypeScriptArgumentDescriptor>,
        line: u32,
        column: u32,
    },
    AwaitCall {
        callee: String,
        arguments: Vec<TypeScriptArgumentDescriptor>,
        line: u32,
        column: u32,
    },
    PromiseAdopt {
        callee: String,
        arguments: Vec<TypeScriptArgumentDescriptor>,
        line: u32,
        column: u32,
    },
    CallbackInvoke {
        parameter: String,
        arguments: Vec<TypeScriptArgumentDescriptor>,
        line: u32,
        column: u32,
    },
    Sequence {
        items: Vec<TypeScriptOutcomeGraph>,
    },
    Branch {
        branches: Vec<TypeScriptOutcomeGraph>,
    },
    TryCatch {
        try_body: Box<TypeScriptOutcomeGraph>,
        catch_body: Box<TypeScriptOutcomeGraph>,
    },
    TryFinally {
        body: Box<TypeScriptOutcomeGraph>,
        finally_body: Box<TypeScriptOutcomeGraph>,
    },
    TerminalSwitch {
        discriminant: Box<TypeScriptOutcomeGraph>,
        discriminant_type: String,
        cases: Vec<TypeScriptSwitchCase>,
        default_body: Box<TypeScriptOutcomeGraph>,
    },
}

#[derive(Clone, Debug, Deserialize)]
pub struct TypeScriptVerification {
    pub schema: String,
    pub compiler_version: String,
    pub functions: Vec<TypeScriptFunction>,
    pub classes: Vec<TypeScriptClass>,
    pub toolchain: TypeScriptToolchainIdentity,
}

pub fn verified_leaf_interfaces(
    verification: &TypeScriptVerification,
    requested_symbols: &[String],
) -> Vec<VerifiedLeafInterface> {
    requested_symbols
        .iter()
        .filter_map(|symbol| {
            let function = verification
                .functions
                .iter()
                .find(|candidate| candidate.name == *symbol)?;
            if function.execution != TypeScriptExecution::Synchronous
                || !primitive_type_name(&function.return_type)
            {
                return None;
            }
            let parameters = function
                .parameters
                .iter()
                .map(|parameter| match &parameter.descriptor {
                    TypeScriptParameterDescriptor::Primitive { type_name } => {
                        Some(VerifiedLeafParameter {
                            name: parameter.name.clone(),
                            type_name: type_name.clone(),
                        })
                    }
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            Some(VerifiedLeafInterface {
                symbol: symbol.clone(),
                execution: "synchronous".to_owned(),
                parameters,
                return_type: function.return_type.clone(),
            })
        })
        .collect()
}

#[derive(Clone, Debug)]
pub struct TypeScriptFailure {
    pub code: String,
    pub message: String,
    pub line: Option<u32>,
    pub column: Option<u32>,
}

#[derive(Deserialize)]
#[serde(tag = "status", rename_all = "lowercase", deny_unknown_fields)]
enum FrontendResult {
    Proved {
        schema: String,
        compiler_version: String,
        functions: Vec<TypeScriptFunction>,
        classes: Vec<TypeScriptClass>,
    },
    Refused {
        code: String,
        message: String,
        line: Option<u32>,
        column: Option<u32>,
    },
}

pub fn verify_closed_module(
    source_path: &Path,
    requested_symbols: &[String],
) -> Result<TypeScriptVerification, TypeScriptFailure> {
    verify_closed_module_as(source_path, requested_symbols, SourceLanguage::TypeScript)
}

pub fn verify_closed_javascript_module(
    source_path: &Path,
    requested_symbols: &[String],
) -> Result<TypeScriptVerification, TypeScriptFailure> {
    verify_closed_module_as(source_path, requested_symbols, SourceLanguage::JavaScript)
}

fn verify_closed_module_as(
    source_path: &Path,
    requested_symbols: &[String],
    language: SourceLanguage,
) -> Result<TypeScriptVerification, TypeScriptFailure> {
    let extension = source_path
        .extension()
        .and_then(|value| value.to_str())
        .unwrap_or_default()
        .to_ascii_lowercase();
    let extension_matches = match language {
        SourceLanguage::JavaScript => matches!(extension.as_str(), "js" | "mjs" | "cjs"),
        SourceLanguage::TypeScript => matches!(extension.as_str(), "ts" | "mts" | "cts"),
    };
    if !extension_matches {
        return Err(TypeScriptFailure {
            code: language.code("source-extension"),
            message: format!(
                "source path {:?} does not have a {} extension",
                source_path,
                language.name()
            ),
            line: None,
            column: None,
        });
    }
    let compiler =
        resolve_typescript_compiler().map_err(|error| relabel_failure(error, language))?;
    let frontend =
        resolve_typescript_frontend().map_err(|error| relabel_failure(error, language))?;
    let node = resolve_node_executable().map_err(|error| relabel_failure(error, language))?;
    let toolchain =
        toolchain_identity(&node, &compiler).map_err(|error| relabel_failure(error, language))?;
    let symbols = serde_json::to_string(requested_symbols).map_err(|error| TypeScriptFailure {
        code: language.code("request-encoding"),
        message: error.to_string(),
        line: None,
        column: None,
    })?;
    let child = Command::new(&node)
        .arg(frontend)
        .arg(compiler)
        .arg(source_path)
        .arg(symbols)
        .arg(language.name())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| TypeScriptFailure {
            code: language.code("compiler-unavailable"),
            message: format!("cannot start pinned TypeScript compiler frontend: {error}"),
            line: None,
            column: None,
        })?;
    let output = child
        .wait_with_output()
        .map_err(|error| TypeScriptFailure {
            code: language.code("compiler-failed"),
            message: error.to_string(),
            line: None,
            column: None,
        })?;
    if !output.status.success() {
        return Err(TypeScriptFailure {
            code: language.code("compiler-failed"),
            message: String::from_utf8_lossy(&output.stderr).trim().to_owned(),
            line: None,
            column: None,
        });
    }
    let result: FrontendResult =
        serde_json::from_slice(&output.stdout).map_err(|error| TypeScriptFailure {
            code: language.code("compiler-protocol"),
            message: format!("invalid compiler frontend response: {error}"),
            line: None,
            column: None,
        })?;
    match result {
        FrontendResult::Refused {
            code,
            message,
            line,
            column,
        } => Err(TypeScriptFailure {
            code,
            message,
            line,
            column,
        }),
        FrontendResult::Proved {
            schema,
            compiler_version,
            functions,
            classes,
        } => {
            if compiler_version != TYPESCRIPT_VERSION
                || schema != language.schema()
                || functions.is_empty()
            {
                return Err(TypeScriptFailure {
                    code: language.code("compiler-protocol"),
                    message:
                        "compiler frontend returned an unsupported version, schema, or empty proof"
                            .to_owned(),
                    line: None,
                    column: None,
                });
            }
            let effects =
                validate_outcome_graphs(&functions, &classes, requested_symbols, language)?;
            check_exit_effects(&effects, &[]).map_err(|error| TypeScriptFailure {
                code: language.code("kernel-rejected"),
                message: format!("kernel rejected compiler-derived effects: {error:?}"),
                line: None,
                column: None,
            })?;
            Ok(TypeScriptVerification {
                schema,
                compiler_version,
                functions,
                classes,
                toolchain,
            })
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum LocatedExit {
    Fallthrough,
    Return {
        type_name: String,
    },
    Raise {
        exception_type: String,
        line: u32,
        column: u32,
    },
    Fulfill {
        type_name: String,
    },
    Reject {
        exception_type: String,
        line: u32,
        column: u32,
    },
}

fn validate_outcome_graphs(
    functions: &[TypeScriptFunction],
    classes: &[TypeScriptClass],
    requested_symbols: &[String],
    language: SourceLanguage,
) -> Result<Vec<ExitEffect>, TypeScriptFailure> {
    let mut definitions = HashMap::new();
    for function in functions {
        if definitions
            .insert(function.name.as_str(), function)
            .is_some()
        {
            return protocol_failure(language, format!("duplicate function {:?}", function.name));
        }
        let mut parameter_names = HashSet::new();
        if !primitive_type_name(&function.return_type) && function.return_type != "void" {
            return protocol_failure(
                language,
                format!("function {:?} has an invalid return type", function.name),
            );
        }
        for parameter in &function.parameters {
            if parameter.name.is_empty() || !parameter_names.insert(parameter.name.as_str()) {
                return protocol_failure(
                    language,
                    format!(
                        "function {:?} has an invalid or duplicate parameter",
                        function.name
                    ),
                );
            }
            validate_parameter_descriptor(&parameter.descriptor, language)?;
            if function.exported
                && matches!(
                    parameter.descriptor,
                    TypeScriptParameterDescriptor::Record { .. }
                        | TypeScriptParameterDescriptor::Callback { .. }
                )
            {
                return protocol_failure(
                    language,
                    format!(
                        "exported function {:?} has a private-boundary parameter",
                        function.name
                    ),
                );
            }
        }
        let mut graph_calls = Vec::new();
        collect_graph_calls(&function.outcome_graph, &mut graph_calls);
        graph_calls.sort();
        graph_calls.dedup();
        if graph_calls != function.calls {
            return protocol_failure(
                language,
                format!(
                    "function {:?} call summary does not match its outcome graph",
                    function.name
                ),
            );
        }
    }

    let mut class_names = HashSet::new();
    let mut class_members = HashSet::new();
    let mut previous_class = None;
    for class in classes {
        if !canonical_record_field_name(&class.name)
            || previous_class.is_some_and(|previous: &str| previous >= class.name.as_str())
            || !class_names.insert(class.name.as_str())
        {
            return protocol_failure(language, "invalid or duplicate source class".to_owned());
        }
        validate_record_fields(&class.fields, language)?;
        let expected_constructor = format!("{}.constructor", class.name);
        if class.constructor != expected_constructor
            || !class_members.insert(class.constructor.as_str())
        {
            return protocol_failure(
                language,
                "source class has invalid constructor identity".to_owned(),
            );
        }
        let constructor = definitions
            .get(class.constructor.as_str())
            .copied()
            .ok_or_else(|| TypeScriptFailure {
                code: language.code("compiler-protocol"),
                message: format!("source class {:?} omits its constructor graph", class.name),
                line: None,
                column: None,
            })?;
        if constructor.exported
            || constructor.execution != TypeScriptExecution::Synchronous
            || constructor.return_type != "void"
            || constructor.parameters.iter().any(|parameter| {
                !matches!(
                    parameter.descriptor,
                    TypeScriptParameterDescriptor::Primitive { .. }
                )
            })
        {
            return protocol_failure(
                language,
                "source constructor has invalid execution shape".to_owned(),
            );
        }
        let mut previous_method = None;
        for method in &class.methods {
            let prefix = format!("{}.", class.name);
            let Some(member_name) = method.strip_prefix(&prefix) else {
                return protocol_failure(
                    language,
                    "source class method identity has the wrong owner".to_owned(),
                );
            };
            if member_name == "constructor"
                || !canonical_record_field_name(member_name)
                || previous_method.is_some_and(|previous: &str| previous >= method.as_str())
                || !class_members.insert(method.as_str())
            {
                return protocol_failure(
                    language,
                    "source class methods are not canonical".to_owned(),
                );
            }
            let definition =
                definitions
                    .get(method.as_str())
                    .copied()
                    .ok_or_else(|| TypeScriptFailure {
                        code: language.code("compiler-protocol"),
                        message: format!("source class method {method:?} has no outcome graph"),
                        line: None,
                        column: None,
                    })?;
            if definition.exported
                || definition.parameters.iter().any(|parameter| {
                    !matches!(
                        parameter.descriptor,
                        TypeScriptParameterDescriptor::Primitive { .. }
                    )
                })
            {
                return protocol_failure(
                    language,
                    "source class method has an invalid boundary shape".to_owned(),
                );
            }
            previous_method = Some(method.as_str());
        }
        previous_class = Some(class.name.as_str());
    }
    for function in functions {
        let looks_like_member = function.name.contains('.');
        if looks_like_member != class_members.contains(function.name.as_str()) {
            return protocol_failure(
                language,
                format!(
                    "function {:?} has inconsistent source-class ownership",
                    function.name
                ),
            );
        }
    }

    for function in functions {
        validate_graph_shape(function, &definitions, language)?;
    }

    let roots = if requested_symbols.is_empty() {
        functions
            .iter()
            .filter(|function| !class_members.contains(function.name.as_str()))
            .map(|function| function.name.as_str())
            .collect::<Vec<_>>()
    } else {
        requested_symbols.iter().map(String::as_str).collect()
    };
    let mut cache = HashMap::new();
    let mut visiting = HashSet::new();
    let mut effects = Vec::new();
    for root in roots {
        if class_members.contains(root) {
            return protocol_failure(
                language,
                format!("source class member {root:?} cannot be an open verification root"),
            );
        }
        let root_function = definitions.get(root).ok_or_else(|| TypeScriptFailure {
            code: language.code("compiler-protocol"),
            message: format!("outcome graph omitted requested root {root:?}"),
            line: None,
            column: None,
        })?;
        if root_function.parameters.iter().any(|parameter| {
            matches!(
                parameter.descriptor,
                TypeScriptParameterDescriptor::Record { .. }
                    | TypeScriptParameterDescriptor::Callback { .. }
            )
        }) {
            return protocol_failure(
                language,
                format!("requested root {root:?} has a private-boundary parameter"),
            );
        }
        let exits = evaluate_function(
            root,
            &HashMap::new(),
            &definitions,
            &mut cache,
            &mut visiting,
            language,
        )?;
        for exit in &exits {
            match exit {
                LocatedExit::Return { type_name } | LocatedExit::Fulfill { type_name } => effects
                    .push(ExitEffect::Return {
                        type_name: type_name.clone(),
                    }),
                LocatedExit::Raise {
                    exception_type,
                    line,
                    column,
                } => {
                    return Err(TypeScriptFailure {
                        code: language.code("unexpected-exception"),
                        message: format!(
                            "requested function {root:?} has uncaught outcome {exception_type}"
                        ),
                        line: Some(*line),
                        column: Some(*column),
                    });
                }
                LocatedExit::Reject {
                    exception_type,
                    line,
                    column,
                } => {
                    return Err(TypeScriptFailure {
                        code: language.code("unexpected-rejection"),
                        message: format!(
                            "requested async function {root:?} has rejected outcome {exception_type}"
                        ),
                        line: Some(*line),
                        column: Some(*column),
                    });
                }
                LocatedExit::Fallthrough => {
                    return protocol_failure(
                        language,
                        format!("requested function {root:?} retained an unnormalized fallthrough"),
                    );
                }
            }
        }
    }
    Ok(effects)
}

fn primitive_type_name(type_name: &str) -> bool {
    matches!(type_name, "number" | "boolean" | "string")
}

fn canonical_record_field_name(name: &str) -> bool {
    if name == "__proto__" {
        return false;
    }
    let mut bytes = name.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    if !(first == b'$' || first == b'_' || first.is_ascii_alphabetic()) {
        return false;
    }
    bytes.all(|byte| byte == b'$' || byte == b'_' || byte.is_ascii_alphanumeric())
}

fn validate_record_fields(
    fields: &[RecordField],
    language: SourceLanguage,
) -> Result<(), TypeScriptFailure> {
    if fields.is_empty() {
        return protocol_failure(language, "sealed record has no fields".to_owned());
    }
    let mut previous = None;
    for field in fields {
        if !canonical_record_field_name(&field.name)
            || !primitive_type_name(&field.type_name)
            || previous.is_some_and(|name: &str| name >= field.name.as_str())
        {
            return protocol_failure(
                language,
                "sealed record fields are not canonical".to_owned(),
            );
        }
        previous = Some(field.name.as_str());
    }
    Ok(())
}

fn validate_parameter_descriptor(
    descriptor: &TypeScriptParameterDescriptor,
    language: SourceLanguage,
) -> Result<(), TypeScriptFailure> {
    match descriptor {
        TypeScriptParameterDescriptor::Primitive { type_name } => {
            if !primitive_type_name(type_name) {
                return protocol_failure(language, "invalid primitive parameter type".to_owned());
            }
        }
        TypeScriptParameterDescriptor::ReadonlyArray { element_type } => {
            if !primitive_type_name(element_type) {
                return protocol_failure(
                    language,
                    "invalid readonly-array element type".to_owned(),
                );
            }
        }
        TypeScriptParameterDescriptor::ReadonlyTuple { element_types } => {
            if element_types.iter().any(|item| !primitive_type_name(item)) {
                return protocol_failure(
                    language,
                    "invalid readonly-tuple element type".to_owned(),
                );
            }
        }
        TypeScriptParameterDescriptor::Record { fields } => {
            validate_record_fields(fields, language)?;
        }
        TypeScriptParameterDescriptor::Callback {
            parameter_types,
            return_type,
        } => {
            if parameter_types
                .iter()
                .any(|item| !primitive_type_name(item))
                || (!primitive_type_name(return_type) && return_type != "void")
            {
                return protocol_failure(language, "invalid callback signature".to_owned());
            }
        }
    }
    Ok(())
}

fn argument_matches_parameter(
    argument: &TypeScriptArgumentDescriptor,
    parameter: &TypeScriptParameterDescriptor,
    language: SourceLanguage,
) -> Result<bool, TypeScriptFailure> {
    match argument {
        TypeScriptArgumentDescriptor::SourceRecord { fields } => {
            validate_record_fields(fields, language)?;
        }
        TypeScriptArgumentDescriptor::Primitive { type_name } => {
            if !primitive_type_name(type_name) {
                return protocol_failure(language, "invalid primitive call argument".to_owned());
            }
        }
        TypeScriptArgumentDescriptor::ReadonlyArray { element_type } => {
            if !primitive_type_name(element_type) {
                return protocol_failure(
                    language,
                    "invalid readonly-array call argument".to_owned(),
                );
            }
        }
        TypeScriptArgumentDescriptor::ReadonlyTuple { element_types } => {
            if element_types.iter().any(|item| !primitive_type_name(item)) {
                return protocol_failure(
                    language,
                    "invalid readonly-tuple call argument".to_owned(),
                );
            }
        }
        TypeScriptArgumentDescriptor::SourceCallback {
            function,
            parameter_types,
            return_type,
        } => {
            if function.is_empty()
                || parameter_types
                    .iter()
                    .any(|item| !primitive_type_name(item))
                || (!primitive_type_name(return_type) && return_type != "void")
            {
                return protocol_failure(language, "invalid source callback argument".to_owned());
            }
        }
    }
    Ok(match (parameter, argument) {
        (
            TypeScriptParameterDescriptor::Primitive {
                type_name: expected,
            },
            TypeScriptArgumentDescriptor::Primitive { type_name: actual },
        ) => expected == actual,
        (
            TypeScriptParameterDescriptor::ReadonlyArray {
                element_type: expected,
            },
            TypeScriptArgumentDescriptor::ReadonlyArray {
                element_type: actual,
            },
        ) => expected == actual,
        (
            TypeScriptParameterDescriptor::ReadonlyTuple {
                element_types: expected,
            },
            TypeScriptArgumentDescriptor::ReadonlyTuple {
                element_types: actual,
            },
        ) => expected == actual,
        (
            TypeScriptParameterDescriptor::Record { fields: expected },
            TypeScriptArgumentDescriptor::SourceRecord { fields: actual },
        ) => expected == actual,
        (
            TypeScriptParameterDescriptor::Callback {
                parameter_types: expected_parameters,
                return_type: expected_return,
            },
            TypeScriptArgumentDescriptor::SourceCallback {
                parameter_types: actual_parameters,
                return_type: actual_return,
                ..
            },
        ) => expected_parameters == actual_parameters && expected_return == actual_return,
        _ => false,
    })
}

fn collect_graph_calls(graph: &TypeScriptOutcomeGraph, calls: &mut Vec<String>) {
    match graph {
        TypeScriptOutcomeGraph::Call {
            callee, arguments, ..
        }
        | TypeScriptOutcomeGraph::AwaitCall {
            callee, arguments, ..
        }
        | TypeScriptOutcomeGraph::PromiseAdopt {
            callee, arguments, ..
        } => {
            calls.push(callee.clone());
            for argument in arguments {
                if let TypeScriptArgumentDescriptor::SourceCallback { function, .. } = argument {
                    calls.push(function.clone());
                }
            }
        }
        TypeScriptOutcomeGraph::Sequence { items } => {
            for item in items {
                collect_graph_calls(item, calls);
            }
        }
        TypeScriptOutcomeGraph::Branch { branches } => {
            for branch in branches {
                collect_graph_calls(branch, calls);
            }
        }
        TypeScriptOutcomeGraph::TryCatch {
            try_body,
            catch_body,
        } => {
            collect_graph_calls(try_body, calls);
            collect_graph_calls(catch_body, calls);
        }
        TypeScriptOutcomeGraph::TryFinally { body, finally_body } => {
            collect_graph_calls(body, calls);
            collect_graph_calls(finally_body, calls);
        }
        TypeScriptOutcomeGraph::TerminalSwitch {
            discriminant,
            cases,
            default_body,
            ..
        } => {
            collect_graph_calls(discriminant, calls);
            for case in cases {
                collect_graph_calls(&case.body, calls);
            }
            collect_graph_calls(default_body, calls);
        }
        TypeScriptOutcomeGraph::Fallthrough
        | TypeScriptOutcomeGraph::Return { .. }
        | TypeScriptOutcomeGraph::Raise { .. }
        | TypeScriptOutcomeGraph::CallbackInvoke { .. } => {}
    }
}

fn validate_source_callback(
    function: &str,
    argument: &TypeScriptArgumentDescriptor,
    definitions: &HashMap<&str, &TypeScriptFunction>,
    language: SourceLanguage,
) -> Result<(), TypeScriptFailure> {
    let TypeScriptArgumentDescriptor::SourceCallback {
        function: recorded_function,
        parameter_types,
        return_type,
    } = argument
    else {
        return protocol_failure(
            language,
            "callback formal lacks source provenance".to_owned(),
        );
    };
    if function != recorded_function {
        return protocol_failure(
            language,
            "source callback identity is inconsistent".to_owned(),
        );
    }
    let definition = definitions
        .get(function)
        .copied()
        .ok_or_else(|| TypeScriptFailure {
            code: language.code("compiler-protocol"),
            message: format!("source callback names unknown function {function:?}"),
            line: None,
            column: None,
        })?;
    if definition.parameters.len() != parameter_types.len()
        || definition.execution != TypeScriptExecution::Synchronous
        || definition
            .parameters
            .iter()
            .zip(parameter_types)
            .any(|(parameter, expected)| {
                !matches!(
                    &parameter.descriptor,
                    TypeScriptParameterDescriptor::Primitive { type_name }
                        if type_name == expected
                )
            })
        || definition.return_type != *return_type
    {
        return protocol_failure(
            language,
            format!("source callback {function:?} signature does not match its descriptor"),
        );
    }
    Ok(())
}

fn validate_graph_shape(
    function: &TypeScriptFunction,
    definitions: &HashMap<&str, &TypeScriptFunction>,
    language: SourceLanguage,
) -> Result<(), TypeScriptFailure> {
    fn validate_call<'a>(
        callee: &str,
        arguments: &[TypeScriptArgumentDescriptor],
        definitions: &'a HashMap<&str, &TypeScriptFunction>,
        language: SourceLanguage,
    ) -> Result<&'a TypeScriptFunction, TypeScriptFailure> {
        let callee_definition =
            definitions
                .get(callee)
                .copied()
                .ok_or_else(|| TypeScriptFailure {
                    code: language.code("compiler-protocol"),
                    message: format!("outcome graph calls unknown function {callee:?}"),
                    line: None,
                    column: None,
                })?;
        if arguments.len() != callee_definition.parameters.len() {
            return protocol_failure(
                language,
                format!("call to {callee:?} has the wrong argument count"),
            );
        }
        for (argument, parameter) in arguments.iter().zip(&callee_definition.parameters) {
            if !argument_matches_parameter(argument, &parameter.descriptor, language)? {
                return protocol_failure(
                    language,
                    format!("call to {callee:?} has incompatible typed arguments"),
                );
            }
            if let TypeScriptArgumentDescriptor::SourceCallback {
                function: callback, ..
            } = argument
            {
                validate_source_callback(callback, argument, definitions, language)?;
            }
        }
        Ok(callee_definition)
    }

    fn visit(
        graph: &TypeScriptOutcomeGraph,
        function: &TypeScriptFunction,
        definitions: &HashMap<&str, &TypeScriptFunction>,
        language: SourceLanguage,
    ) -> Result<(), TypeScriptFailure> {
        match graph {
            TypeScriptOutcomeGraph::Call {
                callee, arguments, ..
            } => {
                let callee_definition = validate_call(callee, arguments, definitions, language)?;
                if callee_definition.execution != TypeScriptExecution::Synchronous {
                    return protocol_failure(
                        language,
                        format!("ordinary call node targets async function {callee:?}"),
                    );
                }
            }
            TypeScriptOutcomeGraph::AwaitCall {
                callee, arguments, ..
            } => {
                validate_call(callee, arguments, definitions, language)?;
                if function.execution != TypeScriptExecution::Asynchronous {
                    return protocol_failure(
                        language,
                        format!("synchronous function {:?} contains await", function.name),
                    );
                }
            }
            TypeScriptOutcomeGraph::PromiseAdopt {
                callee, arguments, ..
            } => {
                let callee_definition = validate_call(callee, arguments, definitions, language)?;
                if function.execution != TypeScriptExecution::Asynchronous
                    || callee_definition.execution != TypeScriptExecution::Asynchronous
                {
                    return protocol_failure(
                        language,
                        "promise adoption requires async caller and async callee".to_owned(),
                    );
                }
                if function.return_type != callee_definition.return_type {
                    return protocol_failure(
                        language,
                        format!(
                            "promise adoption from {callee:?} has incompatible fulfillment type"
                        ),
                    );
                }
                if matches!(function.return_type.as_str(), "void") {
                    // Promise<void> adoption is valid and deliberately explicit here.
                } else if !primitive_type_name(&function.return_type) {
                    return protocol_failure(
                        language,
                        "promise adoption has invalid fulfillment type".to_owned(),
                    );
                }
            }
            TypeScriptOutcomeGraph::CallbackInvoke {
                parameter,
                arguments,
                line,
                column,
            } => {
                if *line == 0 || *column == 0 {
                    return protocol_failure(
                        language,
                        "callback invocation has invalid location".to_owned(),
                    );
                }
                let descriptor = function
                    .parameters
                    .iter()
                    .find(|item| item.name == *parameter)
                    .map(|item| &item.descriptor);
                let Some(TypeScriptParameterDescriptor::Callback {
                    parameter_types, ..
                }) = descriptor
                else {
                    return protocol_failure(
                        language,
                        format!("callback invocation names non-callback parameter {parameter:?}"),
                    );
                };
                if arguments.len() != parameter_types.len()
                    || arguments
                        .iter()
                        .zip(parameter_types)
                        .any(|(argument, expected)| {
                            !matches!(argument,
                            TypeScriptArgumentDescriptor::Primitive { type_name }
                                if type_name == expected)
                        })
                {
                    return protocol_failure(
                        language,
                        format!("callback invocation {parameter:?} has incompatible arguments"),
                    );
                }
            }
            TypeScriptOutcomeGraph::Sequence { items } => {
                for item in items {
                    visit(item, function, definitions, language)?;
                }
            }
            TypeScriptOutcomeGraph::Branch { branches } => {
                for branch in branches {
                    visit(branch, function, definitions, language)?;
                }
            }
            TypeScriptOutcomeGraph::TryCatch {
                try_body,
                catch_body,
            } => {
                visit(try_body, function, definitions, language)?;
                visit(catch_body, function, definitions, language)?;
            }
            TypeScriptOutcomeGraph::TryFinally { body, finally_body } => {
                visit(body, function, definitions, language)?;
                visit(finally_body, function, definitions, language)?;
            }
            TypeScriptOutcomeGraph::TerminalSwitch {
                discriminant,
                cases,
                default_body,
                ..
            } => {
                visit(discriminant, function, definitions, language)?;
                for case in cases {
                    visit(&case.body, function, definitions, language)?;
                }
                visit(default_body, function, definitions, language)?;
            }
            TypeScriptOutcomeGraph::Fallthrough
            | TypeScriptOutcomeGraph::Return { .. }
            | TypeScriptOutcomeGraph::Raise { .. } => {}
        }
        Ok(())
    }

    visit(&function.outcome_graph, function, definitions, language)
}

type CallbackBindings = HashMap<String, String>;
type EvaluationKey = (String, Vec<(String, String)>);

fn evaluation_key(name: &str, callback_bindings: &CallbackBindings) -> EvaluationKey {
    let mut bindings = callback_bindings
        .iter()
        .map(|(parameter, function)| (parameter.clone(), function.clone()))
        .collect::<Vec<_>>();
    bindings.sort();
    (name.to_owned(), bindings)
}

fn evaluate_function(
    name: &str,
    callback_bindings: &CallbackBindings,
    definitions: &HashMap<&str, &TypeScriptFunction>,
    cache: &mut HashMap<EvaluationKey, Vec<LocatedExit>>,
    visiting: &mut HashSet<EvaluationKey>,
    language: SourceLanguage,
) -> Result<Vec<LocatedExit>, TypeScriptFailure> {
    let key = evaluation_key(name, callback_bindings);
    if let Some(cached) = cache.get(&key) {
        return Ok(cached.clone());
    }
    if !visiting.insert(key.clone()) {
        return protocol_failure(
            language,
            format!("outcome graph contains call cycle at {name:?}"),
        );
    }
    let function = definitions
        .get(name)
        .copied()
        .ok_or_else(|| TypeScriptFailure {
            code: language.code("compiler-protocol"),
            message: format!("outcome graph calls unknown function {name:?}"),
            line: None,
            column: None,
        })?;
    let expected_callback_parameters = function
        .parameters
        .iter()
        .filter(|parameter| {
            matches!(
                parameter.descriptor,
                TypeScriptParameterDescriptor::Callback { .. }
            )
        })
        .map(|parameter| parameter.name.as_str())
        .collect::<HashSet<_>>();
    if callback_bindings.len() != expected_callback_parameters.len()
        || callback_bindings
            .keys()
            .any(|parameter| !expected_callback_parameters.contains(parameter.as_str()))
    {
        return protocol_failure(
            language,
            format!("function {name:?} has incomplete callback provenance"),
        );
    }
    let raw = evaluate_graph(
        &function.outcome_graph,
        function,
        callback_bindings,
        definitions,
        cache,
        visiting,
        language,
    )?;
    visiting.remove(&key);
    let mut normalized = Vec::new();
    for exit in raw {
        let exit = match exit {
            LocatedExit::Fallthrough if function.return_type == "void" => LocatedExit::Return {
                type_name: "void".to_owned(),
            },
            LocatedExit::Fallthrough => {
                return protocol_failure(
                    language,
                    format!("non-void function {name:?} can fall through its outcome graph"),
                );
            }
            LocatedExit::Return { type_name } if type_name != function.return_type => {
                return protocol_failure(
                    language,
                    format!(
                        "function {name:?} returns graph type {type_name:?}, expected {:?}",
                        function.return_type
                    ),
                );
            }
            other => other,
        };
        let exit = match (function.execution, exit) {
            (TypeScriptExecution::Asynchronous, LocatedExit::Return { type_name }) => {
                LocatedExit::Fulfill { type_name }
            }
            (
                TypeScriptExecution::Asynchronous,
                LocatedExit::Raise {
                    exception_type,
                    line,
                    column,
                },
            ) => LocatedExit::Reject {
                exception_type,
                line,
                column,
            },
            (TypeScriptExecution::Asynchronous, exit @ LocatedExit::Reject { .. }) => exit,
            (TypeScriptExecution::Synchronous, LocatedExit::Fulfill { .. })
            | (TypeScriptExecution::Synchronous, LocatedExit::Reject { .. })
            | (TypeScriptExecution::Asynchronous, LocatedExit::Fallthrough) => {
                return protocol_failure(
                    language,
                    format!("function {name:?} has an invalid async boundary outcome"),
                );
            }
            (_, exit) => exit,
        };
        push_unique(&mut normalized, exit);
    }
    if normalized.is_empty() {
        return protocol_failure(
            language,
            format!("function {name:?} has no boundary outcomes"),
        );
    }
    cache.insert(key, normalized.clone());
    Ok(normalized)
}

fn callback_bindings_for_call(
    callee: &str,
    arguments: &[TypeScriptArgumentDescriptor],
    callee_definition: &TypeScriptFunction,
    definitions: &HashMap<&str, &TypeScriptFunction>,
    language: SourceLanguage,
) -> Result<CallbackBindings, TypeScriptFailure> {
    if arguments.len() != callee_definition.parameters.len() {
        return protocol_failure(
            language,
            format!("call to {callee:?} has the wrong argument count"),
        );
    }
    let mut bindings = HashMap::new();
    for (argument, parameter) in arguments.iter().zip(&callee_definition.parameters) {
        if !argument_matches_parameter(argument, &parameter.descriptor, language)? {
            return protocol_failure(
                language,
                format!("call to {callee:?} has incompatible typed arguments"),
            );
        }
        if let (
            TypeScriptParameterDescriptor::Callback { .. },
            TypeScriptArgumentDescriptor::SourceCallback { function, .. },
        ) = (&parameter.descriptor, argument)
        {
            validate_source_callback(function, argument, definitions, language)?;
            bindings.insert(parameter.name.clone(), function.clone());
        }
    }
    Ok(bindings)
}

fn evaluate_graph(
    graph: &TypeScriptOutcomeGraph,
    current_function: &TypeScriptFunction,
    callback_bindings: &CallbackBindings,
    definitions: &HashMap<&str, &TypeScriptFunction>,
    cache: &mut HashMap<EvaluationKey, Vec<LocatedExit>>,
    visiting: &mut HashSet<EvaluationKey>,
    language: SourceLanguage,
) -> Result<Vec<LocatedExit>, TypeScriptFailure> {
    match graph {
        TypeScriptOutcomeGraph::Fallthrough => Ok(vec![LocatedExit::Fallthrough]),
        TypeScriptOutcomeGraph::Return { type_name } => Ok(vec![LocatedExit::Return {
            type_name: type_name.clone(),
        }]),
        TypeScriptOutcomeGraph::Raise {
            exception_type,
            line,
            column,
        } => {
            if !matches!(
                exception_type.as_str(),
                "ecmascript.throw.number" | "ecmascript.throw.boolean" | "ecmascript.throw.string"
            ) || *line == 0
                || *column == 0
            {
                return protocol_failure(language, "invalid typed raise outcome".to_owned());
            }
            Ok(vec![LocatedExit::Raise {
                exception_type: exception_type.clone(),
                line: *line,
                column: *column,
            }])
        }
        TypeScriptOutcomeGraph::Call {
            callee,
            arguments,
            line,
            column,
        } => {
            if *line == 0 || *column == 0 {
                return protocol_failure(language, "source call has invalid location".to_owned());
            }
            let callee_definition =
                definitions
                    .get(callee.as_str())
                    .ok_or_else(|| TypeScriptFailure {
                        code: language.code("compiler-protocol"),
                        message: format!("outcome graph calls unknown function {callee:?}"),
                        line: None,
                        column: None,
                    })?;
            if arguments.len() != callee_definition.parameters.len() {
                return protocol_failure(
                    language,
                    format!("call to {callee:?} has the wrong argument count"),
                );
            }
            let mut callee_callback_bindings = HashMap::new();
            for (argument, parameter) in arguments.iter().zip(&callee_definition.parameters) {
                if !argument_matches_parameter(argument, &parameter.descriptor, language)? {
                    return protocol_failure(
                        language,
                        format!("call to {callee:?} has incompatible typed arguments"),
                    );
                }
                if let (
                    TypeScriptParameterDescriptor::Callback { .. },
                    TypeScriptArgumentDescriptor::SourceCallback { function, .. },
                ) = (&parameter.descriptor, argument)
                {
                    validate_source_callback(function, argument, definitions, language)?;
                    callee_callback_bindings.insert(parameter.name.clone(), function.clone());
                }
            }
            let callee_exits = evaluate_function(
                callee,
                &callee_callback_bindings,
                definitions,
                cache,
                visiting,
                language,
            )?;
            let mut exits = Vec::new();
            for exit in callee_exits {
                let exit = match exit {
                    LocatedExit::Return { .. } | LocatedExit::Fallthrough => {
                        LocatedExit::Fallthrough
                    }
                    LocatedExit::Raise { exception_type, .. } => LocatedExit::Raise {
                        exception_type,
                        line: *line,
                        column: *column,
                    },
                    LocatedExit::Fulfill { .. } | LocatedExit::Reject { .. } => {
                        return protocol_failure(
                            language,
                            format!("ordinary call unexpectedly evaluated async callee {callee:?}"),
                        );
                    }
                };
                push_unique(&mut exits, exit);
            }
            Ok(exits)
        }
        TypeScriptOutcomeGraph::AwaitCall {
            callee,
            arguments,
            line,
            column,
        } => {
            if *line == 0 || *column == 0 {
                return protocol_failure(language, "await call has invalid location".to_owned());
            }
            if current_function.execution != TypeScriptExecution::Asynchronous {
                return protocol_failure(
                    language,
                    "await call appears in sync function".to_owned(),
                );
            }
            let callee_definition =
                definitions
                    .get(callee.as_str())
                    .copied()
                    .ok_or_else(|| TypeScriptFailure {
                        code: language.code("compiler-protocol"),
                        message: format!("await calls unknown function {callee:?}"),
                        line: None,
                        column: None,
                    })?;
            let callee_bindings = callback_bindings_for_call(
                callee,
                arguments,
                callee_definition,
                definitions,
                language,
            )?;
            let callee_exits = evaluate_function(
                callee,
                &callee_bindings,
                definitions,
                cache,
                visiting,
                language,
            )?;
            let mut exits = Vec::new();
            for exit in callee_exits {
                let exit = match exit {
                    LocatedExit::Return { .. } | LocatedExit::Fulfill { .. } => {
                        LocatedExit::Fallthrough
                    }
                    LocatedExit::Raise { exception_type, .. }
                    | LocatedExit::Reject { exception_type, .. } => LocatedExit::Raise {
                        exception_type,
                        line: *line,
                        column: *column,
                    },
                    LocatedExit::Fallthrough => {
                        return protocol_failure(
                            language,
                            format!("awaited function {callee:?} retained fallthrough"),
                        );
                    }
                };
                push_unique(&mut exits, exit);
            }
            Ok(exits)
        }
        TypeScriptOutcomeGraph::PromiseAdopt {
            callee,
            arguments,
            line,
            column,
        } => {
            if *line == 0 || *column == 0 {
                return protocol_failure(
                    language,
                    "promise adoption has invalid location".to_owned(),
                );
            }
            let callee_definition =
                definitions
                    .get(callee.as_str())
                    .copied()
                    .ok_or_else(|| TypeScriptFailure {
                        code: language.code("compiler-protocol"),
                        message: format!("promise adoption calls unknown function {callee:?}"),
                        line: None,
                        column: None,
                    })?;
            if current_function.execution != TypeScriptExecution::Asynchronous
                || callee_definition.execution != TypeScriptExecution::Asynchronous
                || current_function.return_type != callee_definition.return_type
            {
                return protocol_failure(
                    language,
                    "invalid promise-adoption execution or fulfillment types".to_owned(),
                );
            }
            let callee_bindings = callback_bindings_for_call(
                callee,
                arguments,
                callee_definition,
                definitions,
                language,
            )?;
            let callee_exits = evaluate_function(
                callee,
                &callee_bindings,
                definitions,
                cache,
                visiting,
                language,
            )?;
            let mut exits = Vec::new();
            for exit in callee_exits {
                let exit = match exit {
                    LocatedExit::Fulfill { type_name } => LocatedExit::Return { type_name },
                    LocatedExit::Reject { exception_type, .. } => LocatedExit::Reject {
                        exception_type,
                        line: *line,
                        column: *column,
                    },
                    _ => {
                        return protocol_failure(
                            language,
                            format!("promise adoption evaluated non-async callee {callee:?}"),
                        );
                    }
                };
                push_unique(&mut exits, exit);
            }
            Ok(exits)
        }
        TypeScriptOutcomeGraph::CallbackInvoke {
            parameter,
            arguments,
            line,
            column,
        } => {
            if *line == 0 || *column == 0 {
                return protocol_failure(
                    language,
                    "callback invocation has invalid location".to_owned(),
                );
            }
            let descriptor = current_function
                .parameters
                .iter()
                .find(|item| item.name == *parameter)
                .map(|item| &item.descriptor);
            let Some(TypeScriptParameterDescriptor::Callback {
                parameter_types,
                return_type,
            }) = descriptor
            else {
                return protocol_failure(
                    language,
                    format!("callback invocation names non-callback parameter {parameter:?}"),
                );
            };
            if arguments.len() != parameter_types.len() {
                return protocol_failure(
                    language,
                    format!("callback invocation {parameter:?} has the wrong argument count"),
                );
            }
            for (argument, expected) in arguments.iter().zip(parameter_types) {
                if !matches!(argument,
                    TypeScriptArgumentDescriptor::Primitive { type_name } if type_name == expected)
                {
                    return protocol_failure(
                        language,
                        format!("callback invocation {parameter:?} has incompatible arguments"),
                    );
                }
            }
            let callback = callback_bindings
                .get(parameter)
                .ok_or_else(|| TypeScriptFailure {
                    code: language.code("compiler-protocol"),
                    message: format!("callback invocation {parameter:?} has no source provenance"),
                    line: None,
                    column: None,
                })?;
            let callback_definition =
                definitions
                    .get(callback.as_str())
                    .copied()
                    .ok_or_else(|| TypeScriptFailure {
                        code: language.code("compiler-protocol"),
                        message: format!("callback invocation calls unknown function {callback:?}"),
                        line: None,
                        column: None,
                    })?;
            if callback_definition.return_type != *return_type {
                return protocol_failure(
                    language,
                    format!("callback {callback:?} return type differs from its formal"),
                );
            }
            let callback_exits = evaluate_function(
                callback,
                &HashMap::new(),
                definitions,
                cache,
                visiting,
                language,
            )?;
            let mut exits = Vec::new();
            for exit in callback_exits {
                let exit = match exit {
                    LocatedExit::Return { .. } | LocatedExit::Fallthrough => {
                        LocatedExit::Fallthrough
                    }
                    LocatedExit::Raise { exception_type, .. } => LocatedExit::Raise {
                        exception_type,
                        line: *line,
                        column: *column,
                    },
                    LocatedExit::Fulfill { .. } | LocatedExit::Reject { .. } => {
                        return protocol_failure(
                            language,
                            format!("callback {callback:?} unexpectedly evaluated as async"),
                        );
                    }
                };
                push_unique(&mut exits, exit);
            }
            Ok(exits)
        }
        TypeScriptOutcomeGraph::Sequence { items } => {
            let mut exits = vec![LocatedExit::Fallthrough];
            for item in items {
                let item_exits = evaluate_graph(
                    item,
                    current_function,
                    callback_bindings,
                    definitions,
                    cache,
                    visiting,
                    language,
                )?;
                let mut next = Vec::new();
                for exit in exits {
                    if exit == LocatedExit::Fallthrough {
                        for item_exit in &item_exits {
                            push_unique(&mut next, item_exit.clone());
                        }
                    } else {
                        push_unique(&mut next, exit);
                    }
                }
                exits = next;
            }
            Ok(exits)
        }
        TypeScriptOutcomeGraph::Branch { branches } => {
            if branches.is_empty() {
                return protocol_failure(language, "outcome branch is empty".to_owned());
            }
            let mut exits = Vec::new();
            for branch in branches {
                for exit in evaluate_graph(
                    branch,
                    current_function,
                    callback_bindings,
                    definitions,
                    cache,
                    visiting,
                    language,
                )? {
                    push_unique(&mut exits, exit);
                }
            }
            Ok(exits)
        }
        TypeScriptOutcomeGraph::TryCatch {
            try_body,
            catch_body,
        } => {
            let try_exits = evaluate_graph(
                try_body,
                current_function,
                callback_bindings,
                definitions,
                cache,
                visiting,
                language,
            )?;
            let catch_exits = evaluate_graph(
                catch_body,
                current_function,
                callback_bindings,
                definitions,
                cache,
                visiting,
                language,
            )?;
            let mut exits = Vec::new();
            for exit in try_exits {
                if matches!(exit, LocatedExit::Raise { .. }) {
                    for catch_exit in &catch_exits {
                        push_unique(&mut exits, catch_exit.clone());
                    }
                } else {
                    push_unique(&mut exits, exit);
                }
            }
            Ok(exits)
        }
        TypeScriptOutcomeGraph::TryFinally { body, finally_body } => {
            let body_exits = evaluate_graph(
                body,
                current_function,
                callback_bindings,
                definitions,
                cache,
                visiting,
                language,
            )?;
            let finally_exits = evaluate_graph(
                finally_body,
                current_function,
                callback_bindings,
                definitions,
                cache,
                visiting,
                language,
            )?;
            let mut exits = Vec::new();
            for body_exit in body_exits {
                for finally_exit in &finally_exits {
                    match finally_exit {
                        LocatedExit::Fallthrough => push_unique(&mut exits, body_exit.clone()),
                        LocatedExit::Return { .. }
                        | LocatedExit::Raise { .. }
                        | LocatedExit::Fulfill { .. }
                        | LocatedExit::Reject { .. } => {
                            push_unique(&mut exits, finally_exit.clone());
                        }
                    }
                }
            }
            Ok(exits)
        }
        TypeScriptOutcomeGraph::TerminalSwitch {
            discriminant,
            discriminant_type,
            cases,
            default_body,
        } => {
            if !primitive_type_name(discriminant_type) || cases.is_empty() {
                return protocol_failure(
                    language,
                    "terminal switch has an invalid discriminant or no cases".to_owned(),
                );
            }
            let mut labels = HashSet::new();
            let mut arm_exits = Vec::new();
            for case in cases {
                let key = switch_label_key(&case.label, discriminant_type, language)?;
                if !labels.insert(key) {
                    return protocol_failure(
                        language,
                        "terminal switch contains a duplicate case label".to_owned(),
                    );
                }
                let exits = evaluate_graph(
                    &case.body,
                    current_function,
                    callback_bindings,
                    definitions,
                    cache,
                    visiting,
                    language,
                )?;
                if exits.contains(&LocatedExit::Fallthrough) {
                    return protocol_failure(
                        language,
                        "terminal switch case can fall through".to_owned(),
                    );
                }
                for exit in exits {
                    push_unique(&mut arm_exits, exit);
                }
            }
            let default_exits = evaluate_graph(
                default_body,
                current_function,
                callback_bindings,
                definitions,
                cache,
                visiting,
                language,
            )?;
            if default_exits.contains(&LocatedExit::Fallthrough) {
                return protocol_failure(
                    language,
                    "terminal switch default can fall through".to_owned(),
                );
            }
            for exit in default_exits {
                push_unique(&mut arm_exits, exit);
            }
            let discriminant_exits = evaluate_graph(
                discriminant,
                current_function,
                callback_bindings,
                definitions,
                cache,
                visiting,
                language,
            )?;
            if discriminant_exits.iter().any(|exit| {
                matches!(
                    exit,
                    LocatedExit::Return { .. } | LocatedExit::Fulfill { .. }
                )
            }) {
                return protocol_failure(
                    language,
                    "terminal switch discriminant contains a return outcome".to_owned(),
                );
            }
            let mut exits = Vec::new();
            for exit in discriminant_exits {
                if exit == LocatedExit::Fallthrough {
                    for arm_exit in &arm_exits {
                        push_unique(&mut exits, arm_exit.clone());
                    }
                } else {
                    push_unique(&mut exits, exit);
                }
            }
            Ok(exits)
        }
    }
}

fn switch_label_key(
    label: &TypeScriptSwitchLabel,
    discriminant_type: &str,
    language: SourceLanguage,
) -> Result<String, TypeScriptFailure> {
    if label.type_name != discriminant_type {
        return protocol_failure(
            language,
            "terminal switch case type does not match its discriminant".to_owned(),
        );
    }
    let key = match discriminant_type {
        "string" => label
            .value
            .as_str()
            .map(|value| format!("string:{value:?}")),
        "boolean" => label
            .value
            .as_bool()
            .map(|value| format!("boolean:{value}")),
        "number" => label
            .value
            .as_f64()
            .filter(|value| value.is_finite())
            .map(|value| {
                let canonical = if value == 0.0 { 0.0 } else { value };
                format!("number:{:016x}", canonical.to_bits())
            }),
        _ => None,
    };
    key.ok_or_else(|| TypeScriptFailure {
        code: language.code("compiler-protocol"),
        message: "terminal switch case label is not a matching primitive JSON value".to_owned(),
        line: None,
        column: None,
    })
}

fn push_unique(exits: &mut Vec<LocatedExit>, exit: LocatedExit) {
    if !exits.contains(&exit) {
        exits.push(exit);
    }
}

fn protocol_failure<T>(language: SourceLanguage, message: String) -> Result<T, TypeScriptFailure> {
    Err(TypeScriptFailure {
        code: language.code("compiler-protocol"),
        message,
        line: None,
        column: None,
    })
}

fn relabel_failure(mut failure: TypeScriptFailure, language: SourceLanguage) -> TypeScriptFailure {
    if let Some(suffix) = failure.code.strip_prefix("frontend.typescript.") {
        failure.code = language.code(suffix);
    }
    failure
}

fn resolve_node_executable() -> Result<PathBuf, TypeScriptFailure> {
    if let Some(path) = std::env::var_os("MALEDICTUS_NODE") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return Ok(path);
        }
    }
    let executable_name = if cfg!(windows) { "node.exe" } else { "node" };
    for directory in std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()) {
        let candidate = directory.join(executable_name);
        if candidate.is_file() {
            return Ok(candidate);
        }
    }
    Err(TypeScriptFailure {
        code: "frontend.typescript.runtime-unavailable".to_owned(),
        message: "Node.js runtime was not found on PATH; set MALEDICTUS_NODE explicitly".to_owned(),
        line: None,
        column: None,
    })
}

fn toolchain_identity(
    node: &Path,
    compiler: &Path,
) -> Result<TypeScriptToolchainIdentity, TypeScriptFailure> {
    let package_root =
        compiler
            .parent()
            .and_then(Path::parent)
            .ok_or_else(|| TypeScriptFailure {
                code: "frontend.typescript.compiler-layout".to_owned(),
                message: format!(
                    "compiler path {:?} is not inside a TypeScript package",
                    compiler
                ),
                line: None,
                column: None,
            })?;
    let compiler_bundle_sha256 = hash_directory(package_root)?;
    let runtime_executable_sha256 = hash_file(node)?;
    let version_output = Command::new(node)
        .arg("--version")
        .output()
        .map_err(|error| TypeScriptFailure {
            code: "frontend.typescript.runtime-unavailable".to_owned(),
            message: error.to_string(),
            line: None,
            column: None,
        })?;
    if !version_output.status.success() {
        return Err(TypeScriptFailure {
            code: "frontend.typescript.runtime-unavailable".to_owned(),
            message: String::from_utf8_lossy(&version_output.stderr)
                .trim()
                .to_owned(),
            line: None,
            column: None,
        });
    }
    Ok(TypeScriptToolchainIdentity {
        compiler: "typescript".to_owned(),
        compiler_version: TYPESCRIPT_VERSION.to_owned(),
        compiler_bundle_sha256,
        runtime: "node".to_owned(),
        runtime_version: String::from_utf8_lossy(&version_output.stdout)
            .trim()
            .to_owned(),
        runtime_executable_sha256,
    })
}

fn hash_file(path: &Path) -> Result<String, TypeScriptFailure> {
    let bytes = std::fs::read(path).map_err(|error| TypeScriptFailure {
        code: "frontend.typescript.toolchain-hash".to_owned(),
        message: format!("cannot hash {:?}: {error}", path),
        line: None,
        column: None,
    })?;
    Ok(hex_digest(&bytes))
}

fn hash_directory(root: &Path) -> Result<String, TypeScriptFailure> {
    let mut files = Vec::new();
    collect_files(root, root, &mut files)?;
    files.sort_by(|left, right| left.0.cmp(&right.0));
    let mut digest = Sha256::new();
    for (relative, path) in files {
        let bytes = std::fs::read(&path).map_err(|error| TypeScriptFailure {
            code: "frontend.typescript.toolchain-hash".to_owned(),
            message: format!("cannot hash {:?}: {error}", path),
            line: None,
            column: None,
        })?;
        digest.update((relative.len() as u64).to_be_bytes());
        digest.update(relative.as_bytes());
        digest.update((bytes.len() as u64).to_be_bytes());
        digest.update(bytes);
    }
    Ok(digest
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn collect_files(
    root: &Path,
    directory: &Path,
    files: &mut Vec<(String, PathBuf)>,
) -> Result<(), TypeScriptFailure> {
    let entries = std::fs::read_dir(directory).map_err(|error| TypeScriptFailure {
        code: "frontend.typescript.toolchain-hash".to_owned(),
        message: format!("cannot enumerate {:?}: {error}", directory),
        line: None,
        column: None,
    })?;
    for entry in entries {
        let entry = entry.map_err(|error| TypeScriptFailure {
            code: "frontend.typescript.toolchain-hash".to_owned(),
            message: error.to_string(),
            line: None,
            column: None,
        })?;
        let path = entry.path();
        if path.is_dir() {
            collect_files(root, &path, files)?;
        } else if path.is_file() {
            let relative = path
                .strip_prefix(root)
                .expect("enumerated file stays below root")
                .to_string_lossy()
                .replace('\\', "/");
            files.push((relative, path));
        }
    }
    Ok(())
}

fn hex_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn resolve_typescript_compiler() -> Result<PathBuf, TypeScriptFailure> {
    if let Some(path) = std::env::var_os("MALEDICTUS_TYPESCRIPT_COMPILER") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return Ok(path);
        }
    }
    if let Ok(executable) = std::env::current_exe()
        && let Some(directory) = executable.parent()
    {
        let packaged = directory.join("typescript/compiler/lib/typescript.js");
        if packaged.is_file() {
            return Ok(packaged);
        }
    }
    let development =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("node_modules/typescript/lib/typescript.js");
    if development.is_file() {
        return Ok(development);
    }
    Err(TypeScriptFailure {
        code: "frontend.typescript.compiler-unavailable".to_owned(),
        message: format!(
            "pinned TypeScript {TYPESCRIPT_VERSION} compiler not found; run npm install or set MALEDICTUS_TYPESCRIPT_COMPILER"
        ),
        line: None,
        column: None,
    })
}

fn resolve_typescript_frontend() -> Result<PathBuf, TypeScriptFailure> {
    if let Some(path) = std::env::var_os("MALEDICTUS_TYPESCRIPT_FRONTEND") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return validate_typescript_frontend(path);
        }
    }
    if let Ok(executable) = std::env::current_exe()
        && let Some(directory) = executable.parent()
    {
        let packaged = directory.join("typescript/frontend.cjs");
        if packaged.is_file() {
            return validate_typescript_frontend(packaged);
        }
    }
    let development = Path::new(env!("CARGO_MANIFEST_DIR")).join("typescript/frontend.cjs");
    if development.is_file() {
        return validate_typescript_frontend(development);
    }
    Err(TypeScriptFailure {
        code: "frontend.typescript.frontend-unavailable".to_owned(),
        message: "TypeScript compiler bridge was not found".to_owned(),
        line: None,
        column: None,
    })
}

fn validate_typescript_frontend(path: PathBuf) -> Result<PathBuf, TypeScriptFailure> {
    let actual = std::fs::read(&path).map_err(|error| TypeScriptFailure {
        code: "frontend.typescript.frontend-identity".to_owned(),
        message: format!("cannot read TypeScript compiler bridge {path:?}: {error}"),
        line: None,
        column: None,
    })?;
    let expected = include_bytes!("../typescript/frontend.cjs");
    if actual.as_slice() != expected {
        return Err(TypeScriptFailure {
            code: "frontend.typescript.frontend-identity".to_owned(),
            message: format!(
                "TypeScript compiler bridge {path:?} does not match the source-bound bridge"
            ),
            line: None,
            column: None,
        });
    }
    Ok(path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn real_strict_compiler_proves_closed_primitive_function() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("closed.ts");
        fs::write(
            &path,
            "export function choose(flag: boolean, left: number, right: number): number { return flag ? left : right; }\n",
        )
        .unwrap();
        let proof = verify_closed_module(&path, &["choose".to_owned()]).unwrap();
        assert_eq!(proof.compiler_version, TYPESCRIPT_VERSION);
        assert_eq!(proof.functions[0].name, "choose");
    }

    #[test]
    fn real_strict_compiler_refuses_type_error() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("invalid.ts");
        fs::write(
            &path,
            concat!(
                "function invalid(value: number): string { return value; }\n",
                "function implicit(value): number { return value; }\n",
            ),
        )
        .unwrap();
        let error = verify_closed_module(&path, &[]).unwrap_err();
        assert_eq!(error.code, "frontend.typescript.strict-typecheck");
        assert!(error.message.contains("TS2322"), "{error:#?}");
        assert!(error.message.contains("TS7006"), "{error:#?}");
    }

    #[test]
    fn compiler_typed_but_abstract_callback_boundary_is_refused() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("call.ts");
        fs::write(
            &path,
            "function call(callback: (value: number) => number, value: number): number { return callback(value); }\n",
        )
        .unwrap();
        let error = verify_closed_module(&path, &[]).unwrap_err();
        assert_eq!(
            error.code,
            "frontend.typescript.callback-boundary-unsupported"
        );
    }

    #[test]
    fn real_check_js_compiler_proves_explicitly_typed_closed_function() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("closed.js");
        fs::write(
            &path,
            "/**\n * @param {boolean} flag\n * @param {number} left\n * @param {number} right\n * @returns {number}\n */\nexport function choose(flag, left, right) { return flag ? left : right; }\n",
        )
        .unwrap();
        let proof = verify_closed_javascript_module(&path, &["choose".to_owned()]).unwrap();
        assert_eq!(proof.compiler_version, TYPESCRIPT_VERSION);
        assert_eq!(proof.schema, "maledictus-javascript-closed-verification/v8");
        assert_eq!(proof.functions[0].name, "choose");
        assert_eq!(proof.functions[0].return_type, "number");
    }

    #[test]
    fn real_check_js_compiler_refuses_declared_return_type_error() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("invalid.js");
        fs::write(
            &path,
            "/** @param {number} value @returns {string} */\nfunction invalid(value) { return value; }\n",
        )
        .unwrap();
        let error = verify_closed_javascript_module(&path, &[]).unwrap_err();
        assert_eq!(error.code, "frontend.javascript.strict-typecheck");
    }

    #[test]
    fn kernel_refuses_forged_source_class_ownership() {
        let constructor = TypeScriptFunction {
            name: "Item.constructor".to_owned(),
            exported: false,
            execution: TypeScriptExecution::Synchronous,
            parameters: vec![TypeScriptParameter {
                name: "value".to_owned(),
                descriptor: TypeScriptParameterDescriptor::Primitive {
                    type_name: "number".to_owned(),
                },
            }],
            return_type: "void".to_owned(),
            calls: vec![],
            outcome_graph: TypeScriptOutcomeGraph::Fallthrough,
        };
        let method = TypeScriptFunction {
            name: "Item.read".to_owned(),
            exported: false,
            execution: TypeScriptExecution::Synchronous,
            parameters: vec![],
            return_type: "number".to_owned(),
            calls: vec![],
            outcome_graph: TypeScriptOutcomeGraph::Return {
                type_name: "number".to_owned(),
            },
        };
        let forged = TypeScriptClass {
            name: "Other".to_owned(),
            fields: vec![RecordField {
                name: "value".to_owned(),
                type_name: "number".to_owned(),
            }],
            constructor: "Item.constructor".to_owned(),
            methods: vec!["Item.read".to_owned()],
        };
        let error = validate_outcome_graphs(
            &[constructor, method],
            &[forged],
            &[],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.typescript.compiler-protocol");
    }

    #[test]
    fn compiler_typed_but_abstract_javascript_callback_boundary_is_refused() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("call.js");
        fs::write(
            &path,
            "/** @param {(value: number) => number} callback @param {number} value @returns {number} */\nfunction call(callback, value) { return callback(value); }\n",
        )
        .unwrap();
        let error = verify_closed_javascript_module(&path, &[]).unwrap_err();
        assert_eq!(
            error.code,
            "frontend.javascript.callback-boundary-unsupported"
        );
    }

    #[test]
    fn javascript_mode_refuses_a_typescript_source_extension() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("mislabelled.ts");
        fs::write(&path, "function value(): number { return 1; }\n").unwrap();
        let error = verify_closed_javascript_module(&path, &[]).unwrap_err();
        assert_eq!(error.code, "frontend.javascript.source-extension");
    }

    #[test]
    fn runtime_bridge_must_match_the_source_bound_frontend() {
        let directory = tempfile::tempdir().unwrap();
        let exact = directory.path().join("exact.cjs");
        fs::write(&exact, include_bytes!("../typescript/frontend.cjs")).unwrap();
        assert_eq!(validate_typescript_frontend(exact.clone()).unwrap(), exact);

        let substituted = directory.path().join("substituted.cjs");
        fs::write(&substituted, b"process.stdout.write('{}');\n").unwrap();
        let failure = validate_typescript_frontend(substituted).unwrap_err();
        assert_eq!(failure.code, "frontend.typescript.frontend-identity");
    }

    #[test]
    fn compiler_bridge_protocol_rejects_unknown_fields_and_malformed_outcomes() {
        let response = r#"{
            "status": "refused",
            "code": "frontend.typescript.example",
            "message": "example",
            "line": null,
            "column": null,
            "unexpected": true
        }"#;
        assert!(serde_json::from_str::<FrontendResult>(response).is_err());

        let call_summary_mismatch = TypeScriptFunction {
            name: "root".to_owned(),
            exported: false,
            execution: TypeScriptExecution::Synchronous,
            parameters: Vec::new(),
            return_type: "number".to_owned(),
            calls: Vec::new(),
            outcome_graph: TypeScriptOutcomeGraph::Call {
                callee: "helper".to_owned(),
                arguments: Vec::new(),
                line: 1,
                column: 1,
            },
        };
        let failure = validate_outcome_graphs(
            &[call_summary_mismatch],
            &[],
            &["root".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(failure.code, "frontend.typescript.compiler-protocol");

        let invalid_raise = TypeScriptFunction {
            name: "root".to_owned(),
            exported: false,
            execution: TypeScriptExecution::Synchronous,
            parameters: Vec::new(),
            return_type: "number".to_owned(),
            calls: Vec::new(),
            outcome_graph: TypeScriptOutcomeGraph::Raise {
                exception_type: "ecmascript.throw.object".to_owned(),
                line: 1,
                column: 1,
            },
        };
        let failure = validate_outcome_graphs(
            &[invalid_raise],
            &[],
            &["root".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(failure.code, "frontend.typescript.compiler-protocol");
    }

    #[test]
    fn compiler_bridge_recomputes_sealed_record_provenance_and_boundaries() {
        let fields = vec![RecordField {
            name: "value".to_owned(),
            type_name: "number".to_owned(),
        }];
        let helper = TypeScriptFunction {
            name: "helper".to_owned(),
            exported: false,
            execution: TypeScriptExecution::Synchronous,
            parameters: vec![TypeScriptParameter {
                name: "item".to_owned(),
                descriptor: TypeScriptParameterDescriptor::Record {
                    fields: fields.clone(),
                },
            }],
            return_type: "number".to_owned(),
            calls: Vec::new(),
            outcome_graph: TypeScriptOutcomeGraph::Return {
                type_name: "number".to_owned(),
            },
        };
        let root = TypeScriptFunction {
            name: "root".to_owned(),
            exported: true,
            execution: TypeScriptExecution::Synchronous,
            parameters: Vec::new(),
            return_type: "number".to_owned(),
            calls: vec!["helper".to_owned()],
            outcome_graph: TypeScriptOutcomeGraph::Sequence {
                items: vec![
                    TypeScriptOutcomeGraph::Call {
                        callee: "helper".to_owned(),
                        arguments: vec![TypeScriptArgumentDescriptor::Primitive {
                            type_name: "number".to_owned(),
                        }],
                        line: 1,
                        column: 1,
                    },
                    TypeScriptOutcomeGraph::Return {
                        type_name: "number".to_owned(),
                    },
                ],
            },
        };
        let failure = validate_outcome_graphs(
            &[helper.clone(), root],
            &[],
            &["root".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(failure.code, "frontend.typescript.compiler-protocol");

        let failure = validate_outcome_graphs(
            &[helper],
            &[],
            &["helper".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(failure.code, "frontend.typescript.compiler-protocol");
    }

    #[test]
    fn compiler_bridge_recomputes_terminal_switch_shape_and_exits() {
        fn terminal_switch(cases: Vec<TypeScriptSwitchCase>) -> TypeScriptFunction {
            TypeScriptFunction {
                name: "root".to_owned(),
                exported: true,
                execution: TypeScriptExecution::Synchronous,
                parameters: vec![TypeScriptParameter {
                    name: "kind".to_owned(),
                    descriptor: TypeScriptParameterDescriptor::Primitive {
                        type_name: "string".to_owned(),
                    },
                }],
                return_type: "number".to_owned(),
                calls: Vec::new(),
                outcome_graph: TypeScriptOutcomeGraph::TerminalSwitch {
                    discriminant: Box::new(TypeScriptOutcomeGraph::Fallthrough),
                    discriminant_type: "string".to_owned(),
                    cases,
                    default_body: Box::new(TypeScriptOutcomeGraph::Return {
                        type_name: "number".to_owned(),
                    }),
                },
            }
        }

        let case = || TypeScriptSwitchCase {
            label: TypeScriptSwitchLabel {
                type_name: "string".to_owned(),
                value: serde_json::Value::String("ready".to_owned()),
            },
            body: TypeScriptOutcomeGraph::Return {
                type_name: "number".to_owned(),
            },
        };
        let failure = validate_outcome_graphs(
            &[terminal_switch(vec![case(), case()])],
            &[],
            &["root".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(failure.code, "frontend.typescript.compiler-protocol");

        let mut wrong_type = case();
        wrong_type.label.type_name = "number".to_owned();
        wrong_type.label.value = serde_json::json!(1);
        let failure = validate_outcome_graphs(
            &[terminal_switch(vec![wrong_type])],
            &[],
            &["root".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(failure.code, "frontend.typescript.compiler-protocol");

        let mut falling_through = case();
        falling_through.body = TypeScriptOutcomeGraph::Fallthrough;
        let failure = validate_outcome_graphs(
            &[terminal_switch(vec![falling_through])],
            &[],
            &["root".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(failure.code, "frontend.typescript.compiler-protocol");

        let mut falling_default = terminal_switch(vec![case()]);
        let TypeScriptOutcomeGraph::TerminalSwitch { default_body, .. } =
            &mut falling_default.outcome_graph
        else {
            unreachable!("test helper always constructs a terminal switch")
        };
        **default_body = TypeScriptOutcomeGraph::Fallthrough;
        let failure = validate_outcome_graphs(
            &[falling_default],
            &[],
            &["root".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(failure.code, "frontend.typescript.compiler-protocol");
    }

    #[test]
    fn compiler_proves_closed_typescript_locals_blocks_and_branches() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("control.ts");
        fs::write(
            &path,
            "export function choose(flag: boolean, left: number, right: number): number {\n  const offset = 2;\n  if (flag) {\n    const selected = left + offset;\n    return selected;\n  }\n  return right + offset;\n}\n",
        )
        .unwrap();
        let proof = verify_closed_module(&path, &["choose".to_owned()]).unwrap();
        assert_eq!(proof.functions[0].return_type, "number");
    }

    #[test]
    fn check_js_proves_closed_locals_blocks_and_branches() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("control.js");
        fs::write(
            &path,
            "/** @param {boolean} flag @param {number} left @param {number} right @returns {number} */\nexport function choose(flag, left, right) {\n  const offset = 2;\n  if (flag) {\n    const selected = left + offset;\n    return selected;\n  }\n  return right + offset;\n}\n",
        )
        .unwrap();
        let proof = verify_closed_javascript_module(&path, &["choose".to_owned()]).unwrap();
        assert_eq!(proof.functions[0].return_type, "number");
    }

    #[test]
    fn closed_javascript_control_flow_refuses_mutable_locals() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("mutable.js");
        fs::write(
            &path,
            "/** @returns {number} */\nfunction mutable() { let value = 1; return value; }\n",
        )
        .unwrap();
        let error = verify_closed_javascript_module(&path, &[]).unwrap_err();
        assert_eq!(error.code, "frontend.javascript.mutable-local-unsupported");
    }

    #[test]
    fn compiler_proves_acyclic_source_local_typescript_calls() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("calls.ts");
        fs::write(
            &path,
            "function offset(value: number): number { return value + 2; }\nexport function choose(flag: boolean, left: number, right: number): number { return flag ? offset(left) : offset(right); }\n",
        )
        .unwrap();
        let proof = verify_closed_module(&path, &["choose".to_owned()]).unwrap();
        let choose = proof
            .functions
            .iter()
            .find(|function| function.name == "choose")
            .unwrap();
        assert_eq!(choose.calls, ["offset"]);
    }

    #[test]
    fn check_js_proves_acyclic_source_local_calls() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("calls.js");
        fs::write(
            &path,
            "/** @param {number} value @returns {number} */\nfunction offset(value) { return value + 2; }\n/** @param {boolean} flag @param {number} left @param {number} right @returns {number} */\nexport function choose(flag, left, right) { return flag ? offset(left) : offset(right); }\n",
        )
        .unwrap();
        let proof = verify_closed_javascript_module(&path, &["choose".to_owned()]).unwrap();
        let choose = proof
            .functions
            .iter()
            .find(|function| function.name == "choose")
            .unwrap();
        assert_eq!(choose.calls, ["offset"]);
    }

    #[test]
    fn compiler_refuses_recursive_source_call_cycle() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("recursive.ts");
        fs::write(
            &path,
            "function left(value: number): number { return right(value); }\nfunction right(value: number): number { return left(value); }\n",
        )
        .unwrap();
        let error = verify_closed_module(&path, &[]).unwrap_err();
        assert_eq!(error.code, "frontend.typescript.call-cycle-unsupported");
    }

    #[test]
    fn compiler_refuses_direct_external_call() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("external.ts");
        fs::write(
            &path,
            "function convert(value: number): number { return Number(value); }\n",
        )
        .unwrap();
        let error = verify_closed_module(&path, &[]).unwrap_err();
        assert_eq!(error.code, "frontend.typescript.call-external-unsupported");
    }

    #[test]
    fn rust_rejects_forged_callback_provenance_and_invocation_parameters() {
        let primitive = TypeScriptParameterDescriptor::Primitive {
            type_name: "number".to_owned(),
        };
        let callback = TypeScriptParameterDescriptor::Callback {
            parameter_types: vec!["number".to_owned()],
            return_type: "number".to_owned(),
        };
        let source_callback = TypeScriptArgumentDescriptor::SourceCallback {
            function: "missing".to_owned(),
            parameter_types: vec!["number".to_owned()],
            return_type: "number".to_owned(),
        };
        let functions = vec![
            TypeScriptFunction {
                name: "apply".to_owned(),
                exported: false,
                execution: TypeScriptExecution::Synchronous,
                parameters: vec![
                    TypeScriptParameter {
                        name: "callback".to_owned(),
                        descriptor: callback,
                    },
                    TypeScriptParameter {
                        name: "value".to_owned(),
                        descriptor: primitive.clone(),
                    },
                ],
                return_type: "number".to_owned(),
                calls: Vec::new(),
                outcome_graph: TypeScriptOutcomeGraph::CallbackInvoke {
                    parameter: "not_callback".to_owned(),
                    arguments: vec![TypeScriptArgumentDescriptor::Primitive {
                        type_name: "number".to_owned(),
                    }],
                    line: 1,
                    column: 1,
                },
            },
            TypeScriptFunction {
                name: "run".to_owned(),
                exported: true,
                execution: TypeScriptExecution::Synchronous,
                parameters: vec![TypeScriptParameter {
                    name: "value".to_owned(),
                    descriptor: primitive,
                }],
                return_type: "number".to_owned(),
                calls: vec!["apply".to_owned(), "missing".to_owned()],
                outcome_graph: TypeScriptOutcomeGraph::Call {
                    callee: "apply".to_owned(),
                    arguments: vec![
                        source_callback,
                        TypeScriptArgumentDescriptor::Primitive {
                            type_name: "number".to_owned(),
                        },
                    ],
                    line: 2,
                    column: 1,
                },
            },
        ];
        let error = validate_outcome_graphs(
            &functions,
            &[],
            &["run".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.typescript.compiler-protocol");
    }

    #[test]
    fn rust_detects_cycles_created_only_by_callback_substitution() {
        let primitive = TypeScriptParameterDescriptor::Primitive {
            type_name: "number".to_owned(),
        };
        let source_loop = TypeScriptArgumentDescriptor::SourceCallback {
            function: "loop".to_owned(),
            parameter_types: vec!["number".to_owned()],
            return_type: "number".to_owned(),
        };
        let functions = vec![
            TypeScriptFunction {
                name: "apply".to_owned(),
                exported: false,
                execution: TypeScriptExecution::Synchronous,
                parameters: vec![
                    TypeScriptParameter {
                        name: "callback".to_owned(),
                        descriptor: TypeScriptParameterDescriptor::Callback {
                            parameter_types: vec!["number".to_owned()],
                            return_type: "number".to_owned(),
                        },
                    },
                    TypeScriptParameter {
                        name: "value".to_owned(),
                        descriptor: primitive.clone(),
                    },
                ],
                return_type: "number".to_owned(),
                calls: Vec::new(),
                outcome_graph: TypeScriptOutcomeGraph::Sequence {
                    items: vec![
                        TypeScriptOutcomeGraph::CallbackInvoke {
                            parameter: "callback".to_owned(),
                            arguments: vec![TypeScriptArgumentDescriptor::Primitive {
                                type_name: "number".to_owned(),
                            }],
                            line: 1,
                            column: 1,
                        },
                        TypeScriptOutcomeGraph::Return {
                            type_name: "number".to_owned(),
                        },
                    ],
                },
            },
            TypeScriptFunction {
                name: "loop".to_owned(),
                exported: true,
                execution: TypeScriptExecution::Synchronous,
                parameters: vec![TypeScriptParameter {
                    name: "value".to_owned(),
                    descriptor: primitive,
                }],
                return_type: "number".to_owned(),
                calls: vec!["apply".to_owned(), "loop".to_owned()],
                outcome_graph: TypeScriptOutcomeGraph::Call {
                    callee: "apply".to_owned(),
                    arguments: vec![
                        source_loop,
                        TypeScriptArgumentDescriptor::Primitive {
                            type_name: "number".to_owned(),
                        },
                    ],
                    line: 2,
                    column: 1,
                },
            },
        ];
        let error = validate_outcome_graphs(
            &functions,
            &[],
            &["loop".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.typescript.compiler-protocol");
        assert!(error.message.contains("call cycle"));
    }

    #[test]
    fn rust_recomputes_async_call_modes_and_rejection_propagation() {
        let sync_helper = TypeScriptFunction {
            name: "sync_helper".to_owned(),
            exported: false,
            execution: TypeScriptExecution::Synchronous,
            parameters: Vec::new(),
            return_type: "number".to_owned(),
            calls: Vec::new(),
            outcome_graph: TypeScriptOutcomeGraph::Return {
                type_name: "number".to_owned(),
            },
        };
        let forged_sync_await = TypeScriptFunction {
            name: "root".to_owned(),
            exported: true,
            execution: TypeScriptExecution::Synchronous,
            parameters: Vec::new(),
            return_type: "number".to_owned(),
            calls: vec!["sync_helper".to_owned()],
            outcome_graph: TypeScriptOutcomeGraph::AwaitCall {
                callee: "sync_helper".to_owned(),
                arguments: Vec::new(),
                line: 1,
                column: 1,
            },
        };
        let error = validate_outcome_graphs(
            &[sync_helper.clone(), forged_sync_await],
            &[],
            &["root".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.typescript.compiler-protocol");

        let forged_adoption = TypeScriptFunction {
            name: "root".to_owned(),
            exported: true,
            execution: TypeScriptExecution::Asynchronous,
            parameters: Vec::new(),
            return_type: "number".to_owned(),
            calls: vec!["sync_helper".to_owned()],
            outcome_graph: TypeScriptOutcomeGraph::PromiseAdopt {
                callee: "sync_helper".to_owned(),
                arguments: Vec::new(),
                line: 1,
                column: 1,
            },
        };
        let error = validate_outcome_graphs(
            &[sync_helper, forged_adoption],
            &[],
            &["root".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.typescript.compiler-protocol");

        let rejecting = TypeScriptFunction {
            name: "rejecting".to_owned(),
            exported: false,
            execution: TypeScriptExecution::Asynchronous,
            parameters: Vec::new(),
            return_type: "number".to_owned(),
            calls: Vec::new(),
            outcome_graph: TypeScriptOutcomeGraph::Raise {
                exception_type: "ecmascript.throw.string".to_owned(),
                line: 1,
                column: 1,
            },
        };
        let adopting = TypeScriptFunction {
            name: "root".to_owned(),
            exported: true,
            execution: TypeScriptExecution::Asynchronous,
            parameters: Vec::new(),
            return_type: "number".to_owned(),
            calls: vec!["rejecting".to_owned()],
            outcome_graph: TypeScriptOutcomeGraph::PromiseAdopt {
                callee: "rejecting".to_owned(),
                arguments: Vec::new(),
                line: 2,
                column: 3,
            },
        };
        let error = validate_outcome_graphs(
            &[rejecting, adopting],
            &[],
            &["root".to_owned()],
            SourceLanguage::TypeScript,
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.typescript.unexpected-rejection");
        assert_eq!((error.line, error.column), (Some(2), Some(3)));
    }
}
