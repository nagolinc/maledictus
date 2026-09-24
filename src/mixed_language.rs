//! Source-bound composition of one Python caller with one primitive-total JS/TS provider.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use crate::protocol::{
    CrossLanguageBindingResult, CrossLanguagePrimitive, ProofRequest, SourceFile,
    TypeScriptToolchainIdentity,
};
use crate::python_contracts::{
    ImportedContractModule, imported_primitive_total_module, validate_mixed_binding_use,
};
use crate::python_typecheck::GeneratedPythonInterface;
use crate::typescript::{
    TypeScriptExecution, TypeScriptFunction, TypeScriptOutcomeGraph, TypeScriptParameterDescriptor,
    verify_closed_javascript_module, verify_closed_module,
};
use crate::vc::Sort;

pub const MIXED_LANGUAGE_FRAGMENT: &str = "python-to-js-primitive-total/v1";

pub struct ResolvedMixedLanguage {
    pub caller_modules: BTreeMap<String, ImportedContractModule>,
    pub generated_interfaces: Vec<GeneratedPythonInterface>,
    pub results: Vec<CrossLanguageBindingResult>,
    pub provider_paths: BTreeSet<String>,
    pub caller_paths: BTreeSet<String>,
    pub toolchain: Option<TypeScriptToolchainIdentity>,
}

#[derive(Clone, Debug)]
pub struct MixedLanguageFailure {
    pub code: &'static str,
    pub message: String,
    pub path: Option<String>,
    pub line: Option<u32>,
    pub column: Option<u32>,
}

fn failure(code: &'static str, message: impl Into<String>) -> MixedLanguageFailure {
    MixedLanguageFailure {
        code,
        message: message.into(),
        path: None,
        line: None,
        column: None,
    }
}

fn valid_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    chars
        .next()
        .is_some_and(|first| first == '_' || first.is_ascii_alphabetic())
        && chars.all(|character| character == '_' || character.is_ascii_alphanumeric())
}

fn valid_module(value: &str) -> bool {
    !value.is_empty() && value.split('.').all(valid_identifier)
}

fn confined_file(root: &Path, relative: &str) -> Result<PathBuf, MixedLanguageFailure> {
    let relative_path = Path::new(relative);
    if relative_path.is_absolute() {
        return Err(failure(
            "frontend.cross-language.source-path",
            format!("mixed source path {relative:?} must be relative"),
        ));
    }
    let path = fs::canonicalize(root.join(relative_path)).map_err(|error| {
        failure(
            "frontend.cross-language.source-path",
            format!("cannot resolve mixed source path {relative:?}: {error}"),
        )
    })?;
    if !path.starts_with(root) || !path.is_file() {
        return Err(failure(
            "frontend.cross-language.source-path",
            format!("mixed source path {relative:?} escapes source_root or is not a file"),
        ));
    }
    Ok(path)
}

fn one_requested_file<'a>(
    files: &'a [SourceFile],
    path: &str,
) -> Result<&'a SourceFile, MixedLanguageFailure> {
    let matches = files
        .iter()
        .filter(|source| source.path == path)
        .collect::<Vec<_>>();
    if matches.len() != 1 {
        return Err(failure(
            "frontend.cross-language.request-file",
            format!("mixed path {path:?} must identify exactly one requested source file"),
        ));
    }
    Ok(matches[0])
}

fn primitive_from_compiler(
    type_name: &str,
) -> Result<CrossLanguagePrimitive, MixedLanguageFailure> {
    match type_name {
        "boolean" => Ok(CrossLanguagePrimitive::Bool),
        "string" => Ok(CrossLanguagePrimitive::Str),
        "void" => Ok(CrossLanguagePrimitive::None),
        "number" => Err(failure(
            "frontend.cross-language.number-unsupported",
            "JavaScript number cannot be represented as a Python int without integer/range evidence",
        )),
        _ => Err(failure(
            "frontend.cross-language.type-unsupported",
            format!("compiler returned unsupported mixed primitive {type_name:?}"),
        )),
    }
}

fn python_sort(primitive: &CrossLanguagePrimitive) -> Sort {
    match primitive {
        CrossLanguagePrimitive::Bool => Sort::Bool,
        CrossLanguagePrimitive::Str => Sort::String,
        CrossLanguagePrimitive::None => Sort::Unit,
    }
}

fn python_annotation(primitive: &CrossLanguagePrimitive) -> &'static str {
    match primitive {
        CrossLanguagePrimitive::Bool => "bool",
        CrossLanguagePrimitive::Str => "str",
        CrossLanguagePrimitive::None => "None",
    }
}

fn sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn exact_provider_function<'a>(
    functions: &'a [TypeScriptFunction],
    name: &str,
) -> Result<&'a TypeScriptFunction, MixedLanguageFailure> {
    let exported = functions
        .iter()
        .filter(|function| function.exported)
        .collect::<Vec<_>>();
    if exported.len() != 1 || exported[0].name != name {
        return Err(failure(
            "frontend.cross-language.provider-export-set",
            "mixed v1 provider must expose exactly the one explicitly bound export",
        ));
    }
    let matches = functions
        .iter()
        .filter(|function| function.name == name)
        .collect::<Vec<_>>();
    if matches.len() != 1 {
        return Err(failure(
            "frontend.cross-language.provider-export",
            format!("provider must contain exactly one compiler-described export {name:?}"),
        ));
    }
    let function = matches[0];
    if !function.exported {
        return Err(failure(
            "frontend.cross-language.provider-unexported",
            format!("provider function {name:?} is not exported"),
        ));
    }
    if function.execution != TypeScriptExecution::Synchronous {
        return Err(failure(
            "frontend.cross-language.provider-async-unsupported",
            "mixed v1 provider must be synchronous; Promise fulfillment/rejection is not a Python total return",
        ));
    }
    if !function.calls.is_empty() {
        return Err(failure(
            "frontend.cross-language.provider-call-unsupported",
            "mixed v1 provider must be a direct primitive-total function without helper calls",
        ));
    }
    fn pure_fallthrough(graph: &TypeScriptOutcomeGraph) -> bool {
        match graph {
            TypeScriptOutcomeGraph::Fallthrough => true,
            TypeScriptOutcomeGraph::Sequence { items } => items.iter().all(pure_fallthrough),
            _ => false,
        }
    }
    fn direct_return(graph: &TypeScriptOutcomeGraph) -> Option<&str> {
        match graph {
            TypeScriptOutcomeGraph::Return { type_name } => Some(type_name),
            TypeScriptOutcomeGraph::Sequence { items } => {
                let (last, prefix) = items.split_last()?;
                prefix
                    .iter()
                    .all(pure_fallthrough)
                    .then(|| direct_return(last))
                    .flatten()
            }
            _ => None,
        }
    }
    let direct_return = direct_return(&function.outcome_graph);
    if direct_return != Some(function.return_type.as_str()) {
        return Err(failure(
            "frontend.cross-language.provider-outcome-unsupported",
            format!(
                "mixed v1 provider must have one direct Return outcome and no exceptional/control outcomes; compiler graph was {:?}",
                function.outcome_graph
            ),
        ));
    }
    Ok(function)
}

pub fn resolve(
    root: &Path,
    request: &ProofRequest,
) -> Result<ResolvedMixedLanguage, MixedLanguageFailure> {
    if request.cross_language_bindings.is_empty() {
        return Ok(ResolvedMixedLanguage {
            caller_modules: BTreeMap::new(),
            generated_interfaces: Vec::new(),
            results: Vec::new(),
            provider_paths: BTreeSet::new(),
            caller_paths: BTreeSet::new(),
            toolchain: None,
        });
    }
    if request.cross_language_bindings.len() != 1 {
        return Err(failure(
            "frontend.cross-language.binding-count",
            "mixed v1 requires exactly one explicit Python-to-JS/TS binding",
        ));
    }
    let binding = &request.cross_language_bindings[0];
    if !valid_identifier(&binding.id)
        || !valid_module(&binding.python_module)
        || !valid_identifier(&binding.python_symbol)
        || !valid_identifier(&binding.provider_export)
        || binding.caller_path == binding.provider_path
    {
        return Err(failure(
            "frontend.cross-language.binding-invalid",
            "mixed binding identifiers, module, and distinct source paths must be canonical",
        ));
    }
    let caller_file = one_requested_file(&request.files, &binding.caller_path)?;
    let provider_file = one_requested_file(&request.files, &binding.provider_path)?;
    if caller_file.language != "python" {
        return Err(failure(
            "frontend.cross-language.caller-language",
            "mixed v1 caller must be requested Python source",
        ));
    }
    if !matches!(provider_file.language.as_str(), "javascript" | "typescript") {
        return Err(failure(
            "frontend.cross-language.provider-language",
            "mixed v1 provider must be requested JavaScript/checkJs or TypeScript source",
        ));
    }
    if provider_file.symbols.as_slice() != [binding.provider_export.as_str()] {
        return Err(failure(
            "frontend.cross-language.provider-request",
            "mixed provider SourceFile must request exactly the bound export",
        ));
    }
    let caller_path = confined_file(root, &binding.caller_path)?;
    let provider_path = confined_file(root, &binding.provider_path)?;
    let caller_bytes = fs::read(&caller_path).map_err(|error| {
        failure(
            "frontend.cross-language.source-read",
            format!("cannot read mixed Python caller: {error}"),
        )
    })?;
    let provider_bytes = fs::read(&provider_path).map_err(|error| {
        failure(
            "frontend.cross-language.source-read",
            format!("cannot read mixed provider: {error}"),
        )
    })?;
    let requested = vec![binding.provider_export.clone()];
    let verification = if provider_file.language == "javascript" {
        verify_closed_javascript_module(&provider_path, &requested)
    } else {
        verify_closed_module(&provider_path, &requested)
    }
    .map_err(|error| MixedLanguageFailure {
        code: "frontend.cross-language.provider-refused",
        message: format!("{}: {}", error.code, error.message),
        path: Some(binding.provider_path.clone()),
        line: error.line,
        column: error.column,
    })?;
    let function = exact_provider_function(&verification.functions, &binding.provider_export)?;
    let mut parameters = Vec::new();
    for parameter in &function.parameters {
        if matches!(
            parameter.descriptor,
            TypeScriptParameterDescriptor::Callback { .. }
        ) {
            return Err(failure(
                "frontend.cross-language.callback-unsupported",
                "mixed v1 does not permit callback parameters across the Python-to-JS boundary",
            ));
        }
        let TypeScriptParameterDescriptor::Primitive { type_name } = &parameter.descriptor else {
            return Err(failure(
                "frontend.cross-language.type-unsupported",
                "mixed v1 accepts only compiler-resolved primitive provider parameters",
            ));
        };
        let primitive = primitive_from_compiler(type_name)?;
        if primitive == CrossLanguagePrimitive::None {
            return Err(failure(
                "frontend.cross-language.parameter-void",
                "mixed provider parameters cannot have void/None type",
            ));
        }
        parameters.push(crate::protocol::CrossLanguageParameter {
            name: parameter.name.clone(),
            type_name: primitive,
        });
    }
    let return_type = primitive_from_compiler(&function.return_type)?;
    if parameters != binding.parameters || return_type != binding.return_type {
        return Err(failure(
            "frontend.cross-language.signature-mismatch",
            "request signature assertions do not exactly equal the real compiler-derived signature",
        ));
    }
    let caller_text = std::str::from_utf8(&caller_bytes).map_err(|error| {
        failure(
            "frontend.cross-language.caller-utf8",
            format!("mixed Python caller is not UTF-8: {error}"),
        )
    })?;
    validate_mixed_binding_use(
        caller_text,
        &binding.caller_path,
        &binding.python_module,
        &binding.python_symbol,
        &caller_file.symbols,
    )
    .map_err(|error| failure(error.code, error.message))?;
    let python_parameters = parameters
        .iter()
        .map(|parameter| (parameter.name.clone(), python_sort(&parameter.type_name)))
        .collect::<Vec<_>>();
    let imported = imported_primitive_total_module(
        &binding.python_module,
        &binding.python_symbol,
        &python_parameters,
        python_sort(&return_type),
    )
    .map_err(|error| failure(error.code, error.message))?;
    let rendered_parameters = parameters
        .iter()
        .map(|parameter| {
            format!(
                "{}: {}",
                parameter.name,
                python_annotation(&parameter.type_name)
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    let interface = format!(
        "def {}({}) -> {}: ...\n",
        binding.python_symbol,
        rendered_parameters,
        python_annotation(&return_type)
    )
    .into_bytes();
    let interface_sha256 = sha256(&interface);
    let result = CrossLanguageBindingResult {
        id: binding.id.clone(),
        caller_path: binding.caller_path.clone(),
        caller_sha256: sha256(&caller_bytes),
        python_module: binding.python_module.clone(),
        python_symbol: binding.python_symbol.clone(),
        provider_path: binding.provider_path.clone(),
        provider_sha256: sha256(&provider_bytes),
        provider_export: binding.provider_export.clone(),
        provider_language: provider_file.language.clone(),
        parameters,
        return_type,
        interface_sha256,
        scope: "compiler-derived-primitive-signature; strict-python-interface; direct-call-edge; composed-no-undeclared-exception".to_owned(),
    };
    Ok(ResolvedMixedLanguage {
        caller_modules: BTreeMap::from([(binding.caller_path.clone(), imported)]),
        generated_interfaces: vec![GeneratedPythonInterface {
            module: binding.python_module.clone(),
            contents: interface,
            diagnostic_path: format!("cross-language-binding:{}", binding.id),
        }],
        results: vec![result],
        provider_paths: BTreeSet::from([binding.provider_path.clone()]),
        caller_paths: BTreeSet::from([binding.caller_path.clone()]),
        toolchain: Some(verification.toolchain),
    })
}
