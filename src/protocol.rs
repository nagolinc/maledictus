use serde::{Deserialize, Serialize};

use crate::VERSION;

pub const PROTOCOL_SCHEMA: &str = "maledictus-verification-request/v4";
pub const RESPONSE_SCHEMA: &str = "maledictus-verification-result/v7";

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ProofRequest {
    pub schema: String,
    pub source_root: String,
    pub source_fingerprint: String,
    pub proof_obligation: String,
    pub files: Vec<SourceFile>,
    #[serde(default)]
    pub external_contract_overlays: Vec<ExternalOverlay>,
    #[serde(default)]
    pub cross_language_bindings: Vec<CrossLanguageBinding>,
    #[serde(default)]
    pub python_callable_bindings: Vec<PythonCallableBinding>,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum CrossLanguagePrimitive {
    Bool,
    Str,
    None,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct CrossLanguageParameter {
    pub name: String,
    /// An audit assertion checked against the real compiler descriptor; never an authority.
    pub type_name: CrossLanguagePrimitive,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CrossLanguageBinding {
    pub id: String,
    pub caller_path: String,
    pub python_module: String,
    pub python_symbol: String,
    pub provider_path: String,
    pub provider_export: String,
    /// Assertions retained for review and required to equal the compiler-derived signature.
    pub parameters: Vec<CrossLanguageParameter>,
    pub return_type: CrossLanguagePrimitive,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CrossLanguageBindingResult {
    pub id: String,
    pub caller_path: String,
    pub caller_sha256: String,
    pub python_module: String,
    pub python_symbol: String,
    pub provider_path: String,
    pub provider_sha256: String,
    pub provider_export: String,
    pub provider_language: String,
    pub parameters: Vec<CrossLanguageParameter>,
    pub return_type: CrossLanguagePrimitive,
    pub interface_sha256: String,
    pub scope: String,
}

/// An auditable binding from one callable-valued operation-input field to its concrete provider.
/// The request identifies provenance; Maledictus derives the signature and effects from the real
/// source file or checked external contract and rejects any mismatch with the field annotation.
#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct PythonCallableBinding {
    pub id: String,
    pub consumer_path: String,
    pub operation_symbol: String,
    pub input_record: String,
    pub field: String,
    pub provider: PythonCallableProvider,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum PythonCallableProvider {
    Source { path: String, symbol: String },
    ExternalContract { module: String, symbol: String },
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct PythonCallableBindingResult {
    pub id: String,
    pub consumer_path: String,
    pub consumer_sha256: String,
    pub operation_symbol: String,
    pub input_record: String,
    pub field: String,
    pub provider: PythonCallableProviderResult,
    pub scope: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum PythonCallableProviderResult {
    Source {
        path: String,
        sha256: String,
        symbol: String,
    },
    ExternalContract {
        module: String,
        stub_path: String,
        stub_sha256: String,
        symbol: String,
    },
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceFile {
    pub path: String,
    pub language: String,
    #[serde(default)]
    pub symbols: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExternalOverlay {
    pub adapter_path: String,
    pub module: String,
    pub stub_path: String,
    pub exception_policy: ExternalExceptionPolicy,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExternalExceptionPolicy {
    AssumeNoException,
    DeclaredByExsures,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExternalContractResult {
    pub adapter_path: String,
    pub module: String,
    pub stub_path: String,
    pub sha256: String,
    pub functions: Vec<String>,
    /// Module-qualified user-defined value types exported by an object/reference contract.
    pub nominal_types: Vec<String>,
    /// Module-qualified classes whose field/constructor/method effects come from a heap contract.
    pub heap_types: Vec<String>,
    /// Source-declared exception classes whose nominal ancestry was checked from the stub.
    pub exception_types: Vec<String>,
    pub exception_policy: ExternalExceptionPolicy,
    pub declared_exceptions: Vec<String>,
    /// This scope states exactly what remains an assumption rather than a verified source fact.
    pub scope: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceImportResult {
    pub importer_path: String,
    pub module: String,
    pub provider_path: String,
    pub provider_sha256: String,
    pub imported_symbols: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ProofStatus {
    Proved,
    Refuted,
    Refused,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FileResult {
    pub path: String,
    pub sha256: String,
    pub symbols: Vec<String>,
    pub scope: String,
    pub result: ProofStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fragment: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub verified_interfaces: Vec<VerifiedLeafInterface>,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct VerifiedLeafParameter {
    pub name: String,
    pub type_name: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct VerifiedLeafInterface {
    pub symbol: String,
    pub execution: String,
    pub parameters: Vec<VerifiedLeafParameter>,
    pub return_type: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SolverIdentity {
    pub solver: String,
    pub solver_version: String,
    pub rust_binding: String,
    pub vc_ir: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct VerifierIdentity {
    pub executable_sha256: String,
    pub frontend_bundle_sha256: String,
    pub kernel_bundle_sha256: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TypeScriptToolchainIdentity {
    pub compiler: String,
    pub compiler_version: String,
    pub compiler_bundle_sha256: String,
    pub runtime: String,
    pub runtime_version: String,
    pub runtime_executable_sha256: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct PythonTypecheckerIdentity {
    pub checker: String,
    pub checker_version: String,
    pub profile: String,
    pub package_sha256: String,
    pub runtime: String,
    pub runtime_version: String,
    pub runtime_executable_sha256: String,
    pub runtime_bundle_sha256: String,
    pub configuration_sha256: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub contract_support_sha256: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct Diagnostic {
    pub severity: String,
    pub code: String,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub column: Option<u32>,
}

impl Diagnostic {
    pub fn error(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: "error".to_owned(),
            code: code.into(),
            message: message.into(),
            path: None,
            line: None,
            column: None,
        }
    }

    pub fn file_error(
        code: impl Into<String>,
        message: impl Into<String>,
        path: impl Into<String>,
    ) -> Self {
        Self {
            path: Some(path.into()),
            ..Self::error(code, message)
        }
    }

    pub fn located_error(
        code: impl Into<String>,
        message: impl Into<String>,
        path: impl Into<String>,
        line: u32,
        column: u32,
    ) -> Self {
        Self {
            path: Some(path.into()),
            line: Some(line),
            column: Some(column),
            ..Self::error(code, message)
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ProofResponse {
    pub schema: String,
    pub verifier: String,
    pub version: String,
    pub status: ProofStatus,
    pub proof_obligation: String,
    pub source_fingerprint: String,
    pub files: Vec<FileResult>,
    pub source_imports: Vec<SourceImportResult>,
    pub external_contracts: Vec<ExternalContractResult>,
    pub cross_language_bindings: Vec<CrossLanguageBindingResult>,
    pub python_callable_bindings: Vec<PythonCallableBindingResult>,
    pub obligations: Vec<crate::vc::ObligationResult>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verifier_identity: Option<VerifierIdentity>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub typescript_toolchain: Option<TypeScriptToolchainIdentity>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub python_typechecker: Option<PythonTypecheckerIdentity>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solver: Option<SolverIdentity>,
    pub diagnostics: Vec<Diagnostic>,
}

impl ProofResponse {
    pub fn refused(request: &ProofRequest) -> Self {
        Self {
            schema: RESPONSE_SCHEMA.to_owned(),
            verifier: "maledictus".to_owned(),
            version: VERSION.to_owned(),
            status: ProofStatus::Refused,
            proof_obligation: request.proof_obligation.clone(),
            source_fingerprint: request.source_fingerprint.clone(),
            files: Vec::new(),
            source_imports: Vec::new(),
            external_contracts: Vec::new(),
            cross_language_bindings: Vec::new(),
            python_callable_bindings: Vec::new(),
            obligations: Vec::new(),
            verifier_identity: None,
            typescript_toolchain: None,
            python_typechecker: None,
            solver: None,
            diagnostics: Vec::new(),
        }
    }
}
