#![forbid(unsafe_code)]

pub mod call_binding;
pub mod conformance;
pub mod conformance_annotations;
pub mod dagcert_operations;
pub mod fragments;
pub mod kernel;
pub mod mixed_language;
mod obligation_kernel;
pub mod protocol;
pub mod python;
mod python_adt_wellformedness;
mod python_contract_positions;
pub mod python_contracts;
pub mod python_heap_contracts;
mod python_io_contracts;
pub mod python_io_wellformedness;
pub mod python_language_wellformedness;
mod python_obligation_leaks;
pub mod python_obligation_levels;
pub mod python_predicate_family_wellformedness;
mod python_private_fields;
pub mod python_proof_irrelevant_bindings;
pub mod python_reference_contracts;
mod python_sequence_builtins;
mod python_thread_wellformedness;
mod python_type_algebra_contracts;
mod python_type_algebra_kernel;
pub mod python_typecheck;
pub mod python_verifier_intrinsics;
pub mod solver;
pub mod typescript;
pub mod vc;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};

use kernel::{ExitEffect, check_exit_effects};
use protocol::{
    Diagnostic, ExternalContractResult, FileResult, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, PythonCallableBindingResult, PythonCallableProvider, PythonCallableProviderResult,
    SolverIdentity, SourceImportResult, VerifierIdentity,
};
pub use python_contract_positions::{
    ContractPositionFailure, InformationFlowVerificationProfile, validate_contract_positions,
    validate_contract_positions_with_profile,
};
use sha2::{Digest, Sha256};

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

struct ResolvedExternalContracts {
    scalar_by_adapter: BTreeMap<String, Vec<python_contracts::ImportedContractModule>>,
    reference_by_adapter:
        BTreeMap<String, Vec<python_reference_contracts::ImportedReferenceContractModule>>,
    heap_by_adapter: BTreeMap<String, Vec<python_heap_contracts::ImportedHeapContractModule>>,
    results: Vec<ExternalContractResult>,
}

struct ResolvedPythonCallableBindings {
    by_consumer: BTreeMap<String, Vec<dagcert_operations::ResolvedCallableBinding>>,
    source_provider_symbols: BTreeMap<String, BTreeSet<String>>,
    results: Vec<PythonCallableBindingResult>,
}

#[derive(Clone)]
struct PythonSourceUnit {
    path: String,
    module: String,
    source: String,
    sha256: String,
}

struct ResolvedSourceImports {
    by_path: BTreeMap<
        String,
        Result<Vec<python_contracts::ImportedContractModule>, python_contracts::ContractFailure>,
    >,
    edges: Vec<SourceImportResult>,
}

struct ResolvedReferenceSourceImports {
    by_path: BTreeMap<
        String,
        Result<
            Vec<python_reference_contracts::ImportedReferenceContractModule>,
            python_contracts::ContractFailure,
        >,
    >,
}

struct ResolvedHeapSourceImports {
    by_path: BTreeMap<
        String,
        Result<
            Vec<python_heap_contracts::ImportedHeapContractModule>,
            python_contracts::ContractFailure,
        >,
    >,
}

struct ResolvedOperationSourceImports {
    by_path: BTreeMap<
        String,
        Result<
            Vec<dagcert_operations::ImportedOperationModule>,
            dagcert_operations::OperationFailure,
        >,
    >,
}

#[derive(Clone)]
enum OperationSourceModuleState {
    Visiting,
    Done(Result<dagcert_operations::ImportedOperationModule, dagcert_operations::OperationFailure>),
}

struct OperationSourceModuleResolver<'a> {
    units: BTreeMap<String, PythonSourceUnit>,
    requested_symbols: BTreeMap<String, Vec<String>>,
    callable_bindings: &'a BTreeMap<String, Vec<dagcert_operations::ResolvedCallableBinding>>,
    states: BTreeMap<String, OperationSourceModuleState>,
}

#[derive(Clone)]
enum SourceModuleState {
    Visiting,
    Done(Result<python_contracts::ImportedContractModule, python_contracts::ContractFailure>),
}

struct SourceModuleResolver<'a> {
    units: BTreeMap<String, PythonSourceUnit>,
    external_by_adapter: &'a BTreeMap<String, Vec<python_contracts::ImportedContractModule>>,
    states: BTreeMap<String, SourceModuleState>,
}

#[derive(Clone)]
enum ReferenceSourceModuleState {
    Visiting,
    Done(
        Result<
            python_reference_contracts::ImportedReferenceContractModule,
            python_contracts::ContractFailure,
        >,
    ),
}

struct ReferenceSourceModuleResolver<'a> {
    units: BTreeMap<String, PythonSourceUnit>,
    external_by_adapter:
        &'a BTreeMap<String, Vec<python_reference_contracts::ImportedReferenceContractModule>>,
    states: BTreeMap<String, ReferenceSourceModuleState>,
}

#[derive(Clone)]
enum HeapSourceModuleState {
    Visiting,
    Done(
        Box<
            Result<
                python_heap_contracts::ImportedHeapContractModule,
                python_contracts::ContractFailure,
            >,
        >,
    ),
}

#[derive(Clone)]
enum HeapPackageInitializerState {
    Visiting,
    Done(Result<(), python_contracts::ContractFailure>),
}

struct HeapSourceModuleResolver<'a> {
    root: &'a Path,
    units: BTreeMap<String, PythonSourceUnit>,
    external_by_adapter:
        &'a BTreeMap<String, Vec<python_heap_contracts::ImportedHeapContractModule>>,
    states: BTreeMap<String, HeapSourceModuleState>,
    package_initializers: BTreeMap<String, HeapPackageInitializerState>,
}

/// Verify a request without trusting caller-supplied proof summaries.
///
/// Source parsing and effect inference are intentionally fail-closed until a language frontend
/// emits kernel-checked effects. Source hashing is implemented now because it is part of the
/// stable Dagcert backend boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FrontendDisposition {
    Supported,
    Refuted,
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct FrontendFileAnalysis {
    pub path: String,
    pub sha256: String,
    pub symbols: Vec<String>,
    pub scope: String,
    pub disposition: FrontendDisposition,
    pub fragment: Option<String>,
}

#[derive(Clone, Debug)]
pub struct FrontendAnalysis {
    pub disposition: FrontendDisposition,
    pub files: Vec<FrontendFileAnalysis>,
    pub source_imports: Vec<SourceImportResult>,
    pub external_contracts: Vec<ExternalContractResult>,
    pub python_callable_bindings: Vec<PythonCallableBindingResult>,
    pub obligations: Vec<vc::ObligationResult>,
    pub solver: Option<SolverIdentity>,
    pub diagnostics: Vec<Diagnostic>,
}

/// Analyze Python frontend behavior without performing issuance. This API deliberately omits
/// certificate schemas, source claims, verifier identities, and typechecker identities. The CLI
/// and protocol entry point call [`verify`] and cannot select this mode.
pub fn analyze_python_frontend(request: &ProofRequest) -> FrontendAnalysis {
    if request.files.iter().any(|file| file.language != "python") {
        return FrontendAnalysis {
            disposition: FrontendDisposition::Unsupported,
            files: Vec::new(),
            source_imports: Vec::new(),
            external_contracts: Vec::new(),
            python_callable_bindings: Vec::new(),
            obligations: Vec::new(),
            solver: None,
            diagnostics: vec![Diagnostic::error(
                "frontend.analysis.language",
                "the non-issuing analysis API accepts only Python source",
            )],
        };
    }
    FrontendAnalysis::from_response(verify_internal(request, false))
}

impl FrontendAnalysis {
    fn from_response(response: ProofResponse) -> Self {
        Self {
            disposition: frontend_disposition(&response.status),
            files: response
                .files
                .into_iter()
                .map(|file| FrontendFileAnalysis {
                    path: file.path,
                    sha256: file.sha256,
                    symbols: file.symbols,
                    scope: file.scope,
                    disposition: frontend_disposition(&file.result),
                    fragment: file.fragment,
                })
                .collect(),
            source_imports: response.source_imports,
            external_contracts: response.external_contracts,
            python_callable_bindings: response.python_callable_bindings,
            obligations: response.obligations,
            solver: response.solver,
            diagnostics: response.diagnostics,
        }
    }
}

fn frontend_disposition(status: &ProofStatus) -> FrontendDisposition {
    match status {
        ProofStatus::Proved => FrontendDisposition::Supported,
        ProofStatus::Refuted => FrontendDisposition::Refuted,
        ProofStatus::Refused => FrontendDisposition::Unsupported,
    }
}

pub fn verify(request: &ProofRequest) -> ProofResponse {
    verify_internal(request, true)
}

fn verify_internal(request: &ProofRequest, issuance: bool) -> ProofResponse {
    let mut response = ProofResponse::refused(request);

    if request.schema != PROTOCOL_SCHEMA {
        response.diagnostics.push(Diagnostic::error(
            "protocol.schema.unsupported",
            format!(
                "unsupported request schema {:?}; expected {:?}",
                request.schema, PROTOCOL_SCHEMA
            ),
        ));
        return response;
    }
    if request.proof_obligation != "no-undeclared-exceptional-exit" {
        response.diagnostics.push(Diagnostic::error(
            "obligation.unsupported",
            format!(
                "unsupported proof obligation {:?}",
                request.proof_obligation
            ),
        ));
        return response;
    }
    if request.files.is_empty() {
        response.diagnostics.push(Diagnostic::error(
            "source.files.empty",
            "at least one source file is required; an empty request is not a proof",
        ));
        return response;
    }
    if request.source_fingerprint.len() != 64
        || !request
            .source_fingerprint
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit())
    {
        response.diagnostics.push(Diagnostic::error(
            "source-fingerprint.invalid",
            "source_fingerprint must be a 64-character hexadecimal SHA-256 digest",
        ));
        return response;
    }
    if issuance {
        response.verifier_identity = match verifier_identity() {
            Ok(identity) => Some(identity),
            Err(message) => {
                response
                    .diagnostics
                    .push(Diagnostic::error("verifier.identity-unavailable", message));
                return response;
            }
        };
    }
    let root = match fs::canonicalize(&request.source_root) {
        Ok(root) => root,
        Err(error) => {
            response.diagnostics.push(Diagnostic::error(
                "source-root.unreadable",
                format!(
                    "cannot resolve source root {:?}: {error}",
                    request.source_root
                ),
            ));
            return response;
        }
    };

    let external_contracts = match resolve_external_contracts(&root, request) {
        Ok(mut resolved) => {
            response.external_contracts = std::mem::take(&mut resolved.results);
            resolved
        }
        Err(diagnostic) => {
            response.diagnostics.push(diagnostic);
            return response;
        }
    };
    let python_callable_bindings = match resolve_python_callable_bindings(
        &root,
        request,
        &external_contracts,
        &response.external_contracts,
    ) {
        Ok(resolved) => resolved,
        Err(diagnostic) => {
            response.diagnostics.push(diagnostic);
            return response;
        }
    };
    response.python_callable_bindings = python_callable_bindings.results.clone();
    let mixed_language = match mixed_language::resolve(&root, request) {
        Ok(resolved) => resolved,
        Err(error) => {
            let diagnostic = match (error.path, error.line, error.column) {
                (Some(path), Some(line), Some(column)) => {
                    Diagnostic::located_error(error.code, error.message, path, line, column)
                }
                (Some(path), _, _) => Diagnostic::file_error(error.code, error.message, path),
                (None, _, _) => Diagnostic::error(error.code, error.message),
            };
            response.diagnostics.push(diagnostic);
            return response;
        }
    };
    response.cross_language_bindings = mixed_language.results.clone();
    response.typescript_toolchain = mixed_language.toolchain.clone();
    if issuance {
        match python_typecheck::typecheck_request_sources_with_interfaces(
            &root,
            &request.files,
            &request.external_contract_overlays,
            &mixed_language.generated_interfaces,
        ) {
            Ok(Some(typecheck)) => {
                let passed = typecheck.passed();
                response.python_typechecker = Some(typecheck.identity);
                if !passed {
                    response.diagnostics.extend(typecheck.diagnostics);
                    return response;
                }
            }
            Ok(None) => {}
            Err(error) => {
                response
                    .diagnostics
                    .push(Diagnostic::error(error.code, error.message));
                return response;
            }
        }
    }
    let mut scalar_imports_by_adapter = external_contracts.scalar_by_adapter.clone();
    for (caller_path, module) in &mixed_language.caller_modules {
        scalar_imports_by_adapter
            .entry(caller_path.clone())
            .or_default()
            .push(module.clone());
    }
    let source_imports = match resolve_source_imports(
        &root,
        request,
        &scalar_imports_by_adapter,
        &mixed_language.caller_modules,
    ) {
        Ok(imports) => {
            response.source_imports = imports.edges;
            imports.by_path
        }
        Err(diagnostic) => {
            response.diagnostics.push(diagnostic);
            return response;
        }
    };
    let reference_source_imports = match resolve_reference_source_imports(
        &root,
        request,
        &external_contracts.reference_by_adapter,
    ) {
        Ok(imports) => imports.by_path,
        Err(diagnostic) => {
            response.diagnostics.push(diagnostic);
            return response;
        }
    };
    let heap_source_imports =
        match resolve_heap_source_imports(&root, request, &external_contracts.heap_by_adapter) {
            Ok(imports) => imports.by_path,
            Err(diagnostic) => {
                response.diagnostics.push(diagnostic);
                return response;
            }
        };
    let operation_source_imports =
        resolve_operation_source_imports(&root, request, &python_callable_bindings.by_consumer);

    // Fold/Unfold position checking needs the exact predicate identities exported by source
    // providers. Resolve and verify those providers first, then pass only their sealed predicate
    // catalogs into the consumer's source-position validator. Import spelling alone is never
    // trusted as proof that an operand is a predicate.
    for source in request
        .files
        .iter()
        .filter(|source| source.language == "python")
    {
        let path = match resolve_source_path(&root, &source.path) {
            Ok(path) => path,
            Err(message) => {
                response.diagnostics.push(Diagnostic::file_error(
                    "source.path.invalid",
                    message,
                    &source.path,
                ));
                return response;
            }
        };
        let bytes = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(error) => {
                response.diagnostics.push(Diagnostic::file_error(
                    "source.file.unreadable",
                    format!("cannot read source file: {error}"),
                    &source.path,
                ));
                return response;
            }
        };
        let text = match std::str::from_utf8(&bytes) {
            Ok(text) => text,
            Err(error) => {
                response.diagnostics.push(Diagnostic::file_error(
                    "source.file.not-utf8",
                    error.to_string(),
                    &source.path,
                ));
                return response;
            }
        };
        let imported_predicates = heap_source_imports
            .get(&source.path)
            .and_then(|result| result.as_ref().ok())
            .into_iter()
            .flatten()
            .filter_map(|module| {
                let names = module.source_predicate_names();
                (!names.is_empty()).then(|| {
                    python_contract_positions::SourcePredicateModule::new(module.module(), names)
                })
            })
            .collect::<Vec<_>>();
        if let Err(failure) =
            python_contract_positions::validate_contract_positions_with_source_predicates(
                text,
                &source.path,
                &imported_predicates,
            )
        {
            response.diagnostics.push(Diagnostic::located_error(
                failure.code,
                failure.message,
                &source.path,
                failure.line,
                failure.column,
            ));
            return response;
        }
    }

    for source in &request.files {
        let path = match resolve_source_path(&root, &source.path) {
            Ok(path) => path,
            Err(message) => {
                response.diagnostics.push(Diagnostic::file_error(
                    "source.path.invalid",
                    message,
                    &source.path,
                ));
                continue;
            }
        };
        let bytes = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(error) => {
                response.diagnostics.push(Diagnostic::file_error(
                    "source.file.unreadable",
                    format!("cannot read source file: {error}"),
                    &source.path,
                ));
                continue;
            }
        };
        response.files.push(FileResult {
            path: source.path.clone(),
            sha256: hex_digest(&bytes),
            symbols: source.symbols.clone(),
            scope: "all-source-symbol-bodies".to_owned(),
            result: ProofStatus::Refused,
            fragment: None,
            verified_interfaces: Vec::new(),
        });

        if mixed_language.provider_paths.contains(&source.path) {
            if let Some(file) = response.files.last_mut() {
                file.result = ProofStatus::Proved;
                file.fragment = Some(mixed_language::MIXED_LANGUAGE_FRAGMENT.to_owned());
                file.scope = "compiler-proved-provider-bound-to-python-call-edge".to_owned();
            }
            continue;
        }
        if let Some(provider_symbols) = python_callable_bindings
            .source_provider_symbols
            .get(&source.path)
        {
            let requested_symbols = source.symbols.iter().cloned().collect::<BTreeSet<_>>();
            if !requested_symbols.is_empty() && &requested_symbols == provider_symbols {
                if let Some(file) = response.files.last_mut() {
                    file.result = ProofStatus::Proved;
                    file.fragment = Some(fragments::DAGCERT_CLOSED_TYPED_OPERATIONS.to_owned());
                    file.scope =
                        "hash-bound-source-callback-signature-body-and-complete-exit-effects"
                            .to_owned();
                }
                continue;
            }
        }

        let language = source.language.as_str();
        if language != "python" && language != "javascript" && language != "typescript" {
            response.diagnostics.push(Diagnostic::file_error(
                "frontend.language.unsupported",
                format!("unsupported source language {language:?}"),
                &source.path,
            ));
            continue;
        }
        if language == "python" {
            match std::str::from_utf8(&bytes) {
                Ok(text) => {
                    if let Some(bindings) = python_callable_bindings.by_consumer.get(&source.path) {
                        match dagcert_operations::verify_operation_module_with_bindings(
                            text,
                            &source.path,
                            &source.symbols,
                            bindings,
                        ) {
                            Ok(_) => {
                                if let Some(file) = response.files.last_mut() {
                                    file.result = ProofStatus::Proved;
                                    file.fragment =
                                        Some(fragments::DAGCERT_CLOSED_TYPED_OPERATIONS.to_owned());
                                    file.scope = "hash-bound-operation-input-and-concrete-callable-provider-with-composed-exit-effects".to_owned();
                                }
                            }
                            Err(error) => response.diagnostics.push(Diagnostic::file_error(
                                error.code,
                                error.message,
                                &source.path,
                            )),
                        }
                        continue;
                    }
                    if source_imports.contains_key(&source.path)
                        || reference_source_imports.contains_key(&source.path)
                        || heap_source_imports.contains_key(&source.path)
                    {
                        let mut operation_error = None;
                        if let Some(resolved) = operation_source_imports.by_path.get(&source.path) {
                            match resolved {
                                Ok(imports) => {
                                    let bindings = python_callable_bindings
                                        .by_consumer
                                        .get(&source.path)
                                        .map_or(&[][..], Vec::as_slice);
                                    match dagcert_operations::verify_and_export_operation_module_with_imports(
                                        text,
                                        &source.path,
                                        &python_module_name(&source.path).unwrap_or_else(|_| source.path.clone()),
                                        &source.symbols,
                                        bindings,
                                        imports,
                                    ) {
                                        Ok(_) => {
                                            if let Some(file) = response.files.last_mut() {
                                                file.result = ProofStatus::Proved;
                                                file.fragment = Some(
                                                    fragments::DAGCERT_CLOSED_TYPED_OPERATIONS.to_owned(),
                                                );
                                            }
                                            continue;
                                        }
                                        Err(error) => operation_error = Some(error),
                                    }
                                }
                                Err(error) => operation_error = Some(error.clone()),
                            }
                        }
                        let scalar_error = match source_imports.get(&source.path) {
                            Some(Ok(imports)) => {
                                match python_contracts::verify_contract_module_with_imports(
                                    text,
                                    &source.path,
                                    &source.symbols,
                                    imports,
                                ) {
                                    Ok(verification) => {
                                        let fragment = if mixed_language
                                            .caller_paths
                                            .contains(&source.path)
                                        {
                                            mixed_language::MIXED_LANGUAGE_FRAGMENT
                                        } else if external_contracts
                                            .scalar_by_adapter
                                            .contains_key(&source.path)
                                        {
                                            fragments::TRANSITIVE_SOURCE_CHECKED_EXTERNAL_SCALAR_CONTRACTS
                                        } else {
                                            fragments::TRANSITIVE_SOURCE_SCALAR_CONTRACTS
                                        };
                                        record_scalar_verification(
                                            &mut response,
                                            &source.path,
                                            verification,
                                            fragment,
                                        );
                                        continue;
                                    }
                                    Err(error) => error,
                                }
                            }
                            Some(Err(error)) => error.clone(),
                            None => python_contracts::ContractFailure {
                                code: "frontend.python.contract-import.not-applicable",
                                message: format!(
                                    "source {:?} has no applicable scalar source-import proof",
                                    source.path
                                ),
                            },
                        };
                        let terminal_scalar_error = matches!(
                            scalar_error.code,
                            "frontend.python.contract-import.cycle"
                                | "frontend.python.contract-import.source-module-refuted"
                        )
                        .then(|| scalar_error.clone());
                        let mut fallback_error = scalar_error;
                        if let Some(resolved) = reference_source_imports.get(&source.path) {
                            match resolved {
                                Ok(imports) => {
                                    match python_reference_contracts::verify_reference_module_with_imports(
                                        text,
                                        &source.path,
                                        &source.symbols,
                                        imports,
                                    ) {
                                        Ok(verification) => {
                                            let fragment = if external_contracts
                                                .reference_by_adapter
                                                .contains_key(&source.path)
                                            {
                                                fragments::TRANSITIVE_SOURCE_CHECKED_EXTERNAL_NOMINAL_REFERENCE_CONTRACTS
                                            } else {
                                                fragments::TRANSITIVE_SOURCE_NOMINAL_REFERENCE_CONTRACTS
                                            };
                                            record_reference_verification(
                                                &mut response,
                                                &source.path,
                                                verification,
                                                fragment,
                                            );
                                            continue;
                                        }
                                        Err(error) => fallback_error = error,
                                    }
                                }
                                Err(error) => fallback_error = error.clone(),
                            }
                        }
                        if let Some(resolved) = heap_source_imports.get(&source.path) {
                            match resolved {
                                Ok(imports) => {
                                    let verification = if is_python_package_initializer(
                                        &source.path,
                                    ) && source.symbols.is_empty()
                                    {
                                        python_heap_contracts::verify_heap_package_initializer_with_imports(
                                            text,
                                            &source.path,
                                            imports,
                                        )
                                    } else {
                                        python_heap_contracts::verify_heap_module_with_imports(
                                            text,
                                            &source.path,
                                            &source.symbols,
                                            imports,
                                        )
                                    };
                                    match verification {
                                        Ok(verification) => {
                                            let fragment = if external_contracts
                                                .heap_by_adapter
                                                .contains_key(&source.path)
                                            {
                                                fragments::TRANSITIVE_SOURCE_CHECKED_EXTERNAL_HEAP_CONTRACTS
                                            } else {
                                                fragments::TRANSITIVE_SOURCE_HEAP_CONTRACTS
                                            };
                                            record_heap_verification(
                                                &mut response,
                                                &source.path,
                                                verification,
                                                fragment,
                                            );
                                            continue;
                                        }
                                        Err(error) => fallback_error = error,
                                    }
                                }
                                Err(error) => fallback_error = error.clone(),
                            }
                        }
                        if let Some(error) = terminal_scalar_error {
                            fallback_error = error;
                        } else if let Some(error) = operation_error {
                            fallback_error = python_contracts::ContractFailure {
                                code: error.code,
                                message: error.message,
                            };
                        }
                        response.diagnostics.push(Diagnostic::file_error(
                            fallback_error.code,
                            fallback_error.message,
                            &source.path,
                        ));
                        continue;
                    }
                    if let Some(externals) = external_contracts.heap_by_adapter.get(&source.path) {
                        match python_heap_contracts::verify_heap_module_with_imports(
                            text,
                            &source.path,
                            &source.symbols,
                            externals,
                        ) {
                            Ok(verification) => record_heap_verification(
                                &mut response,
                                &source.path,
                                verification,
                                fragments::CHECKED_EXTERNAL_HEAP_CONTRACTS,
                            ),
                            Err(error) => response.diagnostics.push(Diagnostic::file_error(
                                error.code,
                                error.message,
                                &source.path,
                            )),
                        }
                        continue;
                    }
                    if let Some(externals) =
                        external_contracts.reference_by_adapter.get(&source.path)
                    {
                        match python_reference_contracts::verify_reference_module_with_imports(
                            text,
                            &source.path,
                            &source.symbols,
                            externals,
                        ) {
                            Ok(verification) => {
                                record_reference_verification(
                                    &mut response,
                                    &source.path,
                                    verification,
                                    fragments::CHECKED_EXTERNAL_NOMINAL_REFERENCE_CONTRACTS,
                                );
                            }
                            Err(error) => response.diagnostics.push(Diagnostic::file_error(
                                error.code,
                                error.message,
                                &source.path,
                            )),
                        }
                        continue;
                    }
                    if let Some(externals) = external_contracts.scalar_by_adapter.get(&source.path)
                    {
                        match python_contracts::verify_contract_module_with_imports(
                            text,
                            &source.path,
                            &source.symbols,
                            externals,
                        ) {
                            Ok(verification) => {
                                record_scalar_verification(
                                    &mut response,
                                    &source.path,
                                    verification,
                                    fragments::CHECKED_EXTERNAL_SCALAR_CONTRACTS,
                                );
                            }
                            Err(error) => response.diagnostics.push(Diagnostic::file_error(
                                error.code,
                                error.message,
                                &source.path,
                            )),
                        }
                        continue;
                    }
                    if is_python_package_initializer(&source.path) && source.symbols.is_empty() {
                        match python_heap_contracts::verify_heap_package_initializer_with_imports(
                            text,
                            &source.path,
                            &[],
                        ) {
                            Ok(verification) => record_heap_verification(
                                &mut response,
                                &source.path,
                                verification,
                                fragments::HEAP_METHOD_CONTRACTS,
                            ),
                            Err(error) => response.diagnostics.push(Diagnostic::file_error(
                                error.code,
                                error.message,
                                &source.path,
                            )),
                        }
                        continue;
                    }
                    let dagcert_error = match dagcert_operations::verify_operation_module(
                        text,
                        &source.path,
                        &source.symbols,
                    ) {
                        Ok(_) => {
                            if let Some(file) = response.files.last_mut() {
                                file.result = ProofStatus::Proved;
                                file.fragment =
                                    Some(fragments::DAGCERT_CLOSED_TYPED_OPERATIONS.to_owned());
                            }
                            continue;
                        }
                        Err(error) => error,
                    };
                    match python::prove_closed_fragment(text, &source.path, &source.symbols) {
                        Ok(_) => {
                            if let Some(file) = response.files.last_mut() {
                                file.result = ProofStatus::Proved;
                                file.fragment = Some(fragments::CLOSED_TOTAL_FUNCTIONS.to_owned());
                            }
                        }
                        Err(closed_error) => {
                            match python::prove_caught_callable_fragment(
                                text,
                                &source.path,
                                &source.symbols,
                            ) {
                                Ok(_) => {
                                    if let Some(file) = response.files.last_mut() {
                                        file.result = ProofStatus::Proved;
                                        file.fragment = Some(
                                            fragments::CAUGHT_CALLABLE_DATACLASS_BOUNDARIES
                                                .to_owned(),
                                        );
                                    }
                                    continue;
                                }
                                Err(callable_error) => {
                                    match python_contracts::verify_contract_module(
                                        text,
                                        &source.path,
                                        &source.symbols,
                                    ) {
                                        Ok(verification) => {
                                            response.solver = Some(solver::identity());
                                            let violations: Vec<_> = verification
                                                .obligations
                                                .iter()
                                                .filter(|item| !item.satisfied())
                                                .cloned()
                                                .collect();
                                            response.obligations.extend(verification.obligations);
                                            if verification.passed {
                                                if let Some(file) = response.files.last_mut() {
                                                    file.result = ProofStatus::Proved;
                                                    file.fragment = Some(
                                                        fragments::SCALAR_NAGINI_CONTRACTS
                                                            .to_owned(),
                                                    );
                                                }
                                            } else {
                                                if let Some(file) = response.files.last_mut() {
                                                    file.result = ProofStatus::Refuted;
                                                    file.fragment = Some(
                                                        fragments::SCALAR_NAGINI_CONTRACTS
                                                            .to_owned(),
                                                    );
                                                }
                                                for item in violations {
                                                    let code = if item.expectation
                                                        == vc::ObligationExpectation::Refute
                                                    {
                                                        "refute.failed:refutation.true"
                                                    } else if item.id.contains(":undefined-local:")
                                                    {
                                                        "expression.undefined:undefined.local.variable"
                                                    } else if item
                                                        .id
                                                        .contains(":invariant-establishment:")
                                                    {
                                                        "invariant.not.established:assertion.false"
                                                    } else if item
                                                        .id
                                                        .contains(":invariant-preservation:")
                                                    {
                                                        "invariant.not.preserved:assertion.false"
                                                    } else if item
                                                        .id
                                                        .contains(":call-precondition:")
                                                    {
                                                        "call.precondition:assertion.false"
                                                    } else if item
                                                        .id
                                                        .contains(":application-precondition:")
                                                        || item.id.contains(
                                                            ":exception-undeclared:IndexError:",
                                                        )
                                                    {
                                                        "application.precondition:assertion.false"
                                                    } else if item
                                                        .id
                                                        .contains(":exception-undeclared:")
                                                    {
                                                        "exhale.failed:assertion.false"
                                                    } else if item
                                                        .id
                                                        .contains(":exception-postcondition:")
                                                        || item.id.contains(":postcondition:")
                                                        || item.id.contains(
                                                            ":function-totality:runtime-path:",
                                                        )
                                                    {
                                                        "postcondition.violated:assertion.false"
                                                    } else if item
                                                        .id
                                                        .contains(":function-totality:")
                                                        || item.id.contains(":pure-assert:")
                                                    {
                                                        "function.not.wellformed:assertion.false"
                                                    } else {
                                                        "assert.failed:assertion.false"
                                                    };
                                                    response.diagnostics.push(Diagnostic::located_error(
                                                    code,
                                                    format!(
                                                        "obligation {:?} expected {:?}, solver returned {:?}; model: {}",
                                                        item.id,
                                                        item.expectation,
                                                        item.status,
                                                        item.counterexample.as_deref().unwrap_or("unavailable")
                                                    ),
                                                    &source.path,
                                                    item.line,
                                                    item.column,
                                                ));
                                                }
                                            }
                                        }
                                        Err(contract_error) => {
                                            match python_heap_contracts::verify_heap_module(
                                                text,
                                                &source.path,
                                                &source.symbols,
                                            ) {
                                                Ok(verification) => {
                                                    response.solver = Some(solver::identity());
                                                    let violations: Vec<_> = verification
                                                        .obligations
                                                        .iter()
                                                        .filter(|item| !item.satisfied())
                                                        .cloned()
                                                        .collect();
                                                    response
                                                        .obligations
                                                        .extend(verification.obligations);
                                                    if let Some(file) = response.files.last_mut() {
                                                        file.result = if verification.passed {
                                                            ProofStatus::Proved
                                                        } else {
                                                            ProofStatus::Refuted
                                                        };
                                                        file.fragment = Some(
                                                            if verification.schema
                                                                == "maledictus-python-nominal-reference-verification/v1"
                                                            {
                                                                fragments::NOMINAL_REFERENCE_CONTRACTS
                                                            } else {
                                                                fragments::HEAP_METHOD_CONTRACTS
                                                            }
                                                            .to_owned(),
                                                        );
                                                    }
                                                    for item in violations {
                                                        let code = if item
                                                            .id
                                                            .contains(":undefined-global:")
                                                        {
                                                            "expression.undefined:undefined.global.name"
                                                        } else if item
                                                            .id
                                                            .contains(":undefined-base:")
                                                        {
                                                            "assert.failed:assertion.false"
                                                        } else if item.id.contains("@property:")
                                                            && item
                                                                .id
                                                                .contains(":field-permission:")
                                                        {
                                                            "function.not.wellformed:insufficient.permission"
                                                        } else if item
                                                            .id
                                                            .contains(":property-precondition:")
                                                        {
                                                            "application.precondition:insufficient.permission"
                                                        } else if item
                                                            .id
                                                            .contains(":undefined-local:")
                                                        {
                                                            "expression.undefined:undefined.local.variable"
                                                        } else if item.id.contains(
                                                            ":property-setter-precondition:",
                                                        ) {
                                                            "call.precondition:insufficient.permission"
                                                        } else if item
                                                            .id
                                                            .contains(":field-permission:")
                                                        {
                                                            "field.read:insufficient.permission"
                                                        } else if item
                                                            .id
                                                            .contains(":field-write-permission:")
                                                        {
                                                            "field.write:insufficient.permission"
                                                        } else if item.id.contains(
                                                            ":precondition-not-strengthened:permission",
                                                        ) {
                                                            "call.precondition:insufficient.permission"
                                                        } else if item.id.contains(
                                                            ":postcondition-not-weakened:permission",
                                                        ) || item.id.contains(
                                                            ":constructor-initialization-permission:",
                                                        ) {
                                                            "postcondition.violated:insufficient.permission"
                                                        } else if item.id.contains(
                                                            ":precondition-not-strengthened",
                                                        ) {
                                                            "call.precondition:assertion.false"
                                                        } else if item.id.contains(
                                                            ":postcondition-not-weakened",
                                                        ) {
                                                            "postcondition.violated:assertion.false"
                                                        } else if item.id.contains(
                                                            ":default-argument-compatible:",
                                                        ) {
                                                            "assert.failed:assertion.false"
                                                        } else if item
                                                            .id
                                                            .contains(":application-precondition:method-call-receiver-nonnull:")
                                                        {
                                                            "application.precondition:assertion.false"
                                                        } else if item
                                                            .id
                                                            .contains(":call-precondition:method-call-receiver-nonnull:")
                                                        {
                                                            "call.precondition:assertion.false"
                                                        } else if item
                                                            .id
                                                            .contains(":method-call-precondition:")
                                                            || item
                                                                .id
                                                                .contains(":call-precondition:")
                                                        {
                                                            if verification.schema
                                                                == "maledictus-python-nominal-reference-verification/v1"
                                                            {
                                                                "call.precondition:assertion.false"
                                                            } else {
                                                                "call.precondition:insufficient.permission"
                                                            }
                                                        } else if item
                                                            .id
                                                            .contains(":function-totality:")
                                                        {
                                                            "function.not.wellformed:assertion.false"
                                                        } else if item
                                                            .id
                                                            .contains(":postcondition:")
                                                        {
                                                            "postcondition.violated:assertion.false"
                                                        } else if item.id.contains(":assert:") {
                                                            "assert.failed:assertion.false"
                                                        } else {
                                                            "heap.obligation.failed"
                                                        };
                                                        response.diagnostics.push(
                                                        Diagnostic::located_error(
                                                            code,
                                                            format!(
                                                                "heap obligation {:?} returned {:?}; model: {}",
                                                                item.id,
                                                                item.status,
                                                                item.counterexample
                                                                    .as_deref()
                                                                    .unwrap_or("unavailable")
                                                            ),
                                                            &source.path,
                                                            item.line,
                                                            item.column,
                                                        ),
                                                    );
                                                    }
                                                }
                                                Err(heap_error) => {
                                                    let contract_source = text
                                                        .contains("nagini_contracts")
                                                        || text.contains("@Pure")
                                                        || text.contains("Requires(")
                                                        || text.contains("Ensures(")
                                                        || text.contains("Assert(");
                                                    let dagcert_source = text
                                                        .contains("@operation")
                                                        && text.contains("@dataclass");
                                                    let callable_source = text.contains("Callable")
                                                        && (text.contains("@dataclass")
                                                            || text.contains(
                                                                "@dataclasses.dataclass",
                                                            ));
                                                    let heap_source = text.contains("class ")
                                                        && (text.contains("Acc(")
                                                            || text.contains("self.")
                                                            || text.contains("isinstance(")
                                                            || python_heap_contracts::source_has_heap_statement_condition_feature(
                                                                text,
                                                                &source.path,
                                                            ));
                                                    let (code, message, byte_offset) =
                                                        if dagcert_source {
                                                            (
                                                                dagcert_error.code,
                                                                dagcert_error.message,
                                                                dagcert_error.byte_offset,
                                                            )
                                                        } else if callable_source {
                                                            (
                                                                callable_error.code,
                                                                callable_error.message,
                                                                None,
                                                            )
                                                        } else if heap_source {
                                                            (
                                                                heap_error.code,
                                                                heap_error.message,
                                                                None,
                                                            )
                                                        } else if contract_source {
                                                            (
                                                                contract_error.code,
                                                                contract_error.message,
                                                                None,
                                                            )
                                                        } else {
                                                            (
                                                                closed_error.code,
                                                                closed_error.message,
                                                                None,
                                                            )
                                                        };
                                                    let detail = match python::analyze_module(
                                                        text,
                                                        &source.path,
                                                    ) {
                                                        Ok(module) => format!(
                                                            "{}; parsed {} functions, {} classes, and {} typed feature uses",
                                                            message,
                                                            module.functions.len(),
                                                            module.classes.len(),
                                                            module.features.len()
                                                        ),
                                                        Err(_) => message,
                                                    };
                                                    let diagnostic =
                                                        if let Some(offset) = byte_offset {
                                                            let (line, column) =
                                                                source_location(text, offset);
                                                            Diagnostic::located_error(
                                                                code,
                                                                detail,
                                                                &source.path,
                                                                line,
                                                                column,
                                                            )
                                                        } else {
                                                            Diagnostic::file_error(
                                                                code,
                                                                detail,
                                                                &source.path,
                                                            )
                                                        };
                                                    response.diagnostics.push(diagnostic);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                Err(error) => response.diagnostics.push(Diagnostic::file_error(
                    "frontend.source.not-utf8",
                    format!("Python source is not UTF-8: {error}"),
                    &source.path,
                )),
            }
        } else if matches!(language, "javascript" | "typescript") {
            let verification = if language == "javascript" {
                typescript::verify_closed_javascript_module(&path, &source.symbols)
            } else {
                typescript::verify_closed_module(&path, &source.symbols)
            };
            match verification {
                Ok(verification) => {
                    let verified_interfaces =
                        typescript::verified_leaf_interfaces(&verification, &source.symbols);
                    response.typescript_toolchain = Some(verification.toolchain);
                    if let Some(file) = response.files.last_mut() {
                        file.result = ProofStatus::Proved;
                        file.fragment = Some(
                            if language == "javascript" {
                                typescript::JAVASCRIPT_FRAGMENT
                            } else {
                                typescript::TYPESCRIPT_FRAGMENT
                            }
                            .to_owned(),
                        );
                        file.verified_interfaces = verified_interfaces;
                    }
                }
                Err(error) => {
                    let diagnostic = match (error.line, error.column) {
                        (Some(line), Some(column)) => Diagnostic::located_error(
                            error.code,
                            error.message,
                            &source.path,
                            line,
                            column,
                        ),
                        _ => Diagnostic::file_error(error.code, error.message, &source.path),
                    };
                    response.diagnostics.push(diagnostic);
                }
            }
        } else {
            response.diagnostics.push(Diagnostic::file_error(
                "frontend.not-implemented",
                format!(
                    "the {language} source frontend is not implemented; Maledictus refuses to infer exception effects"
                ),
                &source.path,
            ));
        }
    }

    let unadvertised_fragments = response
        .files
        .iter()
        .enumerate()
        .filter_map(|(index, file)| {
            let fragment = file.fragment.as_deref()?;
            let source = request
                .files
                .iter()
                .find(|source| source.path == file.path)?;
            (!fragments::advertised_for_language(&source.language, fragment)).then(|| {
                (
                    index,
                    file.path.clone(),
                    source.language.clone(),
                    fragment.to_owned(),
                )
            })
        })
        .collect::<Vec<_>>();
    for (index, path, language, fragment) in unadvertised_fragments {
        response.files[index].result = ProofStatus::Refused;
        response.diagnostics.push(Diagnostic::file_error(
            "verifier.fragment.unadvertised",
            format!(
                "proof frontend selected fragment {fragment:?}, but capabilities do not advertise it for {language:?}"
            ),
            path,
        ));
    }

    if response.diagnostics.is_empty()
        && !response.files.is_empty()
        && response
            .files
            .iter()
            .all(|file| matches!(file.result, ProofStatus::Proved))
    {
        response.status = ProofStatus::Proved;
    } else if response
        .files
        .iter()
        .any(|file| matches!(file.result, ProofStatus::Refuted))
    {
        response.status = ProofStatus::Refuted;
    }
    response
}

fn source_location(source: &str, byte_offset: u32) -> (u32, u32) {
    let end = usize::try_from(byte_offset)
        .unwrap_or(source.len())
        .min(source.len());
    let prefix = &source.as_bytes()[..end];
    let line = 1 + prefix.iter().filter(|byte| **byte == b'\n').count() as u32;
    let column = prefix
        .iter()
        .rposition(|byte| *byte == b'\n')
        .map_or(prefix.len() + 1, |position| prefix.len() - position) as u32;
    (line, column)
}

fn resolve_source_imports(
    root: &Path,
    request: &ProofRequest,
    external_by_adapter: &BTreeMap<String, Vec<python_contracts::ImportedContractModule>>,
    forced_by_adapter: &BTreeMap<String, python_contracts::ImportedContractModule>,
) -> Result<ResolvedSourceImports, Diagnostic> {
    let units = collect_python_source_units(root, request)?;

    let mut resolver = SourceModuleResolver {
        units,
        external_by_adapter,
        states: BTreeMap::new(),
    };
    let paths = resolver
        .units
        .values()
        .map(|unit| (unit.path.clone(), unit.module.clone(), unit.source.clone()))
        .collect::<Vec<_>>();
    let mut by_path = BTreeMap::new();
    let mut edges = Vec::new();
    for (path, _module, source) in paths {
        let Ok(bindings) = python_contracts::source_contract_import_bindings(&source, &path) else {
            // Existing non-module fragments retain responsibility for files outside this narrow
            // absolute from-import composition fragment.
            continue;
        };
        let imported_names = bindings
            .iter()
            .map(|binding| binding.module.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if !imported_names.iter().any(|name| {
            resolver.units.contains_key(name)
                || forced_by_adapter
                    .get(&path)
                    .is_some_and(|module| module.module() == name)
        }) {
            continue;
        }
        for imported_name in imported_names
            .iter()
            .filter(|name| resolver.units.contains_key(*name))
        {
            let provider = &resolver.units[imported_name];
            let imported_symbols = bindings
                .iter()
                .filter(|binding| binding.module == *imported_name)
                .map(|binding| binding.imported_name.clone())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            edges.push(SourceImportResult {
                importer_path: path.clone(),
                module: imported_name.clone(),
                provider_path: provider.path.clone(),
                provider_sha256: provider.sha256.clone(),
                imported_symbols,
            });
        }
        let resolved = resolver.resolve_imports_for_path(&path, &imported_names);
        by_path.insert(path, resolved);
    }
    Ok(ResolvedSourceImports { by_path, edges })
}

fn collect_python_source_units(
    root: &Path,
    request: &ProofRequest,
) -> Result<BTreeMap<String, PythonSourceUnit>, Diagnostic> {
    let mut units = BTreeMap::new();
    for source in request
        .files
        .iter()
        .filter(|source| source.language == "python")
    {
        let path = resolve_source_path(root, &source.path).map_err(|message| {
            Diagnostic::file_error("source.path.invalid", message, &source.path)
        })?;
        let Ok(module) = python_module_name(&source.path) else {
            // A Python script need not have an importable module name. It remains eligible for
            // the ordinary single-file fragments, but cannot be selected as a source import.
            continue;
        };
        let bytes = fs::read(&path).map_err(|error| {
            Diagnostic::file_error(
                "source.file.unreadable",
                format!("cannot read source file while resolving imports: {error}"),
                &source.path,
            )
        })?;
        let text = std::str::from_utf8(&bytes).map_err(|error| {
            Diagnostic::file_error(
                "frontend.source.not-utf8",
                format!("Python source is not UTF-8: {error}"),
                &source.path,
            )
        })?;
        let unit = PythonSourceUnit {
            path: source.path.clone(),
            module: module.clone(),
            source: text.to_owned(),
            sha256: hex_digest(&bytes),
        };
        if let Some(previous) = units.insert(module.clone(), unit) {
            return Err(Diagnostic::file_error(
                "source.module-name.duplicate",
                format!(
                    "source files {:?} and {:?} both resolve to Python module {module:?}",
                    previous.path, source.path
                ),
                &source.path,
            ));
        }
    }
    Ok(units)
}

fn resolve_operation_source_imports(
    root: &Path,
    request: &ProofRequest,
    callable_bindings: &BTreeMap<String, Vec<dagcert_operations::ResolvedCallableBinding>>,
) -> ResolvedOperationSourceImports {
    let Ok(units) = collect_python_source_units(root, request) else {
        // The ordinary source resolvers report path and module-name failures before this
        // operation-specific resolver is consulted.
        return ResolvedOperationSourceImports {
            by_path: BTreeMap::new(),
        };
    };
    let requested_symbols = request
        .files
        .iter()
        .filter(|source| source.language == "python")
        .map(|source| (source.path.clone(), source.symbols.clone()))
        .collect();
    let mut resolver = OperationSourceModuleResolver {
        units,
        requested_symbols,
        callable_bindings,
        states: BTreeMap::new(),
    };
    let paths = resolver
        .units
        .values()
        .map(|unit| (unit.path.clone(), unit.source.clone()))
        .collect::<Vec<_>>();
    let mut by_path = BTreeMap::new();
    for (path, source) in paths {
        let Ok(bindings) = python_contracts::source_contract_import_bindings(&source, &path) else {
            continue;
        };
        let imported_modules = bindings
            .iter()
            .filter(|binding| resolver.units.contains_key(&binding.module))
            .map(|binding| binding.module.clone())
            .collect::<BTreeSet<_>>();
        if imported_modules.is_empty() {
            continue;
        }
        let resolved = imported_modules
            .iter()
            .map(|module| resolver.resolve_module(module))
            .collect();
        by_path.insert(path, resolved);
    }
    ResolvedOperationSourceImports { by_path }
}

impl OperationSourceModuleResolver<'_> {
    fn resolve_module(
        &mut self,
        module: &str,
    ) -> Result<dagcert_operations::ImportedOperationModule, dagcert_operations::OperationFailure>
    {
        if let Some(state) = self.states.get(module) {
            return match state {
                OperationSourceModuleState::Visiting => Err(dagcert_operations::OperationFailure {
                    code: "frontend.python.dagcert.source-import-cycle",
                    message: format!(
                        "Dagcert operation source import graph contains a cycle through module {module:?}"
                    ),
                    byte_offset: None,
                }),
                OperationSourceModuleState::Done(result) => result.clone(),
            };
        }
        self.states
            .insert(module.to_owned(), OperationSourceModuleState::Visiting);
        let unit = self
            .units
            .get(module)
            .expect("operation source resolution starts from registered modules")
            .clone();
        let result = (|| {
            let bindings =
                python_contracts::source_contract_import_bindings(&unit.source, &unit.path)
                    .map_err(|error| dagcert_operations::OperationFailure {
                        code: error.code,
                        message: error.message,
                        byte_offset: None,
                    })?;
            let imported_modules = bindings
                .iter()
                .filter(|binding| self.units.contains_key(&binding.module))
                .map(|binding| binding.module.clone())
                .collect::<BTreeSet<_>>()
                .iter()
                .map(|imported| self.resolve_module(imported))
                .collect::<Result<Vec<_>, _>>()?;
            let requested = self
                .requested_symbols
                .get(&unit.path)
                .map_or(&[][..], Vec::as_slice);
            let callable_bindings = self
                .callable_bindings
                .get(&unit.path)
                .map_or(&[][..], Vec::as_slice);
            let (_, exported) =
                dagcert_operations::verify_and_export_operation_module_with_imports(
                    &unit.source,
                    &unit.path,
                    &unit.module,
                    requested,
                    callable_bindings,
                    &imported_modules,
                )?;
            Ok(exported)
        })();
        self.states.insert(
            module.to_owned(),
            OperationSourceModuleState::Done(result.clone()),
        );
        result
    }
}

impl SourceModuleResolver<'_> {
    fn resolve_imports_for_path(
        &mut self,
        path: &str,
        imported_names: &[String],
    ) -> Result<Vec<python_contracts::ImportedContractModule>, python_contracts::ContractFailure>
    {
        let mut imports = Vec::new();
        for imported_name in imported_names {
            if self.units.contains_key(imported_name) {
                imports.push(self.resolve_module(imported_name)?);
            } else if let Some(external) = self.external_by_adapter.get(path).and_then(|modules| {
                modules
                    .iter()
                    .find(|module| module.module() == imported_name)
            }) {
                imports.push(external.clone());
            } else {
                return Err(python_contracts::ContractFailure {
                    code: "frontend.python.contract-import.unbound-module",
                    message: format!(
                        "source {path:?} imports module {imported_name:?}, but it is neither requested source nor an explicit external contract"
                    ),
                });
            }
        }
        Ok(imports)
    }

    fn resolve_module(
        &mut self,
        module: &str,
    ) -> Result<python_contracts::ImportedContractModule, python_contracts::ContractFailure> {
        if let Some(state) = self.states.get(module) {
            return match state {
                SourceModuleState::Visiting => Err(python_contracts::ContractFailure {
                    code: "frontend.python.contract-import.cycle",
                    message: format!(
                        "source contract import graph contains a cycle through module {module:?}"
                    ),
                }),
                SourceModuleState::Done(result) => result.clone(),
            };
        }
        self.states
            .insert(module.to_owned(), SourceModuleState::Visiting);
        let unit = self
            .units
            .get(module)
            .expect("source module resolution starts from registered modules")
            .clone();
        let result = (|| {
            let imported_names =
                python_contracts::source_contract_imports(&unit.source, &unit.path)?;
            let imports = self.resolve_imports_for_path(&unit.path, &imported_names)?;
            let (_, exported) = python_contracts::verify_and_export_source_contract_module(
                &unit.source,
                &unit.path,
                &unit.module,
                &imports,
            )?;
            Ok(exported)
        })();
        self.states
            .insert(module.to_owned(), SourceModuleState::Done(result.clone()));
        result
    }
}

fn resolve_reference_source_imports(
    root: &Path,
    request: &ProofRequest,
    external_by_adapter: &BTreeMap<
        String,
        Vec<python_reference_contracts::ImportedReferenceContractModule>,
    >,
) -> Result<ResolvedReferenceSourceImports, Diagnostic> {
    let units = collect_python_source_units(root, request)?;
    let mut resolver = ReferenceSourceModuleResolver {
        units,
        external_by_adapter,
        states: BTreeMap::new(),
    };
    let paths = resolver
        .units
        .values()
        .map(|unit| (unit.path.clone(), unit.source.clone()))
        .collect::<Vec<_>>();
    let mut by_path = BTreeMap::new();
    for (path, source) in paths {
        let Ok(imported_names) = python_contracts::source_contract_imports(&source, &path) else {
            continue;
        };
        if !imported_names
            .iter()
            .any(|name| resolver.units.contains_key(name))
        {
            continue;
        }
        let resolved = resolver.resolve_imports_for_path(&path, &imported_names);
        by_path.insert(path, resolved);
    }
    Ok(ResolvedReferenceSourceImports { by_path })
}

impl ReferenceSourceModuleResolver<'_> {
    fn resolve_imports_for_path(
        &mut self,
        path: &str,
        imported_names: &[String],
    ) -> Result<
        Vec<python_reference_contracts::ImportedReferenceContractModule>,
        python_contracts::ContractFailure,
    > {
        let mut imports = Vec::new();
        for imported_name in imported_names {
            if self.units.contains_key(imported_name) {
                imports.push(self.resolve_module(imported_name)?);
            } else if let Some(external) = self.external_by_adapter.get(path).and_then(|modules| {
                modules
                    .iter()
                    .find(|module| module.module() == imported_name)
            }) {
                imports.push(external.clone());
            } else {
                return Err(python_contracts::ContractFailure {
                    code: "frontend.python.references.unbound-module",
                    message: format!(
                        "source {path:?} imports reference module {imported_name:?}, but it is neither requested source nor an explicit external contract"
                    ),
                });
            }
        }
        Ok(imports)
    }

    fn resolve_module(
        &mut self,
        module: &str,
    ) -> Result<
        python_reference_contracts::ImportedReferenceContractModule,
        python_contracts::ContractFailure,
    > {
        if let Some(state) = self.states.get(module) {
            return match state {
                ReferenceSourceModuleState::Visiting => Err(python_contracts::ContractFailure {
                    code: "frontend.python.references.import-cycle",
                    message: format!(
                        "source nominal-reference import graph contains a cycle through {module:?}"
                    ),
                }),
                ReferenceSourceModuleState::Done(result) => result.clone(),
            };
        }
        self.states
            .insert(module.to_owned(), ReferenceSourceModuleState::Visiting);
        let unit = self
            .units
            .get(module)
            .expect("reference source module is registered")
            .clone();
        let result = (|| {
            let imported_names =
                python_contracts::source_contract_imports(&unit.source, &unit.path)?;
            let imports = self.resolve_imports_for_path(&unit.path, &imported_names)?;
            let (_, exported) =
                python_reference_contracts::verify_and_export_source_reference_module(
                    &unit.source,
                    &unit.path,
                    &unit.module,
                    &imports,
                )?;
            Ok(exported)
        })();
        self.states.insert(
            module.to_owned(),
            ReferenceSourceModuleState::Done(result.clone()),
        );
        result
    }
}

fn resolve_heap_source_imports(
    root: &Path,
    request: &ProofRequest,
    external_by_adapter: &BTreeMap<String, Vec<python_heap_contracts::ImportedHeapContractModule>>,
) -> Result<ResolvedHeapSourceImports, Diagnostic> {
    let units = collect_python_source_units(root, request)?;
    let mut resolver = HeapSourceModuleResolver {
        root,
        units,
        external_by_adapter,
        states: BTreeMap::new(),
        package_initializers: BTreeMap::new(),
    };
    let paths = resolver
        .units
        .values()
        .map(|unit| (unit.path.clone(), unit.module.clone(), unit.source.clone()))
        .collect::<Vec<_>>();
    let mut by_path = BTreeMap::new();
    for (path, module, source) in paths {
        let Ok(imported_names) = python_contracts::source_contract_imports(&source, &path) else {
            continue;
        };
        if !module.contains('.')
            && !imported_names
                .iter()
                .any(|name| resolver.units.contains_key(name))
        {
            continue;
        }
        let resolved = resolver
            .verify_parent_package_initializers(&module)
            .and_then(|()| resolver.resolve_imports_for_path(&path, &imported_names));
        by_path.insert(path, resolved);
    }
    Ok(ResolvedHeapSourceImports { by_path })
}

impl HeapSourceModuleResolver<'_> {
    fn resolve_imports_for_path(
        &mut self,
        path: &str,
        imported_names: &[String],
    ) -> Result<
        Vec<python_heap_contracts::ImportedHeapContractModule>,
        python_contracts::ContractFailure,
    > {
        let mut imports = Vec::new();
        for imported_name in imported_names {
            if self.units.contains_key(imported_name) {
                imports.push(self.resolve_module(imported_name)?);
            } else if let Some(external) = self.external_by_adapter.get(path).and_then(|modules| {
                modules
                    .iter()
                    .find(|module| module.module() == imported_name)
            }) {
                imports.push(external.clone());
            } else {
                return Err(python_contracts::ContractFailure {
                    code: "frontend.python.heap.unbound-module",
                    message: format!(
                        "source {path:?} imports heap module {imported_name:?}, but it is neither requested source nor an explicit external contract"
                    ),
                });
            }
        }
        Ok(imports)
    }

    fn resolve_module(
        &mut self,
        module: &str,
    ) -> Result<python_heap_contracts::ImportedHeapContractModule, python_contracts::ContractFailure>
    {
        if let Some(state) = self.states.get(module) {
            return match state {
                HeapSourceModuleState::Visiting => Err(python_contracts::ContractFailure {
                    code: "frontend.python.heap.import-cycle",
                    message: format!(
                        "source heap import graph contains a cycle through module {module:?}"
                    ),
                }),
                HeapSourceModuleState::Done(result) => result.as_ref().clone(),
            };
        }
        self.states
            .insert(module.to_owned(), HeapSourceModuleState::Visiting);
        let unit = self
            .units
            .get(module)
            .expect("heap source module is registered")
            .clone();
        let result = (|| {
            self.verify_parent_package_initializers(module)?;
            let imported_names =
                python_contracts::source_contract_imports(&unit.source, &unit.path)?;
            let imports = self.resolve_imports_for_path(&unit.path, &imported_names)?;
            let (_, exported) = python_heap_contracts::verify_and_export_source_heap_module(
                &unit.source,
                &unit.path,
                &unit.module,
                &imports,
            )?;
            Ok(exported)
        })();
        self.states.insert(
            module.to_owned(),
            HeapSourceModuleState::Done(Box::new(result.clone())),
        );
        result
    }

    fn verify_parent_package_initializers(
        &mut self,
        module: &str,
    ) -> Result<(), python_contracts::ContractFailure> {
        let components = module.split('.').collect::<Vec<_>>();
        for prefix_len in 1..components.len() {
            let package = components[..prefix_len].join(".");
            if let Some(unit) = self.units.get(&package) {
                let normalized = unit.path.replace('\\', "/");
                if !normalized.ends_with("/__init__.py") && normalized != "__init__.py" {
                    return Err(python_contracts::ContractFailure {
                        code: "frontend.python.heap.import-parent-not-package",
                        message: format!(
                            "source module {module:?} has non-package parent {package:?} at {:?}",
                            unit.path
                        ),
                    });
                }
                self.verify_package_initializer(&package)?;
                continue;
            }

            let mut initializer = self.root.to_path_buf();
            for component in &components[..prefix_len] {
                initializer.push(component);
            }
            let sibling_module = initializer.with_extension("py");
            initializer.push("__init__.py");
            if initializer.exists() {
                return Err(python_contracts::ContractFailure {
                    code: "frontend.python.heap.package-initializer-not-requested",
                    message: format!(
                        "source module {module:?} requires package initializer {} to be explicitly requested and hash-bound",
                        initializer.display()
                    ),
                });
            }
            if sibling_module.exists() {
                return Err(python_contracts::ContractFailure {
                    code: "frontend.python.heap.import-parent-not-package",
                    message: format!(
                        "source module {module:?} cannot have module file {} as package parent {package:?}",
                        sibling_module.display()
                    ),
                });
            }
        }
        Ok(())
    }

    fn verify_package_initializer(
        &mut self,
        package: &str,
    ) -> Result<(), python_contracts::ContractFailure> {
        if let Some(state) = self.package_initializers.get(package) {
            return match state {
                HeapPackageInitializerState::Visiting => Err(python_contracts::ContractFailure {
                    code: "frontend.python.heap.package-initializer-cycle",
                    message: format!(
                        "source heap package initializer graph contains a cycle through {package:?}"
                    ),
                }),
                HeapPackageInitializerState::Done(result) => result.clone(),
            };
        }
        self.package_initializers
            .insert(package.to_owned(), HeapPackageInitializerState::Visiting);
        let unit = self
            .units
            .get(package)
            .expect("requested package initializer is a registered source unit")
            .clone();
        let result = (|| {
            let imported_names =
                python_contracts::source_contract_imports(&unit.source, &unit.path)?;
            let imports = self.resolve_imports_for_path(&unit.path, &imported_names)?;
            let verification = python_heap_contracts::verify_heap_package_initializer_with_imports(
                &unit.source,
                &unit.path,
                &imports,
            )?;
            if !verification.passed {
                return Err(python_contracts::ContractFailure {
                    code: "frontend.python.heap.package-initializer-refuted",
                    message: format!(
                        "source heap package initializer {package:?} contains a refuted obligation"
                    ),
                });
            }
            Ok(())
        })();
        self.package_initializers.insert(
            package.to_owned(),
            HeapPackageInitializerState::Done(result.clone()),
        );
        result
    }
}

fn python_module_name(path: &str) -> Result<String, String> {
    let normalized = path.replace('\\', "/");
    let Some(without_suffix) = normalized.strip_suffix(".py") else {
        return Err(format!("Python source path must end in .py: {path:?}"));
    };
    let mut components = without_suffix.split('/').collect::<Vec<_>>();
    if components
        .last()
        .is_some_and(|component| *component == "__init__")
    {
        components.pop();
    }
    if components.is_empty()
        || components.iter().any(|component| {
            component.is_empty()
                || !component
                    .chars()
                    .next()
                    .is_some_and(|character| character == '_' || character.is_alphabetic())
                || !component
                    .chars()
                    .all(|character| character == '_' || character.is_alphanumeric())
        })
    {
        return Err(format!(
            "source path {path:?} cannot be mapped to a dotted Python module below source_root"
        ));
    }
    Ok(components.join("."))
}

fn is_python_package_initializer(path: &str) -> bool {
    let normalized = path.replace('\\', "/");
    normalized == "__init__.py" || normalized.ends_with("/__init__.py")
}

fn resolve_python_callable_bindings(
    root: &Path,
    request: &ProofRequest,
    external_contracts: &ResolvedExternalContracts,
    external_results: &[ExternalContractResult],
) -> Result<ResolvedPythonCallableBindings, Diagnostic> {
    let mut ids = BTreeSet::new();
    let mut targets = BTreeSet::new();
    let mut by_consumer = BTreeMap::<String, Vec<_>>::new();
    let mut source_provider_symbols = BTreeMap::<String, BTreeSet<String>>::new();
    let mut results = Vec::new();
    for binding in &request.python_callable_bindings {
        if binding.id.is_empty() || !ids.insert(binding.id.clone()) {
            return Err(Diagnostic::file_error(
                "python-callable-binding.id-invalid",
                "each Python callable binding requires a unique nonempty id",
                &binding.consumer_path,
            ));
        }
        if !targets.insert((
            binding.consumer_path.clone(),
            binding.operation_symbol.clone(),
            binding.input_record.clone(),
            binding.field.clone(),
        )) {
            return Err(Diagnostic::file_error(
                "python-callable-binding.target-duplicate",
                format!(
                    "operation callable target {}.{} is bound more than once for {:?}",
                    binding.input_record, binding.field, binding.operation_symbol
                ),
                &binding.consumer_path,
            ));
        }
        if [
            binding.operation_symbol.as_str(),
            binding.input_record.as_str(),
            binding.field.as_str(),
        ]
        .iter()
        .any(|name| !is_plain_python_identifier(name))
        {
            return Err(Diagnostic::file_error(
                "python-callable-binding.target-invalid",
                "operation_symbol, input_record, and field must be Python identifiers",
                &binding.consumer_path,
            ));
        }
        let Some(consumer) = request
            .files
            .iter()
            .find(|source| source.path == binding.consumer_path)
        else {
            return Err(Diagnostic::file_error(
                "python-callable-binding.consumer-not-requested",
                "consumer_path must exactly name a requested source file",
                &binding.consumer_path,
            ));
        };
        if consumer.language != "python" {
            return Err(Diagnostic::file_error(
                "python-callable-binding.consumer-language",
                "callable-valued Dagcert operations currently require a Python consumer",
                &binding.consumer_path,
            ));
        }
        let consumer_path =
            resolve_source_path(root, &binding.consumer_path).map_err(|message| {
                Diagnostic::file_error(
                    "python-callable-binding.consumer-path-invalid",
                    message,
                    &binding.consumer_path,
                )
            })?;
        let consumer_bytes = fs::read(&consumer_path).map_err(|error| {
            Diagnostic::file_error(
                "python-callable-binding.consumer-unreadable",
                format!("cannot read callable consumer: {error}"),
                &binding.consumer_path,
            )
        })?;
        let consumer_sha256 = hex_digest(&consumer_bytes);

        let (contract, source_provider, provider_description, provider_result, scope) =
            match &binding.provider {
                PythonCallableProvider::Source { path, symbol } => {
                    if !is_plain_python_identifier(symbol) {
                        return Err(Diagnostic::file_error(
                            "python-callable-binding.provider-symbol-invalid",
                            "source callback symbol must be a Python identifier",
                            path,
                        ));
                    }
                    let Some(provider) = request.files.iter().find(|source| source.path == *path)
                    else {
                        return Err(Diagnostic::file_error(
                            "python-callable-binding.provider-not-requested",
                            "source callback provider must exactly name a requested source file",
                            path,
                        ));
                    };
                    if provider.language != "python" {
                        return Err(Diagnostic::file_error(
                            "python-callable-binding.provider-language",
                            "source callback provider must be Python",
                            path,
                        ));
                    }
                    let provider_path = resolve_source_path(root, path).map_err(|message| {
                        Diagnostic::file_error(
                            "python-callable-binding.provider-path-invalid",
                            message,
                            path,
                        )
                    })?;
                    let bytes = fs::read(&provider_path).map_err(|error| {
                        Diagnostic::file_error(
                            "python-callable-binding.provider-unreadable",
                            format!("cannot read source callback provider: {error}"),
                            path,
                        )
                    })?;
                    let text = std::str::from_utf8(&bytes).map_err(|error| {
                        Diagnostic::file_error(
                            "python-callable-binding.provider-not-utf8",
                            error.to_string(),
                            path,
                        )
                    })?;
                    let contract = dagcert_operations::analyze_source_callable(text, path, symbol)
                        .map_err(|error| Diagnostic::file_error(error.code, error.message, path))?;
                    source_provider_symbols
                        .entry(path.clone())
                        .or_default()
                        .insert(symbol.clone());
                    (
                        contract,
                        Some(dagcert_operations::SourceCallableProvider {
                            path: path.clone(),
                            symbol: symbol.clone(),
                        }),
                        format!("source {path}:{symbol}"),
                        PythonCallableProviderResult::Source {
                            path: path.clone(),
                            sha256: hex_digest(&bytes),
                            symbol: symbol.clone(),
                        },
                        "source-callback-signature-body-and-complete-normal-exception-outcomes-checked-and-composed",
                    )
                }
                PythonCallableProvider::ExternalContract { module, symbol } => {
                    if module.is_empty()
                        || module
                            .split('.')
                            .any(|part| !is_plain_python_identifier(part))
                        || !is_plain_python_identifier(symbol)
                    {
                        return Err(Diagnostic::file_error(
                            "python-callable-binding.external-provider-invalid",
                            "external callback module and symbol must be dotted Python identifiers",
                            &binding.consumer_path,
                        ));
                    }
                    let Some(contract_module) = external_contracts
                        .scalar_by_adapter
                        .get(&binding.consumer_path)
                        .into_iter()
                        .flatten()
                        .find(|candidate| candidate.module() == module)
                    else {
                        return Err(Diagnostic::file_error(
                            "python-callable-binding.external-contract-missing",
                            format!(
                                "consumer has no checked scalar external overlay for module {module:?}"
                            ),
                            &binding.consumer_path,
                        ));
                    };
                    let imported = contract_module.callable_contract(symbol).map_err(|error| {
                        Diagnostic::file_error(error.code, error.message, &binding.consumer_path)
                    })?;
                    if imported.has_preconditions {
                        return Err(Diagnostic::file_error(
                            "python-callable-binding.external-precondition-unsupported",
                            "external callback preconditions must be proved at the invocation; this operation tranche does not yet lower them",
                            &binding.consumer_path,
                        ));
                    }
                    let parameters = imported
                        .positional_parameter_sorts
                        .iter()
                        .map(callable_primitive_from_sort)
                        .collect::<Result<Vec<_>, _>>()?;
                    let return_type = callable_primitive_from_sort(&imported.return_sort)?;
                    let Some(result) = external_results.iter().find(|result| {
                        result.adapter_path == binding.consumer_path && result.module == *module
                    }) else {
                        return Err(Diagnostic::file_error(
                            "python-callable-binding.external-result-missing",
                            "checked external contract did not produce hash-bound evidence",
                            &binding.consumer_path,
                        ));
                    };
                    (
                        dagcert_operations::CallableContract {
                            parameters,
                            return_type,
                            raised_exceptions: imported.declared_exceptions,
                        },
                        None,
                        format!("external contract {module}.{symbol}"),
                        PythonCallableProviderResult::ExternalContract {
                            module: module.clone(),
                            stub_path: result.stub_path.clone(),
                            stub_sha256: result.sha256.clone(),
                            symbol: symbol.clone(),
                        },
                        "external-provider-conformance-assumed-by-explicit-hash-bound-contract; fixed-signature-and-declared-exception-outcomes-composed",
                    )
                }
            };
        by_consumer
            .entry(binding.consumer_path.clone())
            .or_default()
            .push(dagcert_operations::ResolvedCallableBinding {
                operation: binding.operation_symbol.clone(),
                input_record: binding.input_record.clone(),
                field: binding.field.clone(),
                provider_description,
                source_provider,
                contract,
            });
        results.push(PythonCallableBindingResult {
            id: binding.id.clone(),
            consumer_path: binding.consumer_path.clone(),
            consumer_sha256,
            operation_symbol: binding.operation_symbol.clone(),
            input_record: binding.input_record.clone(),
            field: binding.field.clone(),
            provider: provider_result,
            scope: scope.to_owned(),
        });
    }
    Ok(ResolvedPythonCallableBindings {
        by_consumer,
        source_provider_symbols,
        results,
    })
}

fn callable_primitive_from_sort(
    sort: &vc::Sort,
) -> Result<dagcert_operations::CallablePrimitiveType, Diagnostic> {
    match sort {
        vc::Sort::Int => Ok(dagcert_operations::CallablePrimitiveType::Int),
        vc::Sort::Float => Ok(dagcert_operations::CallablePrimitiveType::Float),
        vc::Sort::Bool => Ok(dagcert_operations::CallablePrimitiveType::Bool),
        vc::Sort::String => Ok(dagcert_operations::CallablePrimitiveType::Str),
        _ => Err(Diagnostic::error(
            "python-callable-binding.external-type-unsupported",
            format!("external callback type {sort:?} is outside the primitive operation fragment"),
        )),
    }
}

fn is_plain_python_identifier(value: &str) -> bool {
    let mut characters = value.chars();
    characters
        .next()
        .is_some_and(|character| character == '_' || character.is_alphabetic())
        && characters.all(|character| character == '_' || character.is_alphanumeric())
}

fn resolve_external_contracts(
    root: &Path,
    request: &ProofRequest,
) -> Result<ResolvedExternalContracts, Diagnostic> {
    let source_paths = request
        .files
        .iter()
        .map(|source| source.path.as_str())
        .collect::<BTreeSet<_>>();
    let mut seen = BTreeSet::new();
    let mut scalar_modules = BTreeMap::<String, Vec<_>>::new();
    let mut reference_modules = BTreeMap::<String, Vec<_>>::new();
    let mut heap_modules = BTreeMap::<String, Vec<_>>::new();
    let mut results = Vec::new();
    for overlay in &request.external_contract_overlays {
        let Some(adapter) = request
            .files
            .iter()
            .find(|source| source.path == overlay.adapter_path)
        else {
            return Err(Diagnostic::file_error(
                "external-contract.adapter-not-requested",
                "external contract adapter_path must exactly name a requested source file",
                &overlay.adapter_path,
            ));
        };
        if adapter.language != "python" {
            return Err(Diagnostic::file_error(
                "external-contract.language-unsupported",
                "checked external contracts currently support only Python adapters",
                &overlay.adapter_path,
            ));
        }
        if source_paths.contains(overlay.stub_path.as_str()) {
            return Err(Diagnostic::file_error(
                "external-contract.stub-is-source",
                "a contract-only stub cannot also be requested as verified application source",
                &overlay.stub_path,
            ));
        }
        if !seen.insert((overlay.adapter_path.clone(), overlay.module.clone())) {
            return Err(Diagnostic::file_error(
                "external-contract.duplicate-overlay",
                format!(
                    "adapter {:?} has multiple overlays for module {:?}",
                    overlay.adapter_path, overlay.module
                ),
                &overlay.stub_path,
            ));
        }
        let stub_path = resolve_source_path(root, &overlay.stub_path).map_err(|message| {
            Diagnostic::file_error(
                "external-contract.stub-path-invalid",
                message,
                &overlay.stub_path,
            )
        })?;
        let bytes = fs::read(&stub_path).map_err(|error| {
            Diagnostic::file_error(
                "external-contract.stub-unreadable",
                format!("cannot read external contract stub: {error}"),
                &overlay.stub_path,
            )
        })?;
        let text = std::str::from_utf8(&bytes).map_err(|error| {
            Diagnostic::file_error(
                "external-contract.stub-not-utf8",
                format!("external contract stub is not UTF-8: {error}"),
                &overlay.stub_path,
            )
        })?;
        match python_contracts::parse_external_contract_module(
            text,
            &overlay.stub_path,
            &overlay.module,
        ) {
            Ok(contract) => {
                let functions = contract.function_names();
                let exception_types = contract.exception_type_names();
                let declared_exceptions = contract.declared_exception_types();
                let scope = match &overlay.exception_policy {
                    protocol::ExternalExceptionPolicy::AssumeNoException
                        if declared_exceptions.is_empty() =>
                    {
                        "provider-import-conformance-and-normal-return-assumed; adapter-symbol-binding-call-sites-and-preconditions-verified"
                    }
                    protocol::ExternalExceptionPolicy::DeclaredByExsures
                        if !declared_exceptions.is_empty() =>
                    {
                        "provider-import-and-contract-conformance-assumed; exsures-outcome-union-propagated; adapter-symbol-binding-call-sites-and-preconditions-verified"
                    }
                    protocol::ExternalExceptionPolicy::AssumeNoException => {
                        return Err(Diagnostic::file_error(
                            "external-contract.exception-policy-mismatch",
                            "assume-no-exception cannot be used with an external contract that declares Exsures outcomes",
                            &overlay.stub_path,
                        ));
                    }
                    protocol::ExternalExceptionPolicy::DeclaredByExsures => {
                        return Err(Diagnostic::file_error(
                            "external-contract.exception-policy-mismatch",
                            "declared-by-exsures requires at least one typed Exsures outcome",
                            &overlay.stub_path,
                        ));
                    }
                };
                results.push(ExternalContractResult {
                    adapter_path: overlay.adapter_path.clone(),
                    module: overlay.module.clone(),
                    stub_path: overlay.stub_path.clone(),
                    sha256: hex_digest(&bytes),
                    functions,
                    nominal_types: Vec::new(),
                    heap_types: Vec::new(),
                    exception_types,
                    exception_policy: overlay.exception_policy.clone(),
                    declared_exceptions,
                    scope: scope.to_owned(),
                });
                scalar_modules
                    .entry(overlay.adapter_path.clone())
                    .or_default()
                    .push(contract);
            }
            Err(scalar_error) => {
                match python_reference_contracts::parse_external_reference_contract_module(
                    text,
                    &overlay.stub_path,
                    &overlay.module,
                ) {
                    Ok(contract) => {
                        if !matches!(
                            overlay.exception_policy,
                            protocol::ExternalExceptionPolicy::AssumeNoException
                        ) {
                            return Err(Diagnostic::file_error(
                                "external-contract.exception-policy-mismatch",
                                "nominal reference contracts currently require assume-no-exception",
                                &overlay.stub_path,
                            ));
                        }
                        let functions = contract.function_names();
                        let nominal_types = contract.type_names();
                        results.push(ExternalContractResult {
                            adapter_path: overlay.adapter_path.clone(),
                            module: overlay.module.clone(),
                            stub_path: overlay.stub_path.clone(),
                            sha256: hex_digest(&bytes),
                            functions,
                            nominal_types,
                            heap_types: Vec::new(),
                            exception_types: Vec::new(),
                            exception_policy: overlay.exception_policy.clone(),
                            declared_exceptions: Vec::new(),
                            scope: "provider-import-conformance-and-nominal-return-types-assumed; adapter-symbol-binding-and-nominal-call-types-verified".to_owned(),
                        });
                        reference_modules
                            .entry(overlay.adapter_path.clone())
                            .or_default()
                            .push(contract);
                    }
                    Err(_) => {
                        let contract = python_heap_contracts::parse_external_heap_contract_module(
                            text,
                            &overlay.stub_path,
                            &overlay.module,
                        )
                        .map_err(|heap_error| {
                            let (code, message) = if matches!(
                                heap_error.code,
                                "frontend.python.heap.external-old-unsupported"
                                    | "frontend.python.heap.result-identity-external-unsupported"
                            ) {
                                (heap_error.code, heap_error.message)
                            } else {
                                (scalar_error.code, scalar_error.message)
                            };
                            Diagnostic::file_error(code, message, &overlay.stub_path)
                        })?;
                        if !matches!(
                            overlay.exception_policy,
                            protocol::ExternalExceptionPolicy::AssumeNoException
                        ) {
                            return Err(Diagnostic::file_error(
                                "external-contract.exception-policy-mismatch",
                                "heap contracts currently require assume-no-exception",
                                &overlay.stub_path,
                            ));
                        }
                        let heap_types = contract.qualified_class_names();
                        results.push(ExternalContractResult {
                            adapter_path: overlay.adapter_path.clone(),
                            module: overlay.module.clone(),
                            stub_path: overlay.stub_path.clone(),
                            sha256: hex_digest(&bytes),
                            functions: Vec::new(),
                            nominal_types: Vec::new(),
                            heap_types,
                            exception_types: Vec::new(),
                            exception_policy: overlay.exception_policy.clone(),
                            declared_exceptions: Vec::new(),
                            scope: "provider-import-and-heap-contract-conformance-assumed; class-layout-constructor-method-and-permission-effects-checked-at-adapter".to_owned(),
                        });
                        heap_modules
                            .entry(overlay.adapter_path.clone())
                            .or_default()
                            .push(contract);
                    }
                }
            }
        }
    }
    if let Some(adapter) = scalar_modules
        .keys()
        .chain(reference_modules.keys())
        .find(|adapter| {
            let count = usize::from(scalar_modules.contains_key(*adapter))
                + usize::from(reference_modules.contains_key(*adapter))
                + usize::from(heap_modules.contains_key(*adapter));
            count > 1
        })
    {
        return Err(Diagnostic::file_error(
            "external-contract.mixed-fragments-unsupported",
            "one adapter cannot yet combine scalar, nominal-reference, and heap external contracts",
            adapter,
        ));
    }
    Ok(ResolvedExternalContracts {
        scalar_by_adapter: scalar_modules,
        reference_by_adapter: reference_modules,
        heap_by_adapter: heap_modules,
        results,
    })
}

fn record_scalar_verification(
    response: &mut ProofResponse,
    path: &str,
    verification: python_contracts::ContractVerification,
    fragment: &str,
) {
    response.solver = Some(solver::identity());
    let violations: Vec<_> = verification
        .obligations
        .iter()
        .filter(|item| !item.satisfied())
        .cloned()
        .collect();
    response.obligations.extend(verification.obligations);
    if let Some(file) = response.files.last_mut() {
        file.result = if verification.passed {
            ProofStatus::Proved
        } else {
            ProofStatus::Refuted
        };
        file.fragment = Some(fragment.to_owned());
    }
    if !verification.passed {
        for item in violations {
            let code = if item.expectation == vc::ObligationExpectation::Refute {
                "refute.failed:refutation.true"
            } else if item.id.contains(":undefined-local:") {
                "expression.undefined:undefined.local.variable"
            } else if item.id.contains(":invariant-establishment:") {
                "invariant.not.established:assertion.false"
            } else if item.id.contains(":invariant-preservation:") {
                "invariant.not.preserved:assertion.false"
            } else if item.id.contains(":call-precondition:") {
                "call.precondition:assertion.false"
            } else if item.id.contains(":exception-undeclared:IndexError:") {
                "application.precondition:assertion.false"
            } else if item.id.contains(":exception-undeclared:") {
                "exhale.failed:assertion.false"
            } else if item.id.contains(":exception-postcondition:")
                || item.id.contains(":postcondition:")
                || item.id.contains(":function-totality:runtime-path:")
            {
                "postcondition.violated:assertion.false"
            } else if item.id.contains(":function-totality:") || item.id.contains(":pure-assert:") {
                "function.not.wellformed:assertion.false"
            } else {
                "assert.failed:assertion.false"
            };
            response.diagnostics.push(Diagnostic::located_error(
                code,
                format!(
                    "obligation {:?} expected {:?}, solver returned {:?}; model: {}",
                    item.id,
                    item.expectation,
                    item.status,
                    item.counterexample.as_deref().unwrap_or("unavailable")
                ),
                path,
                item.line,
                item.column,
            ));
        }
    }
}

/// Public kernel seam used by frontends and the Lean correspondence tests.
pub fn verify_effects(effects: &[ExitEffect], allowed_exceptions: &[String]) -> bool {
    check_exit_effects(effects, allowed_exceptions).is_ok()
}

fn record_reference_verification(
    response: &mut ProofResponse,
    path: &str,
    verification: python_reference_contracts::ReferenceContractVerification,
    fragment: &str,
) {
    response.solver = Some(solver::identity());
    let violations = verification
        .obligations
        .iter()
        .filter(|item| !item.satisfied())
        .cloned()
        .collect::<Vec<_>>();
    response.obligations.extend(verification.obligations);
    if let Some(file) = response.files.last_mut() {
        file.result = if verification.passed {
            ProofStatus::Proved
        } else {
            ProofStatus::Refuted
        };
        file.fragment = Some(fragment.to_owned());
    }
    if !verification.passed {
        for item in violations {
            let code =
                if item.id.contains(":call-precondition:") || item.id.contains(":return-type:") {
                    "call.precondition:assertion.false"
                } else if item.id.contains(":reference-return-totality") {
                    "function.not.wellformed:assertion.false"
                } else {
                    "assert.failed:assertion.false"
                };
            response.diagnostics.push(Diagnostic::located_error(
                code,
                format!(
                    "nominal-reference obligation {:?} was refuted; model: {}",
                    item.id,
                    serde_json::to_string(&item.counterexample)
                        .unwrap_or_else(|_| "null".to_owned())
                ),
                path,
                item.line,
                item.column,
            ));
        }
    }
}

fn record_heap_verification(
    response: &mut ProofResponse,
    path: &str,
    verification: python_heap_contracts::HeapContractVerification,
    fragment: &str,
) {
    response.solver = Some(solver::identity());
    let violations = verification
        .obligations
        .iter()
        .filter(|item| !item.satisfied())
        .cloned()
        .collect::<Vec<_>>();
    response.obligations.extend(verification.obligations);
    if let Some(file) = response.files.last_mut() {
        file.result = if verification.passed {
            ProofStatus::Proved
        } else {
            ProofStatus::Refuted
        };
        file.fragment = Some(fragment.to_owned());
    }
    for item in violations {
        let code = if item.expectation == vc::ObligationExpectation::Refute {
            "refute.failed:refutation.true"
        } else if item.id.contains(":undefined-global:") {
            "expression.undefined:undefined.global.name"
        } else if item.id.contains(":undefined-local:") {
            "expression.undefined:undefined.local.variable"
        } else if item.id.contains(":undefined-base:") {
            "assert.failed:assertion.false"
        } else if item.id.contains(":field-permission:") {
            "field.read:insufficient.permission"
        } else if item.id.contains(":field-write-permission:") {
            "field.write:insufficient.permission"
        } else if item
            .id
            .contains(":application-precondition:method-call-receiver-nonnull:")
        {
            "application.precondition:assertion.false"
        } else if item
            .id
            .contains(":call-precondition:method-call-receiver-nonnull:")
        {
            "call.precondition:assertion.false"
        } else if item.id.contains(":method-call-precondition:")
            || item.id.contains(":constructor-precondition:")
        {
            "call.precondition:insufficient.permission"
        } else if item.id.contains(":constructor-initialization-permission:") {
            "postcondition.violated:insufficient.permission"
        } else if item.id.contains(":function-totality:") {
            "function.not.wellformed:assertion.false"
        } else if item.id.contains(":postcondition:") {
            "postcondition.violated:assertion.false"
        } else if item.id.contains(":assert:") {
            "assert.failed:assertion.false"
        } else {
            "heap.obligation.failed"
        };
        response.diagnostics.push(Diagnostic::located_error(
            code,
            format!(
                "heap obligation {:?} returned {:?}; model: {}",
                item.id,
                item.status,
                item.counterexample.as_deref().unwrap_or("unavailable")
            ),
            path,
            item.line,
            item.column,
        ));
    }
}

fn resolve_source_path(root: &Path, relative: &str) -> Result<PathBuf, String> {
    let relative_path = Path::new(relative);
    if relative_path.is_absolute()
        || relative_path
            .components()
            .any(|part| matches!(part, Component::ParentDir | Component::Prefix(_)))
    {
        return Err(format!(
            "source path must stay below source_root: {relative:?}"
        ));
    }
    let resolved = fs::canonicalize(root.join(relative_path))
        .map_err(|error| format!("cannot resolve source path {relative:?}: {error}"))?;
    if !resolved.starts_with(root) {
        return Err(format!(
            "resolved source path escapes source_root: {relative:?}"
        ));
    }
    Ok(resolved)
}

fn hex_digest(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn verifier_identity() -> Result<VerifierIdentity, String> {
    let executable = std::env::current_exe()
        .map_err(|error| format!("cannot resolve running verifier executable: {error}"))?;
    let executable_bytes = fs::read(&executable).map_err(|error| {
        format!(
            "cannot hash running verifier executable {:?}: {error}",
            executable
        )
    })?;
    let frontend_sources = frontend_bundle_sources();
    let kernel_sources = kernel_bundle_sources();
    Ok(VerifierIdentity {
        executable_sha256: hex_digest(&executable_bytes),
        frontend_bundle_sha256: bundle_digest(&frontend_sources),
        kernel_bundle_sha256: bundle_digest(&kernel_sources),
    })
}

fn frontend_bundle_sources() -> Vec<&'static [u8]> {
    vec![
        include_bytes!("python.rs"),
        include_bytes!("conformance_annotations.rs"),
        include_bytes!("python_contracts.rs"),
        include_bytes!("python_sequence_builtins.rs"),
        include_bytes!("python_contract_positions.rs"),
        include_bytes!("python_adt_wellformedness.rs"),
        include_bytes!("python_adt_contracts.rs"),
        include_bytes!("python_adt_contracts/expressions.rs"),
        include_bytes!("python_io_contracts.rs"),
        include_bytes!("python_io_wellformedness.rs"),
        include_bytes!("python_io_wellformedness/existentials.rs"),
        include_bytes!("python_language_wellformedness.rs"),
        include_bytes!("python_thread_wellformedness.rs"),
        include_bytes!("python_thread_wellformedness/bindings.rs"),
        include_bytes!("python_thread_wellformedness/calls.rs"),
        include_bytes!("python_thread_wellformedness/expressions.rs"),
        include_bytes!("python_thread_wellformedness/sif.rs"),
        include_bytes!("python_thread_wellformedness/traversal.rs"),
        include_bytes!("fragments.rs"),
        include_bytes!("python_heap_contracts.rs"),
        include_bytes!("python_dataclass_defaults.rs"),
        include_bytes!("python_int_enum.rs"),
        include_bytes!("python_reference_contracts.rs"),
        include_bytes!("mixed_language.rs"),
        include_bytes!("typescript.rs"),
        include_bytes!("../typescript/frontend.cjs"),
        include_bytes!("../package-lock.json"),
    ]
}

fn kernel_bundle_sources() -> Vec<&'static [u8]> {
    vec![
        include_bytes!("call_binding.rs"),
        include_bytes!("kernel.rs"),
        include_bytes!("vc.rs"),
        include_bytes!("solver.rs"),
    ]
}

fn bundle_digest(parts: &[&[u8]]) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_be_bytes());
        digest.update(part);
    }
    digest
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn traversal_is_rejected_before_source_read() {
        let root = Path::new("C:\\workspace");
        let error = resolve_source_path(root, "../secret.py").unwrap_err();
        assert!(error.contains("must stay below"));
    }

    #[test]
    fn frontend_identity_covers_specialized_heap_lowerings_and_detects_tampering() {
        let sources = frontend_bundle_sources();
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("conformance_annotations.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_dataclass_defaults.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_int_enum.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_contract_positions.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_sequence_builtins.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_adt_wellformedness.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_adt_contracts.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_adt_contracts/expressions.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_io_contracts.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_io_wellformedness.rs"))
        );
        assert!(sources.iter().any(|source| *source
            == include_bytes!("python_io_wellformedness/existentials.rs")));
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_language_wellformedness.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_thread_wellformedness.rs"))
        );
        assert!(sources.iter().any(
            |source| *source == include_bytes!("python_thread_wellformedness/bindings.rs")
        ));
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_thread_wellformedness/calls.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source
                    == include_bytes!("python_thread_wellformedness/expressions.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_thread_wellformedness/sif.rs"))
        );
        assert!(
            sources.iter().any(
                |source| *source == include_bytes!("python_thread_wellformedness/traversal.rs")
            )
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("fragments.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("python_heap_contracts.rs"))
        );
        assert!(
            sources
                .iter()
                .any(|source| *source == include_bytes!("mixed_language.rs"))
        );
        let identity = bundle_digest(&sources);
        let mut tampered = sources.clone();
        let index = tampered
            .iter()
            .position(|source| *source == include_bytes!("python_int_enum.rs"))
            .unwrap();
        tampered[index] = b"tampered IntEnum frontend";
        assert_ne!(identity, bundle_digest(&tampered));

        let mut tampered = sources;
        let index = tampered
            .iter()
            .position(|source| *source == include_bytes!("python_dataclass_defaults.rs"))
            .unwrap();
        tampered[index] = b"tampered dataclass defaults frontend";
        assert_ne!(identity, bundle_digest(&tampered));

        let mut tampered = frontend_bundle_sources();
        let index = tampered
            .iter()
            .position(|source| *source == include_bytes!("python_heap_contracts.rs"))
            .unwrap();
        tampered[index] = b"tampered direct heap frontend";
        assert_ne!(identity, bundle_digest(&tampered));

        let mut tampered = frontend_bundle_sources();
        let index = tampered
            .iter()
            .position(|source| *source == include_bytes!("python_contract_positions.rs"))
            .unwrap();
        tampered[index] = b"tampered contract-position frontend";
        assert_ne!(identity, bundle_digest(&tampered));

        let mut tampered = frontend_bundle_sources();
        let index = tampered
            .iter()
            .position(|source| *source == include_bytes!("python_adt_wellformedness.rs"))
            .unwrap();
        tampered[index] = b"tampered ADT well-formedness frontend";
        assert_ne!(identity, bundle_digest(&tampered));

        let mut tampered = frontend_bundle_sources();
        let index = tampered
            .iter()
            .position(|source| *source == include_bytes!("python_language_wellformedness.rs"))
            .unwrap();
        tampered[index] = b"tampered language well-formedness frontend";
        assert_ne!(identity, bundle_digest(&tampered));

        let mut tampered = frontend_bundle_sources();
        let index = tampered
            .iter()
            .position(|source| *source == include_bytes!("fragments.rs"))
            .unwrap();
        tampered[index] = b"tampered public fragment identities";
        assert_ne!(identity, bundle_digest(&tampered));

        let mut tampered = frontend_bundle_sources();
        let index = tampered
            .iter()
            .position(|source| *source == include_bytes!("mixed_language.rs"))
            .unwrap();
        tampered[index] = b"tampered mixed-language frontend";
        assert_ne!(identity, bundle_digest(&tampered));
    }
}
