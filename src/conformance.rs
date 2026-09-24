use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::mpsc::sync_channel;
use std::thread;

use rustpython_ast::Ranged;
use rustpython_parser::{Mode, Parse, Tok, ast, lexer::lex};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::conformance_annotations::{
    AnnotationBackend, AnnotationPhase, AnnotationProfileEvaluation, NaginiConformanceEnvironment,
    SelectedAnnotationProfile, evaluate_ignore_file_annotations, has_ignore_file_annotation,
};
use crate::protocol::{Diagnostic, PythonTypecheckerIdentity, SourceFile};
use crate::python_contract_positions::{
    ContractPositionFailure, INVALID_CONTRACT_POSITION, InformationFlowVerificationProfile,
    LOCAL_IMPORT, RECURSIVE_STATIC_CALL, TYPE_ERROR_DEAD_CODE, WILDCARD_VARIABLE_READ,
    is_canonical_abc_import_binding, validate_contract_positions_with_profile,
};
use crate::python_contracts::{
    ContractFailure, SourceContractImportRequest, is_canonical_adt_import_binding,
    source_contract_import_requests, verify_contract_module_for_conformance,
};
use crate::python_heap_contracts::{
    HeapContractVerification, ImportedHeapContractModule, source_activates_ordinary_heap_semantics,
    verify_and_export_source_heap_module, verify_heap_module_for_conformance_with_profile,
    verify_heap_package_initializer_with_imports, verify_sif_termination_module,
};
use crate::python_io_contracts::{has_pinned_io_imports, verify_pinned_io_module};
use crate::python_io_wellformedness::{
    EXISTENTIAL_DEFINITION_TYPE_MISMATCH, EXISTENTIAL_USE_UNDEFINED,
    OPERATION_RESULT_NOT_EXISTENTIAL, OPERATION_RESULT_NOT_VARIABLE,
    OPERATION_UNDEFINED_EXISTENTIAL,
};
use crate::python_obligation_leaks::verify_obligation_module_with_intrinsics;
use crate::python_obligation_levels::{CertifiedLevelIntrinsics, ResolvedLevelIntrinsicBindings};
use crate::python_private_fields::PRIVATE_FIELD_ACCESS;
use crate::python_reference_contracts::{
    validate_reference_source_ownership, verify_reference_module,
};
use crate::python_thread_wellformedness::CONCURRENCY_IN_SIF;
use crate::python_typecheck::{
    MYPY_VERSION, PYTHON_TYPECHECK_PROFILE, PythonTypecheckFailure, PythonTypecheckVerification,
    typecheck_request_sources,
};
use crate::python_verifier_intrinsics::{
    CANONICAL_OBLIGATIONS_MODULE, is_canonical_obligations_provider_path,
    validate_canonical_obligations_provider,
};
use crate::vc::ObligationExpectation;

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NaginiSuitePin {
    pub schema: String,
    pub project: String,
    pub repository: String,
    pub tag: String,
    pub commit: String,
    pub license: String,
    pub test_entrypoint: String,
    pub fixture_roots: Vec<String>,
    pub fixture_profiles: Vec<NaginiFixtureVerificationProfile>,
    pub conformance_environment: NaginiConformanceEnvironment,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NaginiFixtureVerificationProfile {
    pub root: String,
    pub information_flow: PinnedInformationFlowProfile,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum PinnedInformationFlowProfile {
    Ordinary,
    SecureInformationFlow,
    PossibilisticSecureInformationFlow,
    ProbabilisticSecureInformationFlow,
}

impl From<PinnedInformationFlowProfile> for InformationFlowVerificationProfile {
    fn from(profile: PinnedInformationFlowProfile) -> Self {
        match profile {
            PinnedInformationFlowProfile::Ordinary => Self::Ordinary,
            PinnedInformationFlowProfile::SecureInformationFlow => Self::SecureInformationFlow,
            PinnedInformationFlowProfile::PossibilisticSecureInformationFlow => {
                Self::PossibilisticSecureInformationFlow
            }
            PinnedInformationFlowProfile::ProbabilisticSecureInformationFlow => {
                Self::ProbabilisticSecureInformationFlow
            }
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct AnnotationCounts {
    pub expected_outputs: u64,
    pub unexpected_outputs: u64,
    pub missing_outputs: u64,
    pub ignored_files: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct NaginiInventory {
    pub schema: String,
    pub project: String,
    pub tag: String,
    pub commit: String,
    pub python_files: u64,
    pub annotations: AnnotationCounts,
    pub areas: BTreeMap<String, u64>,
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExpectedDiagnostic {
    pub code: String,
    pub line: u32,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ConformanceMatchKind {
    SemanticVerification,
    ProductionTypecheckRejection,
    SourceWellformednessRejection,
    SupersededUpstreamUnsupported,
    ProfileIgnored,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ScalarConformanceResult {
    pub schema: String,
    pub fixture: String,
    pub expected: Vec<ExpectedDiagnostic>,
    pub actual: Vec<ExpectedDiagnostic>,
    pub passed: bool,
    pub analysis_kind: ConformanceMatchKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub python_typechecker: Option<PythonTypecheckerIdentity>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub python_typecheck_diagnostics: Vec<Diagnostic>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub annotation_profile: Option<AnnotationProfileEvaluation>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScalarFixtureManifest {
    pub schema: String,
    pub fixtures: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ScalarSuiteConformanceResult {
    pub schema: String,
    pub fixtures: Vec<ScalarConformanceResult>,
    pub passed: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct HeapConformanceResult {
    pub schema: String,
    pub fixture: String,
    pub expected: Vec<ExpectedDiagnostic>,
    pub actual: Vec<ExpectedDiagnostic>,
    pub passed: bool,
    pub semantic_verified: bool,
    pub analysis_kind: ConformanceMatchKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub python_typechecker: Option<PythonTypecheckerIdentity>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub python_typecheck_diagnostics: Vec<Diagnostic>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub annotation_profile: Option<AnnotationProfileEvaluation>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct HeapSuiteConformanceResult {
    pub schema: String,
    pub fixtures: Vec<HeapConformanceResult>,
    pub passed: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ReferenceConformanceResult {
    pub schema: String,
    pub fixture: String,
    pub expected: Vec<ExpectedDiagnostic>,
    pub actual: Vec<ExpectedDiagnostic>,
    pub passed: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub annotation_profile: Option<AnnotationProfileEvaluation>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ReferenceSuiteConformanceResult {
    pub schema: String,
    pub fixtures: Vec<ReferenceConformanceResult>,
    pub passed: bool,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ScalarFixtureClassification {
    pub fixture: String,
    pub status: String,
    pub detail: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub expected: Vec<ExpectedDiagnostic>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub actual: Vec<ExpectedDiagnostic>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub match_kind: Option<ConformanceMatchKind>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub python_typechecker: Option<PythonTypecheckerIdentity>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub python_typecheck_diagnostics: Vec<Diagnostic>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub annotation_profile: Option<AnnotationProfileEvaluation>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ScalarClassificationReport {
    pub schema: String,
    pub suite_commit: String,
    pub root: String,
    pub matched: u64,
    pub semantic_matched: u64,
    pub production_typecheck_rejection_matched: u64,
    pub source_wellformedness_rejection_matched: u64,
    pub production_typecheck_divergent: u64,
    pub mismatched: u64,
    pub refused: u64,
    pub profile_ignored: u64,
    pub fixtures: Vec<ScalarFixtureClassification>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct HeapClassificationReport {
    pub schema: String,
    pub suite_commit: String,
    pub root: String,
    pub matched: u64,
    pub superseded_upstream_unsupported: u64,
    pub mismatched: u64,
    pub refused: u64,
    pub profile_ignored: u64,
    pub fixtures: Vec<ScalarFixtureClassification>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ReferenceClassificationReport {
    pub schema: String,
    pub suite_commit: String,
    pub root: String,
    pub matched: u64,
    pub mismatched: u64,
    pub refused: u64,
    pub profile_ignored: u64,
    pub fixtures: Vec<ScalarFixtureClassification>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CombinedFixtureClassification {
    pub fixture: String,
    pub status: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub expected: Vec<ExpectedDiagnostic>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub actual: Vec<ExpectedDiagnostic>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub match_kind: Option<ConformanceMatchKind>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub python_typechecker: Option<PythonTypecheckerIdentity>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub python_typecheck_diagnostics: Vec<Diagnostic>,
    pub scalar_status: String,
    pub scalar_detail: String,
    pub heap_status: String,
    pub heap_detail: String,
    pub reference_status: String,
    pub reference_detail: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub annotation_profile: Option<AnnotationProfileEvaluation>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CombinedClassificationReport {
    pub schema: String,
    pub suite_commit: String,
    pub roots: Vec<String>,
    pub total: u64,
    pub matched: u64,
    pub semantic_matched: u64,
    pub production_typecheck_rejection_matched: u64,
    pub source_wellformedness_rejection_matched: u64,
    pub superseded_upstream_unsupported: u64,
    pub production_typecheck_divergent: u64,
    pub mismatched: u64,
    pub refused: u64,
    pub profile_ignored: u64,
    pub scalar_matched: u64,
    pub scalar_mismatched: u64,
    pub scalar_refused: u64,
    pub scalar_profile_ignored: u64,
    pub heap_matched: u64,
    pub heap_superseded_upstream_unsupported: u64,
    pub heap_mismatched: u64,
    pub heap_refused: u64,
    pub heap_profile_ignored: u64,
    pub reference_matched: u64,
    pub reference_mismatched: u64,
    pub reference_refused: u64,
    pub reference_profile_ignored: u64,
    pub fixtures: Vec<CombinedFixtureClassification>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClassificationLane {
    Scalar,
    Heap,
    Reference,
}

impl ClassificationLane {
    const ALL: [Self; 3] = [Self::Scalar, Self::Heap, Self::Reference];

    pub fn label(self) -> &'static str {
        match self {
            Self::Scalar => "scalar",
            Self::Heap => "heap",
            Self::Reference => "reference",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClassificationProgressEvent {
    FixtureStarted {
        lane: ClassificationLane,
        root: String,
        fixture: String,
        ordinal: u64,
        total: u64,
    },
    LaneCompleted {
        lane: ClassificationLane,
        root: String,
        total: u64,
    },
}

const CLASSIFIER_CACHE_SCHEMA: &str = "maledictus-classifier-cache-entry/v1";
const CLASSIFIER_CACHE_KEY_SCHEMA: &str = "maledictus-classifier-cache-key/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ClassifierCacheFileIdentity {
    path: String,
    sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ClassifierSolverIdentity {
    solver: String,
    solver_version: String,
    rust_binding: String,
    vc_ir: String,
}

impl From<crate::protocol::SolverIdentity> for ClassifierSolverIdentity {
    fn from(identity: crate::protocol::SolverIdentity) -> Self {
        Self {
            solver: identity.solver,
            solver_version: identity.solver_version,
            rust_binding: identity.rust_binding,
            vc_ir: identity.vc_ir,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ClassifierCacheBaseKey {
    schema: String,
    lane: String,
    fixture: String,
    fixture_sha256: String,
    suite_pin_sha256: String,
    suite_commit: String,
    pinned_root_inventory_sha256: String,
    suite_source_tree_sha256: String,
    executable_sha256: String,
    solver: ClassifierSolverIdentity,
    python_fragments: Vec<String>,
    checked_external_adapters: Vec<ClassifierCacheFileIdentity>,
    external_stubs: Vec<ClassifierCacheFileIdentity>,
    generated_interfaces: Vec<ClassifierCacheFileIdentity>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ClassifierCacheKey {
    base: ClassifierCacheBaseKey,
    #[serde(skip_serializing_if = "Option::is_none")]
    python_typechecker: Option<PythonTypecheckerIdentity>,
}

#[derive(Serialize)]
struct ClassifierCachePayload<'a> {
    key: &'a ClassifierCacheKey,
    result: &'a ScalarFixtureClassification,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ClassifierCacheEntry {
    schema: String,
    payload_sha256: String,
    key: ClassifierCacheKey,
    result: ScalarFixtureClassification,
}

struct ClassifierCache {
    cache_root: PathBuf,
    cache_root_canonical: PathBuf,
    _source_snapshot: tempfile::TempDir,
    analysis_root: PathBuf,
    pin: NaginiSuitePin,
    suite_pin_sha256: String,
    suite_commit: String,
    pinned_root_inventory_sha256: String,
    suite_source_tree_sha256: String,
    executable_sha256: String,
    solver: ClassifierSolverIdentity,
    python_fragments: Vec<String>,
}

pub fn default_classifier_cache_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(".cache")
        .join("classify-suite")
}

fn sha256_bytes(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let bytes = fs::read(path)
        .map_err(|error| format!("cannot hash classifier input {}: {error}", path.display()))?;
    Ok(sha256_bytes(&bytes))
}

fn update_framed_digest(digest: &mut Sha256, value: &[u8]) -> Result<(), String> {
    let length = u64::try_from(value.len())
        .map_err(|_| "classifier cache identity component exceeds u64".to_owned())?;
    digest.update(length.to_be_bytes());
    digest.update(value);
    Ok(())
}

fn canonical_json_sha256<T: Serialize>(value: &T) -> Result<String, String> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| format!("cannot encode classifier cache identity: {error}"))?;
    Ok(sha256_bytes(&bytes))
}

fn normalized_suite_path(suite_root: &Path, path: &Path) -> Result<String, String> {
    let relative = path.strip_prefix(suite_root).map_err(|_| {
        format!(
            "classifier semantic input escaped suite root: {}",
            path.display()
        )
    })?;
    let normalized = relative.to_string_lossy().replace('\\', "/");
    if normalized.is_empty()
        || relative.is_absolute()
        || relative
            .components()
            .any(|part| matches!(part, std::path::Component::ParentDir))
    {
        return Err(format!(
            "classifier semantic input has invalid suite-relative path: {}",
            path.display()
        ));
    }
    Ok(normalized)
}

fn collect_suite_python_sources(directory: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    let mut entries = fs::read_dir(directory)
        .map_err(|error| {
            format!(
                "cannot inspect suite source tree {}: {error}",
                directory.display()
            )
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| {
            format!(
                "cannot inspect suite source tree {}: {error}",
                directory.display()
            )
        })?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let file_name = entry.file_name();
        if file_name == ".git" {
            continue;
        }
        let metadata = fs::symlink_metadata(&path).map_err(|error| {
            format!(
                "cannot inspect suite source input {}: {error}",
                path.display()
            )
        })?;
        if metadata.file_type().is_symlink() {
            let extension = path.extension().and_then(|value| value.to_str());
            if matches!(extension, Some("py" | "pyi")) {
                return Err(format!(
                    "classifier cache refuses symbolic-link Python source input: {}",
                    path.display()
                ));
            }
        } else if metadata.is_dir() {
            collect_suite_python_sources(&path, files)?;
        } else if metadata.is_file()
            && matches!(
                path.extension().and_then(|value| value.to_str()),
                Some("py" | "pyi")
            )
        {
            files.push(path);
        }
    }
    Ok(())
}

fn snapshot_suite_source_tree(
    suite_root: &Path,
    cache_root: &Path,
) -> Result<(tempfile::TempDir, PathBuf, String), String> {
    let mut files = Vec::new();
    collect_suite_python_sources(suite_root, &mut files)?;
    files.sort();
    let snapshot = tempfile::Builder::new()
        .prefix("source-snapshot-")
        .tempdir_in(cache_root)
        .map_err(|error| {
            format!(
                "cannot create classifier source snapshot in {}: {error}",
                cache_root.display()
            )
        })?;
    let analysis_root = snapshot.path().join("suite");
    fs::create_dir_all(&analysis_root).map_err(|error| {
        format!(
            "cannot create classifier source snapshot root {}: {error}",
            analysis_root.display()
        )
    })?;
    let mut digest = Sha256::new();
    update_framed_digest(&mut digest, b"maledictus-classifier-suite-source-tree/v1")?;
    for path in files {
        let relative = normalized_suite_path(suite_root, &path)?;
        update_framed_digest(&mut digest, relative.as_bytes())?;
        let bytes = fs::read(&path).map_err(|error| {
            format!("cannot read suite source input {}: {error}", path.display())
        })?;
        update_framed_digest(&mut digest, &bytes)?;
        let snapshot_path = analysis_root.join(&relative);
        let snapshot_parent = snapshot_path.parent().ok_or_else(|| {
            format!("classifier source snapshot path has no parent: {relative:?}")
        })?;
        fs::create_dir_all(snapshot_parent).map_err(|error| {
            format!(
                "cannot create classifier source snapshot directory {}: {error}",
                snapshot_parent.display()
            )
        })?;
        fs::write(&snapshot_path, bytes).map_err(|error| {
            format!(
                "cannot write classifier source snapshot {}: {error}",
                snapshot_path.display()
            )
        })?;
    }
    Ok((snapshot, analysis_root, format!("{:x}", digest.finalize())))
}

fn pinned_root_inventory_sha256(
    suite_root: &Path,
    fixture_roots: &[String],
) -> Result<String, String> {
    let mut digest = Sha256::new();
    update_framed_digest(&mut digest, b"maledictus-classifier-root-inventory/v1")?;
    for fixture_root in fixture_roots {
        update_framed_digest(&mut digest, fixture_root.replace('\\', "/").as_bytes())?;
        let root = suite_root.join(fixture_root);
        let mut fixtures = Vec::new();
        collect_nagini_test_files(&root, &mut fixtures)?;
        fixtures.sort();
        for fixture in fixtures {
            let relative = normalized_suite_path(suite_root, &fixture)?;
            update_framed_digest(&mut digest, relative.as_bytes())?;
        }
    }
    Ok(format!("{:x}", digest.finalize()))
}

fn path_is_within(path: &Path, parent: &Path) -> bool {
    path == parent || path.starts_with(parent)
}

fn resolve_path_before_creation(path: &Path) -> Result<PathBuf, String> {
    let mut existing = path.to_path_buf();
    let mut missing = Vec::new();
    while !existing.exists() {
        let name = existing.file_name().ok_or_else(|| {
            format!(
                "cannot resolve classifier cache path before creation: {}",
                path.display()
            )
        })?;
        missing.push(name.to_os_string());
        existing = existing
            .parent()
            .ok_or_else(|| {
                format!(
                    "classifier cache path has no existing ancestor: {}",
                    path.display()
                )
            })?
            .to_path_buf();
    }
    let mut resolved = fs::canonicalize(&existing).map_err(|error| {
        format!(
            "cannot resolve classifier cache ancestor {}: {error}",
            existing.display()
        )
    })?;
    for component in missing.into_iter().rev() {
        resolved.push(component);
    }
    Ok(resolved)
}

impl ClassifierCache {
    fn new(suite_root: &Path, pin_path: &Path, cache_root: &Path) -> Result<Self, String> {
        let pin_bytes = fs::read(pin_path)
            .map_err(|error| format!("cannot read suite pin {}: {error}", pin_path.display()))?;
        let pin = parse_pin(&pin_bytes, pin_path)?;
        let suite_root = fs::canonicalize(suite_root).map_err(|error| {
            format!(
                "cannot resolve pinned suite root {} for classifier cache: {error}",
                suite_root.display()
            )
        })?;
        let actual_commit = git_commit(&suite_root)?;
        if actual_commit != pin.commit {
            return Err(format!(
                "Nagini suite commit mismatch: expected {}, found {actual_commit}",
                pin.commit
            ));
        }

        let repository_root = fs::canonicalize(env!("CARGO_MANIFEST_DIR")).map_err(|error| {
            format!("cannot resolve Maledictus repository root for classifier cache: {error}")
        })?;
        let repository_cache = repository_root.join(".cache");
        fs::create_dir_all(&repository_cache).map_err(|error| {
            format!(
                "cannot create repository cache {}: {error}",
                repository_cache.display()
            )
        })?;
        let repository_cache = fs::canonicalize(&repository_cache).map_err(|error| {
            format!(
                "cannot resolve repository cache {}: {error}",
                repository_cache.display()
            )
        })?;
        if !path_is_within(&repository_cache, &repository_root) {
            return Err(format!(
                "repository .cache resolves outside the Maledictus repository: {}",
                repository_cache.display()
            ));
        }
        let requested_cache_root = if cache_root.is_absolute() {
            cache_root.to_path_buf()
        } else {
            repository_root.join(cache_root)
        };
        let requested_cache_root = resolve_path_before_creation(&requested_cache_root)?;
        if !path_is_within(&requested_cache_root, &repository_cache) {
            return Err(format!(
                "classifier cache must be below repository .cache: {}",
                requested_cache_root.display()
            ));
        }
        fs::create_dir_all(&requested_cache_root).map_err(|error| {
            format!(
                "cannot create classifier cache {}: {error}",
                requested_cache_root.display()
            )
        })?;
        let cache_root_canonical = fs::canonicalize(&requested_cache_root).map_err(|error| {
            format!(
                "cannot resolve classifier cache {}: {error}",
                requested_cache_root.display()
            )
        })?;
        if !path_is_within(&cache_root_canonical, &repository_cache) {
            return Err(format!(
                "classifier cache resolves outside repository .cache: {}",
                cache_root_canonical.display()
            ));
        }

        let executable = std::env::current_exe()
            .map_err(|error| format!("cannot resolve classifier executable: {error}"))?;
        let mut python_fragments = crate::fragments::PYTHON_CAPABILITIES
            .iter()
            .map(|fragment| (*fragment).to_owned())
            .collect::<Vec<_>>();
        python_fragments.sort();

        let (source_snapshot, analysis_root, suite_source_tree_sha256) =
            snapshot_suite_source_tree(&suite_root, &requested_cache_root)?;
        let pinned_root_inventory_sha256 =
            pinned_root_inventory_sha256(&analysis_root, &pin.fixture_roots)?;

        Ok(Self {
            cache_root: requested_cache_root,
            cache_root_canonical,
            _source_snapshot: source_snapshot,
            analysis_root,
            pin,
            suite_pin_sha256: sha256_bytes(&pin_bytes),
            suite_commit: actual_commit,
            pinned_root_inventory_sha256,
            suite_source_tree_sha256,
            executable_sha256: sha256_file(&executable)?,
            solver: crate::solver::identity().into(),
            python_fragments,
        })
    }

    fn base_key(
        &self,
        lane: ClassificationLane,
        fixture: &str,
        fixture_path: &Path,
    ) -> Result<ClassifierCacheBaseKey, String> {
        Ok(ClassifierCacheBaseKey {
            schema: CLASSIFIER_CACHE_KEY_SCHEMA.to_owned(),
            lane: lane.label().to_owned(),
            fixture: fixture.to_owned(),
            fixture_sha256: sha256_file(fixture_path)?,
            suite_pin_sha256: self.suite_pin_sha256.clone(),
            suite_commit: self.suite_commit.clone(),
            pinned_root_inventory_sha256: self.pinned_root_inventory_sha256.clone(),
            suite_source_tree_sha256: self.suite_source_tree_sha256.clone(),
            executable_sha256: self.executable_sha256.clone(),
            solver: self.solver.clone(),
            python_fragments: self.python_fragments.clone(),
            checked_external_adapters: Vec::new(),
            external_stubs: Vec::new(),
            generated_interfaces: Vec::new(),
        })
    }

    fn entry_directory(&self, base: &ClassifierCacheBaseKey) -> Result<PathBuf, String> {
        let base_sha256 = canonical_json_sha256(base)?;
        let directory = self
            .cache_root
            .join(&base.lane)
            .join(&base_sha256[0..2])
            .join(base_sha256);
        fs::create_dir_all(&directory).map_err(|error| {
            format!(
                "cannot create classifier cache entry directory {}: {error}",
                directory.display()
            )
        })?;
        let canonical = fs::canonicalize(&directory).map_err(|error| {
            format!(
                "cannot resolve classifier cache entry directory {}: {error}",
                directory.display()
            )
        })?;
        if !path_is_within(&canonical, &self.cache_root_canonical) {
            return Err(format!(
                "classifier cache entry directory resolves outside cache root: {}",
                canonical.display()
            ));
        }
        Ok(directory)
    }

    fn load(
        &self,
        lane: ClassificationLane,
        fixture: &str,
        fixture_path: &Path,
        source: &str,
    ) -> Result<Option<ScalarFixtureClassification>, String> {
        let base = self.base_key(lane, fixture, fixture_path)?;
        let directory = self.entry_directory(&base)?;
        let mut candidates = fs::read_dir(&directory)
            .map_err(|error| {
                format!(
                    "cannot inspect classifier cache entry directory {}: {error}",
                    directory.display()
                )
            })?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| {
                format!(
                    "cannot inspect classifier cache entry directory {}: {error}",
                    directory.display()
                )
            })?;
        candidates.sort_by_key(|candidate| candidate.file_name());
        let mut valid = Vec::new();
        for candidate in candidates {
            let path = candidate.path();
            if path.extension().and_then(|extension| extension.to_str()) != Some("json") {
                continue;
            }
            let metadata = match fs::symlink_metadata(&path) {
                Ok(metadata) if metadata.is_file() && !metadata.file_type().is_symlink() => {
                    metadata
                }
                _ => continue,
            };
            if metadata.len() == 0 {
                continue;
            }
            let bytes = match fs::read(&path) {
                Ok(bytes) => bytes,
                Err(_) => continue,
            };
            let entry: ClassifierCacheEntry = match serde_json::from_slice(&bytes) {
                Ok(entry) => entry,
                Err(_) => continue,
            };
            if entry.schema != CLASSIFIER_CACHE_SCHEMA || entry.key.base != base {
                continue;
            }
            let payload_sha256 = canonical_json_sha256(&ClassifierCachePayload {
                key: &entry.key,
                result: &entry.result,
            })?;
            let candidate_name = match path.file_name().and_then(|name| name.to_str()) {
                Some(name) => name,
                None => continue,
            };
            if entry.payload_sha256 != payload_sha256
                || !candidate_name.starts_with(&format!("{payload_sha256}."))
                || !candidate_name.ends_with(".json")
            {
                continue;
            }
            if validate_cached_fixture(lane, fixture, &entry.key, &entry.result).is_err() {
                continue;
            }
            let information_flow =
                information_flow_profile_for_fixture(&self.pin, Path::new(fixture))?;
            let typechecker_applicable = match lane {
                ClassificationLane::Scalar => {
                    scalar_source_may_invoke_typechecker(source, fixture, information_flow)
                }
                ClassificationLane::Heap => {
                    heap_source_may_invoke_typechecker(source, fixture, information_flow)
                }
                ClassificationLane::Reference => {
                    validate_contract_positions_with_profile(source, fixture, information_flow)
                        .is_err()
                }
            };
            if typechecker_applicable != entry.key.python_typechecker.is_some() {
                continue;
            }
            if let Some(expected_identity) = &entry.key.python_typechecker {
                let current_identity = match probe_classifier_typechecker_identity(
                    &self.analysis_root,
                    fixture,
                    source,
                ) {
                    Ok(identity) => identity,
                    Err(_) => continue,
                };
                if &current_identity != expected_identity {
                    continue;
                }
            }
            valid.push(entry.result);
        }
        let Some(first) = valid.first() else {
            return Ok(None);
        };
        if valid.iter().all(|candidate| candidate == first) {
            Ok(Some(first.clone()))
        } else {
            Ok(None)
        }
    }

    fn store(
        &self,
        lane: ClassificationLane,
        fixture: &str,
        fixture_path: &Path,
        python_typechecker: Option<PythonTypecheckerIdentity>,
        result: &ScalarFixtureClassification,
    ) -> Result<(), String> {
        let key = ClassifierCacheKey {
            base: self.base_key(lane, fixture, fixture_path)?,
            python_typechecker,
        };
        validate_cached_fixture(lane, fixture, &key, result)?;
        let payload_sha256 = canonical_json_sha256(&ClassifierCachePayload { key: &key, result })?;
        let entry = ClassifierCacheEntry {
            schema: CLASSIFIER_CACHE_SCHEMA.to_owned(),
            payload_sha256: payload_sha256.clone(),
            key,
            result: result.clone(),
        };
        let directory = self.entry_directory(&entry.key.base)?;
        let mut temporary = tempfile::NamedTempFile::new_in(&directory).map_err(|error| {
            format!(
                "cannot create atomic classifier cache temporary file in {}: {error}",
                directory.display()
            )
        })?;
        serde_json::to_writer(&mut temporary, &entry)
            .map_err(|error| format!("cannot encode classifier cache entry: {error}"))?;
        temporary
            .write_all(b"\n")
            .map_err(|error| format!("cannot finish classifier cache entry: {error}"))?;
        temporary
            .flush()
            .map_err(|error| format!("cannot flush classifier cache entry: {error}"))?;
        temporary
            .as_file()
            .sync_all()
            .map_err(|error| format!("cannot synchronize classifier cache entry: {error}"))?;
        let temporary_name = temporary
            .path()
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| "classifier cache temporary file has no UTF-8 name".to_owned())?;
        let destination = directory.join(format!("{payload_sha256}.{temporary_name}.json"));
        temporary
            .persist_noclobber(&destination)
            .map(|_| ())
            .map_err(|error| {
                format!(
                    "cannot atomically publish classifier cache entry {}: {}",
                    destination.display(),
                    error.error
                )
            })
    }
}

fn probe_classifier_typechecker_identity(
    suite_root: &Path,
    fixture: &str,
    _source: &str,
) -> Result<PythonTypecheckerIdentity, String> {
    let fixture_path = suite_root.join(fixture);
    let source_root = fixture_path
        .parent()
        .ok_or_else(|| format!("classifier fixture has no source parent: {fixture:?}"))?;
    let checked_path = fixture_path
        .file_name()
        .ok_or_else(|| format!("classifier fixture has no file name: {fixture:?}"))?
        .to_string_lossy()
        .into_owned();
    let verification = typecheck_request_sources(
        source_root,
        &[SourceFile {
            path: checked_path,
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        &[],
    )
    .map_err(|error| format!("{}: {}", error.code, error.message))?
    .ok_or_else(|| "classifier typechecker identity probe returned no result".to_owned())?;
    validate_conformance_typechecker_identity(&verification.identity)?;
    Ok(verification.identity)
}

fn validate_cached_fixture(
    lane: ClassificationLane,
    fixture: &str,
    key: &ClassifierCacheKey,
    result: &ScalarFixtureClassification,
) -> Result<(), String> {
    if key.base.schema != CLASSIFIER_CACHE_KEY_SCHEMA
        || key.base.lane != lane.label()
        || key.base.fixture != fixture
        || result.fixture != fixture
        || !key.base.checked_external_adapters.is_empty()
        || !key.base.external_stubs.is_empty()
        || !key.base.generated_interfaces.is_empty()
    {
        return Err(
            "classifier cache entry does not bind the requested fixture and lane".to_owned(),
        );
    }
    if result.expected.windows(2).any(|pair| pair[0] > pair[1])
        || result.actual.windows(2).any(|pair| pair[0] > pair[1])
    {
        return Err("classifier cache diagnostics are not canonical".to_owned());
    }
    if let Some(identity) = &key.python_typechecker {
        validate_conformance_typechecker_identity(identity)?;
    }
    match lane {
        ClassificationLane::Scalar => {
            if result.python_typechecker != key.python_typechecker {
                return Err("scalar cache typechecker identity mismatch".to_owned());
            }
            match result.status.as_str() {
                "matched"
                    if matches!(
                        result.match_kind,
                        Some(
                            ConformanceMatchKind::SemanticVerification
                                | ConformanceMatchKind::ProductionTypecheckRejection
                                | ConformanceMatchKind::SourceWellformednessRejection
                        )
                    ) => {}
                "mismatched" | "production-typecheck-divergence" | "refused"
                    if result.match_kind.is_none() => {}
                "profile-ignored"
                    if result.match_kind == Some(ConformanceMatchKind::ProfileIgnored) => {}
                _ => return Err("invalid scalar classifier cache result".to_owned()),
            }
        }
        ClassificationLane::Heap => {
            if result.python_typechecker != key.python_typechecker {
                return Err("heap cache typechecker identity mismatch".to_owned());
            }
            match result.status.as_str() {
                "matched"
                    if matches!(
                        result.match_kind,
                        Some(
                            ConformanceMatchKind::SemanticVerification
                                | ConformanceMatchKind::SourceWellformednessRejection
                        )
                    ) => {}
                "superseded-upstream-unsupported"
                    if result.match_kind
                        == Some(ConformanceMatchKind::SupersededUpstreamUnsupported) => {}
                "mismatched" | "refused" if result.match_kind.is_none() => {}
                "profile-ignored"
                    if result.match_kind == Some(ConformanceMatchKind::ProfileIgnored) => {}
                _ => return Err("invalid heap classifier cache result".to_owned()),
            }
        }
        ClassificationLane::Reference => {
            if result.python_typechecker.is_some() {
                return Err(
                    "reference cache result unexpectedly stores typechecker output".to_owned(),
                );
            }
            match result.status.as_str() {
                "matched"
                    if result.match_kind == Some(ConformanceMatchKind::SemanticVerification) => {}
                "mismatched" | "refused" if result.match_kind.is_none() => {}
                "profile-ignored"
                    if result.match_kind == Some(ConformanceMatchKind::ProfileIgnored) => {}
                _ => return Err("invalid reference classifier cache result".to_owned()),
            }
        }
    }
    Ok(())
}

#[derive(Clone)]
enum PinnedHeapModuleState {
    Visiting {
        path: PathBuf,
    },
    Done {
        path: PathBuf,
        result: Box<Result<ImportedHeapContractModule, ContractFailure>>,
    },
}

#[derive(Clone)]
enum PinnedPackageInitializerState {
    Visiting,
    Done(Result<(), ContractFailure>),
}

#[derive(Debug)]
struct LocatedPinnedModule {
    path: PathBuf,
    import_root: PathBuf,
}

const PYTHON_SRC_LAYOUT_DIRECTORY: &str = "src";

/// Resolve the real source providers used by a pinned Nagini fixture.
///
/// Nagini's functional fixtures put importable `resources` packages beside the fixture groups,
/// rather than at the repository root.  Resolution therefore walks the importing file's ancestor
/// directories toward the pinned suite root and takes the nearest unambiguous source module.  A
/// provider is usable only after its own body and every recursively imported provider have been
/// verified.  Missing providers, cycles, symlinks, and ambiguous module/package files refuse.
struct PinnedHeapSourceResolver {
    suite_root: PathBuf,
    modules: BTreeMap<String, PinnedHeapModuleState>,
    package_initializers: BTreeMap<PathBuf, PinnedPackageInitializerState>,
}

impl PinnedHeapSourceResolver {
    fn new(suite_root: &Path) -> Result<Self, String> {
        let suite_root = fs::canonicalize(suite_root).map_err(|error| {
            format!(
                "cannot resolve pinned suite root {}: {error}",
                suite_root.display()
            )
        })?;
        Ok(Self {
            suite_root,
            modules: BTreeMap::new(),
            package_initializers: BTreeMap::new(),
        })
    }

    fn resolve_imports_for_source(
        &mut self,
        importer_path: &Path,
        source: &str,
        display_path: &str,
        importer_module: Option<&str>,
    ) -> Result<Vec<ImportedHeapContractModule>, ContractFailure> {
        let import_requests = source_contract_import_requests(source, display_path)?;
        import_requests
            .iter()
            .filter(|request| !is_builtin_heap_semantic_import(request))
            .map(|request| self.resolve_import(importer_path, importer_module, request))
            .collect()
    }

    fn resolve_import(
        &mut self,
        importer_path: &Path,
        importer_module: Option<&str>,
        request: &SourceContractImportRequest,
    ) -> Result<ImportedHeapContractModule, ContractFailure> {
        if request.relative_level == 0 {
            return self.resolve_module(importer_path, &request.module);
        }
        let importer_module = importer_module.ok_or_else(|| ContractFailure {
            code: "frontend.python.heap.relative-import-context-missing",
            message: format!(
                "source {} uses a relative import without a package module context",
                importer_path.display()
            ),
        })?;
        let (canonical_module, located) =
            self.locate_relative_module(importer_path, importer_module, request)?;
        let imported = self.resolve_located_module(&canonical_module, located)?;
        Ok(imported.rebound_for_source_import(&request.module))
    }

    fn resolve_module(
        &mut self,
        importer_path: &Path,
        module: &str,
    ) -> Result<ImportedHeapContractModule, ContractFailure> {
        let located = self.locate_module(importer_path, module)?;
        self.resolve_located_module(module, located)
    }

    fn resolve_located_module(
        &mut self,
        module: &str,
        located: LocatedPinnedModule,
    ) -> Result<ImportedHeapContractModule, ContractFailure> {
        if let Some(state) = self.modules.get(module) {
            return match state {
                PinnedHeapModuleState::Visiting { path } => Err(ContractFailure {
                    code: "frontend.python.heap.import-cycle",
                    message: format!(
                        "pinned source import graph contains a cycle through module {module:?} at {}",
                        path.display()
                    ),
                }),
                PinnedHeapModuleState::Done { path, result } if *path == located.path => {
                    result.as_ref().clone()
                }
                PinnedHeapModuleState::Done { path, .. } => Err(ContractFailure {
                    code: "frontend.python.heap.import-module-ambiguous",
                    message: format!(
                        "module {module:?} resolves to both {} and {}",
                        path.display(),
                        located.path.display()
                    ),
                }),
            };
        }

        self.modules.insert(
            module.to_owned(),
            PinnedHeapModuleState::Visiting {
                path: located.path.clone(),
            },
        );
        let result = (|| {
            self.verify_parent_package_initializers(module, &located)?;
            let source = fs::read_to_string(&located.path).map_err(|error| ContractFailure {
                code: "frontend.python.heap.import-provider-unreadable",
                message: format!(
                    "cannot read source provider {} for module {module:?}: {error}",
                    located.path.display()
                ),
            })?;
            let display_path = self.display_path(&located.path);
            if is_canonical_obligations_provider_path(&self.suite_root, module, &located.path) {
                let provider = validate_canonical_obligations_provider(&source, &display_path)?;
                let certified_level_intrinsics =
                    CertifiedLevelIntrinsics::from_validated_provider(&provider).map_err(
                        |error| ContractFailure {
                            code: "frontend.python.verifier-intrinsic.level-certification-failed",
                            message: format!(
                                "validated canonical obligations provider could not certify level intrinsics: {error:?}"
                            ),
                        },
                    )?;
                return Ok(ImportedHeapContractModule::from_verifier_intrinsics(
                    provider,
                    certified_level_intrinsics,
                ));
            }
            let imports = self.resolve_imports_for_source(
                &located.path,
                &source,
                &display_path,
                Some(module),
            )?;
            let (_, exported) =
                verify_and_export_source_heap_module(&source, &display_path, module, &imports)?;
            Ok(exported)
        })();
        self.modules.insert(
            module.to_owned(),
            PinnedHeapModuleState::Done {
                path: located.path,
                result: Box::new(result.clone()),
            },
        );
        result
    }

    fn verify_parent_package_initializers(
        &mut self,
        module: &str,
        located: &LocatedPinnedModule,
    ) -> Result<(), ContractFailure> {
        let components = module.split('.').collect::<Vec<_>>();
        for prefix_len in 1..components.len() {
            let mut initializer = located.import_root.clone();
            for component in &components[..prefix_len] {
                initializer.push(component);
            }
            initializer.push("__init__.py");
            if initializer.is_file() {
                let package = components[..prefix_len].join(".");
                self.verify_package_initializer(&initializer, &package)?;
            }
        }
        Ok(())
    }

    fn verify_package_initializer(
        &mut self,
        initializer: &Path,
        package: &str,
    ) -> Result<(), ContractFailure> {
        let initializer = self.checked_source_path(initializer)?;
        if let Some(state) = self.package_initializers.get(&initializer) {
            return match state {
                PinnedPackageInitializerState::Visiting => Err(ContractFailure {
                    code: "frontend.python.heap.package-initializer-cycle",
                    message: format!(
                        "package initializer cycle reaches {package:?} at {}",
                        initializer.display()
                    ),
                }),
                PinnedPackageInitializerState::Done(result) => result.clone(),
            };
        }
        self.package_initializers
            .insert(initializer.clone(), PinnedPackageInitializerState::Visiting);
        let result = (|| {
            let source = fs::read_to_string(&initializer).map_err(|error| ContractFailure {
                code: "frontend.python.heap.package-initializer-unreadable",
                message: format!(
                    "cannot read package initializer {}: {error}",
                    initializer.display()
                ),
            })?;
            let display_path = self.display_path(&initializer);
            let imports = self.resolve_imports_for_source(
                &initializer,
                &source,
                &display_path,
                Some(package),
            )?;
            let verification =
                verify_heap_package_initializer_with_imports(&source, &display_path, &imports)?;
            if !verification.passed {
                return Err(ContractFailure {
                    code: "frontend.python.heap.package-initializer-refuted",
                    message: format!(
                        "package initializer {package:?} contains a refuted obligation"
                    ),
                });
            }
            Ok(())
        })();
        self.package_initializers.insert(
            initializer,
            PinnedPackageInitializerState::Done(result.clone()),
        );
        result
    }

    fn locate_relative_module(
        &self,
        importer_path: &Path,
        importer_module: &str,
        request: &SourceContractImportRequest,
    ) -> Result<(String, LocatedPinnedModule), ContractFailure> {
        let importer = self.checked_source_path(importer_path)?;
        let mut directory = importer.parent().ok_or_else(|| ContractFailure {
            code: "frontend.python.heap.importer-parent-missing",
            message: format!(
                "source importer {} has no parent directory",
                importer.display()
            ),
        })?;
        let package_initializer = directory.join("__init__.py");
        if !package_initializer.is_file() {
            return Err(ContractFailure {
                code: "frontend.python.heap.relative-import-package-missing",
                message: format!(
                    "source {} uses a relative import outside a source package",
                    importer.display()
                ),
            });
        }
        self.checked_source_path(&package_initializer)?;

        let mut package_components = importer_module.split('.').collect::<Vec<_>>();
        if importer
            .file_name()
            .is_none_or(|name| name != "__init__.py")
        {
            package_components.pop();
        }
        let ascents = request.relative_level.saturating_sub(1);
        if usize::try_from(ascents).map_or(true, |count| count >= package_components.len()) {
            return Err(ContractFailure {
                code: "frontend.python.heap.relative-import-beyond-top-level",
                message: format!(
                    "source {} uses a relative import beyond package {importer_module:?}",
                    importer.display()
                ),
            });
        }
        for _ in 0..ascents {
            directory = directory.parent().ok_or_else(|| ContractFailure {
                code: "frontend.python.heap.relative-import-beyond-top-level",
                message: format!(
                    "source {} uses a relative import beyond the pinned suite root",
                    importer.display()
                ),
            })?;
            package_components.pop();
        }
        if !directory.starts_with(&self.suite_root) {
            return Err(ContractFailure {
                code: "frontend.python.heap.import-path-escape",
                message: format!(
                    "relative import from {} escapes pinned suite root {}",
                    importer.display(),
                    self.suite_root.display()
                ),
            });
        }

        let mut relative = PathBuf::new();
        for component in request.module.split('.') {
            if !is_python_identifier(component) {
                return Err(ContractFailure {
                    code: "frontend.python.heap.import-module-invalid",
                    message: format!(
                        "relative imported module name {:?} is not a dotted identifier",
                        request.module
                    ),
                });
            }
            relative.push(component);
        }
        let file_candidate = directory.join(&relative).with_extension("py");
        let package_candidate = directory.join(&relative).join("__init__.py");
        let candidates = [file_candidate, package_candidate]
            .into_iter()
            .filter(|candidate| candidate.is_file())
            .collect::<Vec<_>>();
        let provider = match candidates.as_slice() {
            [path] => self.checked_source_path(path)?,
            [first, second] => {
                return Err(ContractFailure {
                    code: "frontend.python.heap.import-module-ambiguous",
                    message: format!(
                        "relative module {:?} has both file and package providers {} and {}",
                        request.module,
                        first.display(),
                        second.display()
                    ),
                });
            }
            [] => {
                return Err(ContractFailure {
                    code: "frontend.python.heap.unbound-module",
                    message: format!(
                        "source {} imports relative module {:?}, but no source provider exists in {}",
                        importer.display(),
                        request.module,
                        directory.display()
                    ),
                });
            }
            _ => unreachable!("a module has at most file and package candidates"),
        };
        let mut canonical_components = package_components
            .iter()
            .map(|component| (*component).to_owned())
            .collect::<Vec<_>>();
        canonical_components.extend(request.module.split('.').map(str::to_owned));
        let canonical_module = canonical_components.join(".");
        let mut import_root = directory.to_path_buf();
        for _ in 0..package_components.len() {
            import_root = import_root
                .parent()
                .expect("package directory has a parent")
                .to_path_buf();
        }
        Ok((
            canonical_module,
            LocatedPinnedModule {
                path: provider,
                import_root,
            },
        ))
    }

    fn source_module_context(&self, source_path: &Path) -> Result<Option<String>, ContractFailure> {
        let source = self.checked_source_path(source_path)?;
        let is_initializer = source.file_name().is_some_and(|name| name == "__init__.py");
        let mut components = if is_initializer {
            Vec::new()
        } else {
            vec![
                source
                    .file_stem()
                    .expect("checked Python source has a file stem")
                    .to_string_lossy()
                    .into_owned(),
            ]
        };
        let mut directory = source.parent();
        while let Some(package) = directory {
            let initializer = package.join("__init__.py");
            if !initializer.is_file() {
                break;
            }
            self.checked_source_path(&initializer)?;
            let name = package
                .file_name()
                .expect("package below suite root has a name")
                .to_string_lossy()
                .into_owned();
            components.push(name);
            directory = package.parent();
        }
        components.reverse();
        Ok((!components.is_empty()).then(|| components.join(".")))
    }

    fn locate_module(
        &self,
        importer_path: &Path,
        module: &str,
    ) -> Result<LocatedPinnedModule, ContractFailure> {
        if module.is_empty() || module.split('.').any(|part| !is_python_identifier(part)) {
            return Err(ContractFailure {
                code: "frontend.python.heap.import-module-invalid",
                message: format!("imported module name {module:?} is not a dotted identifier"),
            });
        }
        let importer = self.checked_source_path(importer_path)?;
        let mut directory = importer.parent().ok_or_else(|| ContractFailure {
            code: "frontend.python.heap.importer-parent-missing",
            message: format!(
                "source importer {} has no parent directory",
                importer.display()
            ),
        })?;
        loop {
            if !directory.starts_with(&self.suite_root) {
                break;
            }
            let mut relative = PathBuf::new();
            for component in module.split('.') {
                relative.push(component);
            }
            let file_candidate = directory.join(&relative).with_extension("py");
            let package_candidate = directory.join(&relative).join("__init__.py");
            let candidates = [file_candidate, package_candidate]
                .into_iter()
                .filter(|candidate| candidate.is_file())
                .collect::<Vec<_>>();
            match candidates.as_slice() {
                [path] => {
                    return Ok(LocatedPinnedModule {
                        path: self.checked_source_path(path)?,
                        import_root: directory.to_path_buf(),
                    });
                }
                [first, second] => {
                    return Err(ContractFailure {
                        code: "frontend.python.heap.import-module-ambiguous",
                        message: format!(
                            "module {module:?} has both file and package providers {} and {}",
                            first.display(),
                            second.display()
                        ),
                    });
                }
                [] => {}
                _ => unreachable!("a module has at most file and package candidates"),
            }
            let Some(parent) = directory.parent() else {
                break;
            };
            directory = parent;
        }

        // Python projects commonly expose their import packages from a repository-level
        // `src/` directory.  The pinned Nagini repository itself uses that layout for the
        // `nagini_contracts` package.  Treat this as one explicit import root after the local
        // ancestor search, preserving the nearer fixture/resource provider precedence above.
        // The provider remains inside the pinned, hash-bound suite and still passes through the
        // complete recursive source verifier; this only locates it.
        let source_import_root = self.suite_root.join(PYTHON_SRC_LAYOUT_DIRECTORY);
        if source_import_root.is_dir() {
            let metadata =
                fs::symlink_metadata(&source_import_root).map_err(|error| ContractFailure {
                    code: "frontend.python.heap.import-path-unreadable",
                    message: format!(
                        "cannot inspect Python source import root {}: {error}",
                        source_import_root.display()
                    ),
                })?;
            if metadata.file_type().is_symlink() {
                return Err(ContractFailure {
                    code: "frontend.python.heap.import-symlink-refused",
                    message: format!(
                        "pinned source imports may not traverse symlink {}",
                        source_import_root.display()
                    ),
                });
            }
            let source_import_root = self.checked_source_path(&source_import_root)?;
            let mut relative = PathBuf::new();
            for component in module.split('.') {
                relative.push(component);
            }
            let file_candidate = source_import_root.join(&relative).with_extension("py");
            let package_candidate = source_import_root.join(&relative).join("__init__.py");
            let candidates = [file_candidate, package_candidate]
                .into_iter()
                .filter(|candidate| candidate.is_file())
                .collect::<Vec<_>>();
            match candidates.as_slice() {
                [path] => {
                    return Ok(LocatedPinnedModule {
                        path: self.checked_source_path(path)?,
                        import_root: source_import_root,
                    });
                }
                [first, second] => {
                    return Err(ContractFailure {
                        code: "frontend.python.heap.import-module-ambiguous",
                        message: format!(
                            "module {module:?} has both file and package providers {} and {}",
                            first.display(),
                            second.display()
                        ),
                    });
                }
                [] => {}
                _ => unreachable!("a module has at most file and package candidates"),
            }
        }
        Err(ContractFailure {
            code: "frontend.python.heap.unbound-module",
            message: format!(
                "source {} imports module {module:?}, but no source provider exists between the importer and pinned suite root {} or its canonical {} layout",
                importer.display(),
                self.suite_root.display(),
                PYTHON_SRC_LAYOUT_DIRECTORY
            ),
        })
    }

    fn checked_source_path(&self, path: &Path) -> Result<PathBuf, ContractFailure> {
        let canonical = fs::canonicalize(path).map_err(|error| ContractFailure {
            code: "frontend.python.heap.import-path-unreadable",
            message: format!("cannot resolve imported source {}: {error}", path.display()),
        })?;
        if !canonical.starts_with(&self.suite_root) {
            return Err(ContractFailure {
                code: "frontend.python.heap.import-path-escape",
                message: format!(
                    "imported source {} escapes pinned suite root {}",
                    canonical.display(),
                    self.suite_root.display()
                ),
            });
        }
        let relative = canonical
            .strip_prefix(&self.suite_root)
            .expect("checked source is below suite root");
        let mut cursor = self.suite_root.clone();
        for component in relative.components() {
            cursor.push(component.as_os_str());
            let metadata = fs::symlink_metadata(&cursor).map_err(|error| ContractFailure {
                code: "frontend.python.heap.import-path-unreadable",
                message: format!(
                    "cannot inspect imported source {}: {error}",
                    cursor.display()
                ),
            })?;
            if metadata.file_type().is_symlink() {
                return Err(ContractFailure {
                    code: "frontend.python.heap.import-symlink-refused",
                    message: format!(
                        "pinned source imports may not traverse symlink {}",
                        cursor.display()
                    ),
                });
            }
        }
        Ok(canonical)
    }

    fn display_path(&self, path: &Path) -> String {
        path.strip_prefix(&self.suite_root)
            .unwrap_or(path)
            .to_string_lossy()
            .replace('\\', "/")
    }
}

fn is_builtin_heap_semantic_import(request: &SourceContractImportRequest) -> bool {
    // These imports name verifier-defined types whose behavior is implemented by a dedicated
    // source-bound heap frontend. They are not application modules to resolve from the pinned
    // source tree. Keep this list shape-exact: unsupported aliases, stars, and unrelated exports
    // must still pass through source resolution and fail closed when no provider exists.
    request.relative_level == 0
        && ((request.module == "enum" && request.imported_names == [("IntEnum".to_owned(), None)])
            || is_canonical_abc_import_binding(
                request.relative_level == 0,
                &request.module,
                &request.imported_names,
            )
            || is_canonical_adt_import_binding(
                request.relative_level == 0,
                &request.module,
                &request.imported_names,
            ))
}

fn is_python_identifier(value: &str) -> bool {
    let mut characters = value.chars();
    characters
        .next()
        .is_some_and(|character| character == '_' || character.is_alphabetic())
        && characters.all(|character| character == '_' || character.is_alphanumeric())
}

pub fn load_pin(path: &Path) -> Result<NaginiSuitePin, String> {
    let source = fs::read(path)
        .map_err(|error| format!("cannot read suite pin {}: {error}", path.display()))?;
    parse_pin(&source, path)
}

fn parse_pin(source: &[u8], path: &Path) -> Result<NaginiSuitePin, String> {
    let pin: NaginiSuitePin = serde_json::from_slice(source)
        .map_err(|error| format!("invalid suite pin {}: {error}", path.display()))?;
    if pin.schema != "maledictus-upstream-suite/v1" {
        return Err(format!("unsupported suite pin schema {:?}", pin.schema));
    }
    if pin.commit.len() != 40 || !pin.commit.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("suite pin commit must be a full 40-character Git hash".to_owned());
    }
    validate_fixture_profiles(&pin)?;
    Ok(pin)
}

fn validate_fixture_profiles(pin: &NaginiSuitePin) -> Result<(), String> {
    let roots = pin.fixture_roots.iter().collect::<BTreeSet<_>>();
    if roots.len() != pin.fixture_roots.len() {
        return Err("suite pin fixture roots must be unique".to_owned());
    }
    let mut profile_roots = BTreeSet::new();
    for profile in &pin.fixture_profiles {
        let root = Path::new(&profile.root);
        if profile.root.is_empty()
            || root.is_absolute()
            || root
                .components()
                .any(|component| matches!(component, std::path::Component::ParentDir))
        {
            return Err(format!(
                "suite pin fixture profile has invalid root {:?}",
                profile.root
            ));
        }
        if !profile_roots.insert(&profile.root) {
            return Err(format!(
                "suite pin fixture profile root is duplicated: {:?}",
                profile.root
            ));
        }
    }
    if roots != profile_roots {
        return Err(
            "suite pin must declare exactly one verification profile for every fixture root"
                .to_owned(),
        );
    }
    validate_conformance_environment(pin)?;
    Ok(())
}

fn validate_conformance_environment(pin: &NaginiSuitePin) -> Result<(), String> {
    let environment = &pin.conformance_environment;
    if environment.nagini_tag != pin.tag || environment.nagini_commit != pin.commit {
        return Err(
            "suite pin conformance environment must repeat the exact pinned Nagini tag and commit"
                .to_owned(),
        );
    }
    if environment.python.major == 0 {
        return Err("suite pin Python language profile major version must be positive".to_owned());
    }
    let fixture_roots = pin.fixture_roots.iter().collect::<BTreeSet<_>>();
    let mut annotation_roots = BTreeSet::new();
    for profile in &environment.annotation_profiles {
        let root = Path::new(&profile.root);
        if profile.root.is_empty()
            || root.is_absolute()
            || root
                .components()
                .any(|component| matches!(component, std::path::Component::ParentDir))
        {
            return Err(format!(
                "suite pin annotation profile has invalid root {:?}",
                profile.root
            ));
        }
        if !annotation_roots.insert(&profile.root) {
            return Err(format!(
                "suite pin annotation profile root is duplicated: {:?}",
                profile.root
            ));
        }
        if !fixture_roots
            .iter()
            .any(|fixture_root| root.starts_with(Path::new(fixture_root)))
        {
            return Err(format!(
                "suite pin annotation profile {:?} is outside every declared fixture root",
                profile.root
            ));
        }
        match (profile.phase, profile.backend) {
            (AnnotationPhase::Translation, AnnotationBackend::Any)
            | (
                AnnotationPhase::Verification,
                AnnotationBackend::Silicon | AnnotationBackend::Carbon,
            ) => {}
            _ => {
                return Err(format!(
                    "suite pin annotation profile {:?} has incompatible phase/backend",
                    profile.root
                ));
            }
        }
    }
    for fixture_root in fixture_roots {
        if !annotation_roots.contains(fixture_root) {
            return Err(format!(
                "suite pin fixture root {fixture_root:?} has no explicit base annotation profile"
            ));
        }
    }
    Ok(())
}

fn information_flow_profile_for_fixture(
    pin: &NaginiSuitePin,
    fixture: &Path,
) -> Result<InformationFlowVerificationProfile, String> {
    let matches = pin
        .fixture_profiles
        .iter()
        .filter(|profile| fixture.starts_with(Path::new(&profile.root)))
        .collect::<Vec<_>>();
    let [profile] = matches.as_slice() else {
        return Err(format!(
            "fixture {:?} must belong to exactly one explicitly profiled suite root",
            fixture.to_string_lossy()
        ));
    };
    Ok(profile.information_flow.into())
}

fn selected_annotation_profile_for_fixture(
    pin: &NaginiSuitePin,
    fixture: &Path,
) -> Result<SelectedAnnotationProfile, String> {
    let profile = pin
        .conformance_environment
        .annotation_profiles
        .iter()
        .filter(|profile| fixture.starts_with(Path::new(&profile.root)))
        .max_by_key(|profile| Path::new(&profile.root).components().count())
        .ok_or_else(|| {
            format!(
                "fixture {:?} has no explicit conformance annotation profile",
                fixture.to_string_lossy()
            )
        })?;
    Ok(SelectedAnnotationProfile {
        root: profile.root.clone(),
        python: pin.conformance_environment.python.clone(),
        nagini_tag: pin.conformance_environment.nagini_tag.clone(),
        nagini_commit: pin.conformance_environment.nagini_commit.clone(),
        phase: profile.phase,
        backend: profile.backend,
    })
}

fn evaluate_pinned_annotations(
    pin: &NaginiSuitePin,
    fixture: &Path,
    source: &str,
) -> Result<AnnotationProfileEvaluation, String> {
    let selected = selected_annotation_profile_for_fixture(pin, fixture)?;
    evaluate_ignore_file_annotations(source, selected)
}

fn retained_annotation_profile(
    evaluation: AnnotationProfileEvaluation,
) -> Option<AnnotationProfileEvaluation> {
    (!evaluation.ignore_file_conditions.is_empty()).then_some(evaluation)
}

fn profile_ignored_scalar(
    fixture: &str,
    evaluation: AnnotationProfileEvaluation,
) -> ScalarConformanceResult {
    ScalarConformanceResult {
        schema: "maledictus-nagini-scalar-conformance/v3".to_owned(),
        fixture: fixture.to_owned(),
        expected: Vec::new(),
        actual: Vec::new(),
        passed: false,
        analysis_kind: ConformanceMatchKind::ProfileIgnored,
        python_typechecker: None,
        python_typecheck_diagnostics: Vec::new(),
        annotation_profile: Some(evaluation),
    }
}

fn profile_ignored_heap(
    fixture: &str,
    evaluation: AnnotationProfileEvaluation,
) -> HeapConformanceResult {
    HeapConformanceResult {
        schema: "maledictus-nagini-heap-conformance/v2".to_owned(),
        fixture: fixture.to_owned(),
        expected: Vec::new(),
        actual: Vec::new(),
        passed: false,
        semantic_verified: false,
        analysis_kind: ConformanceMatchKind::ProfileIgnored,
        python_typechecker: None,
        python_typecheck_diagnostics: Vec::new(),
        annotation_profile: Some(evaluation),
    }
}

fn profile_ignored_reference(
    fixture: &str,
    evaluation: AnnotationProfileEvaluation,
) -> ReferenceConformanceResult {
    ReferenceConformanceResult {
        schema: "maledictus-nagini-reference-conformance/v1".to_owned(),
        fixture: fixture.to_owned(),
        expected: Vec::new(),
        actual: Vec::new(),
        passed: false,
        annotation_profile: Some(evaluation),
    }
}

pub fn inventory_pinned_nagini(
    suite_root: &Path,
    pin_path: &Path,
) -> Result<NaginiInventory, String> {
    let pin = load_pin(pin_path)?;
    let actual_commit = git_commit(suite_root)?;
    if actual_commit != pin.commit {
        return Err(format!(
            "Nagini suite commit mismatch: expected {}, found {actual_commit}",
            pin.commit
        ));
    }

    let mut inventory = NaginiInventory {
        schema: "maledictus-nagini-inventory/v1".to_owned(),
        project: pin.project,
        tag: pin.tag,
        commit: pin.commit,
        python_files: 0,
        annotations: AnnotationCounts::default(),
        areas: BTreeMap::new(),
    };
    for fixture_root in pin.fixture_roots {
        let root = suite_root.join(&fixture_root);
        if !root.is_dir() {
            return Err(format!(
                "pinned fixture root is missing: {}",
                root.display()
            ));
        }
        let area = Path::new(&fixture_root)
            .components()
            .nth(1)
            .map(|component| component.as_os_str().to_string_lossy().into_owned())
            .unwrap_or(fixture_root);
        let mut files = Vec::new();
        collect_python_files(&root, &mut files)?;
        *inventory.areas.entry(area).or_default() += files.len() as u64;
        inventory.python_files += files.len() as u64;
        for file in files {
            scan_annotations(&file, &mut inventory.annotations)?;
        }
    }
    Ok(inventory)
}

pub fn check_pinned_scalar_fixture(
    suite_root: &Path,
    pin_path: &Path,
    fixture: &str,
) -> Result<ScalarConformanceResult, String> {
    let pin = load_pin(pin_path)?;
    let actual_commit = git_commit(suite_root)?;
    if actual_commit != pin.commit {
        return Err(format!(
            "Nagini suite commit mismatch: expected {}, found {actual_commit}",
            pin.commit
        ));
    }
    let relative = Path::new(fixture);
    if relative.is_absolute()
        || relative
            .components()
            .any(|part| matches!(part, std::path::Component::ParentDir))
    {
        return Err(format!("fixture path escapes suite root: {fixture:?}"));
    }
    let path = suite_root.join(relative);
    let source = fs::read_to_string(&path)
        .map_err(|error| format!("cannot read scalar fixture {}: {error}", path.display()))?;
    let annotations = evaluate_pinned_annotations(&pin, relative, &source)?;
    if annotations.ignored {
        return Ok(profile_ignored_scalar(fixture, annotations));
    }
    let information_flow = information_flow_profile_for_fixture(&pin, relative)?;
    check_pinned_scalar_source(
        suite_root,
        relative,
        fixture,
        &source,
        information_flow,
        annotations,
    )
}

fn check_pinned_scalar_source(
    suite_root: &Path,
    relative: &Path,
    fixture: &str,
    source: &str,
    information_flow: InformationFlowVerificationProfile,
    annotations: AnnotationProfileEvaluation,
) -> Result<ScalarConformanceResult, String> {
    let annotation_profile = retained_annotation_profile(annotations);
    let expected = parse_expected_diagnostics(source)?;
    let position_failure =
        validate_contract_positions_with_profile(source, fixture, information_flow).err();
    if let Some(failure) = position_failure.as_ref()
        && failure.code == TYPE_ERROR_DEAD_CODE
    {
        let mut result = check_pinned_source_wellformedness_rejection(
            suite_root,
            fixture,
            &expected,
            failure.clone(),
        )?;
        result.annotation_profile = annotation_profile;
        return Ok(result);
    }
    if expected
        .iter()
        .any(|diagnostic| is_typecheck_expectation(&diagnostic.code))
    {
        let mut result = check_pinned_typecheck_rejection(suite_root, fixture, &expected)?;
        result.annotation_profile = annotation_profile;
        return Ok(result);
    }
    if let Some(failure) = position_failure {
        let mut result =
            check_pinned_source_wellformedness_rejection(suite_root, fixture, &expected, failure)?;
        result.annotation_profile = annotation_profile;
        return Ok(result);
    }
    let mut result = match selected_symbols_from_fixture(relative) {
        Some(selected) => check_scalar_source_internal(source, fixture, Some(&selected), true),
        None => check_scalar_source_internal(source, fixture, None, true),
    }?;
    result.annotation_profile = annotation_profile;
    Ok(result)
}

fn check_pinned_source_wellformedness_rejection(
    suite_root: &Path,
    fixture: &str,
    expected: &[ExpectedDiagnostic],
    failure: ContractPositionFailure,
) -> Result<ScalarConformanceResult, String> {
    let fixture_path = suite_root.join(fixture);
    let source_root = fixture_path
        .parent()
        .ok_or_else(|| format!("pinned well-formedness fixture has no parent: {fixture:?}"))?;
    let checked_path = fixture_path
        .file_name()
        .ok_or_else(|| format!("pinned well-formedness fixture has no file name: {fixture:?}"))?
        .to_string_lossy()
        .into_owned();
    let checked = typecheck_request_sources(
        source_root,
        &[SourceFile {
            path: checked_path,
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        &[],
    )
    .map_err(|error| format!("{}: {}", error.code, error.message))?
    .ok_or_else(|| "well-formedness conformance requires strict Python typechecking".to_owned())?;
    validate_conformance_typechecker_identity(&checked.identity)?;
    let only_missing_returns = !checked.diagnostics.is_empty()
        && checked
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code == "frontend.python.typecheck.return");
    let only_wildcard_read_consequences = failure.code == WILDCARD_VARIABLE_READ
        && !checked.diagnostics.is_empty()
        && checked.diagnostics.iter().all(|diagnostic| {
            diagnostic.code == "frontend.python.typecheck.no-any-return"
                && diagnostic.line == Some(failure.line)
        });
    // A function-local import is rejected by the verified source-language pass before that
    // statement can contribute an imported binding. Mypy consequently reports one or more
    // same-location `misc` diagnostics because the imported module is deliberately absent from
    // this closed invocation. Those are consequences of the already-invalid statement, not an
    // independent reason to hide the more precise source rejection. Different diagnostic codes
    // or locations remain typechecker-first.
    let only_local_import_consequences =
        only_same_line_local_import_typecheck_consequences(&failure, &checked.diagnostics);
    let only_rejected_expression_consequences =
        only_same_line_rejected_expression_typecheck_consequences(&failure, &checked.diagnostics);
    let only_private_field_ignore_consequences =
        only_private_field_unused_ignore_consequences(&failure, &checked.diagnostics);
    let only_io_existential_contract_consequences = failure.code
        == EXISTENTIAL_DEFINITION_TYPE_MISMATCH
        && checked
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "frontend.python.typecheck.return")
        && checked.diagnostics.iter().all(|diagnostic| {
            diagnostic.code == "frontend.python.typecheck.return"
                || (diagnostic.code == "frontend.python.typecheck.comparison-overlap"
                    && diagnostic.line.is_some_and(|line| line > failure.line))
        });
    let source_failure_precedes_typecheck = (failure.code
        == "invalid.program:function.return.missing"
        && only_missing_returns)
        // Mypy assigns the wildcard binding `_` an Any-like placeholder and therefore reports a
        // secondary no-any-return error when that invalid wildcard is read. Nagini rejects the
        // read itself at the same source line, so retain both facts while giving the primary
        // source-language violation precedence.
        || only_wildcard_read_consequences
        || only_local_import_consequences
        || only_rejected_expression_consequences
        // The pinned private-field translation fixture predates strict mypy's unused-ignore
        // diagnostic and contains verifier-only ignores on valid class-internal accesses. Keep
        // those diagnostics in the report, but do not let that cosmetic category hide the later
        // source-bound illegal external access. Any real type error still remains typecheck-first.
        || only_private_field_ignore_consequences
        // A GetGhostOutput use is checked only after all IO relation declarations have passed
        // their source-bound shape validation. Strict mypy still records their deliberately
        // bodyless executable representation; preserve that evidence without hiding the later
        // malformed use.
        || (failure
            .code
            .starts_with("invalid.program:invalid.get_ghost_output.")
            && only_missing_returns)
        // ContractOnly IO clients deliberately omit executable return bodies. Preserve strict
        // mypy's missing-return evidence, but let the source-bound existential definition error
        // identify the malformed verifier contract. Any different typechecking error remains
        // typecheck-first.
        || (matches!(
            failure.code,
            EXISTENTIAL_USE_UNDEFINED | EXISTENTIAL_DEFINITION_TYPE_MISMATCH
        ) && only_missing_returns)
        // The SIF concurrency restriction is selected by the typed suite profile and precedes
        // verification of verifier-only method bodies. Preserve strict mypy's missing-return
        // evidence without hiding the source-bound concurrency failure.
        || (failure.code == CONCURRENCY_IN_SIF && only_missing_returns)
        || only_io_existential_contract_consequences
        // Nagini's thread fixtures declare verifier-only target methods with `pass` bodies.
        // Their missing-return diagnostics are an artifact of executable Python typing; the
        // source-bound thread API rejection remains the intended, later source diagnostic.
        || (matches!(
            failure.code,
            "invalid.program:invalid.thread.creation"
                | "invalid.program:invalid.thread.start"
                | "invalid.program:invalid.thread.join"
                | "invalid.program:invalid.get.method.use"
                | "invalid.program:invalid.arg.use"
        ) && only_missing_returns)
        // IO declarations are verifier relations rather than executable Python functions.
        // Their source-bound signature checker is authoritative for the relation shape; retain
        // strict-mypy diagnostics as evidence, but do not let executable-body diagnostics hide
        // a prior malformed-relation result.
        || failure
            .code
            .starts_with("invalid.program:invalid.io_operation.");
    if !checked.passed() && !source_failure_precedes_typecheck {
        return Err(format!(
            "strict Python typechecking rejected before contract-position validation: {:?}",
            checked.diagnostics
        ));
    }
    let mut expected = expected.to_vec();
    expected.sort();
    let actual = vec![ExpectedDiagnostic {
        code: failure.code.to_owned(),
        line: failure.line,
    }];
    Ok(ScalarConformanceResult {
        schema: "maledictus-nagini-scalar-conformance/v3".to_owned(),
        fixture: fixture.to_owned(),
        passed: expected == actual,
        expected,
        actual,
        analysis_kind: ConformanceMatchKind::SourceWellformednessRejection,
        python_typechecker: Some(checked.identity),
        python_typecheck_diagnostics: checked.diagnostics,
        annotation_profile: None,
    })
}

fn only_same_line_local_import_typecheck_consequences(
    failure: &ContractPositionFailure,
    diagnostics: &[Diagnostic],
) -> bool {
    failure.code == LOCAL_IMPORT
        && !diagnostics.is_empty()
        && diagnostics.iter().all(|diagnostic| {
            diagnostic.code == "frontend.python.typecheck.misc"
                && diagnostic.line == Some(failure.line)
        })
}

fn only_same_line_rejected_expression_typecheck_consequences(
    failure: &ContractPositionFailure,
    diagnostics: &[Diagnostic],
) -> bool {
    failure.code == INVALID_CONTRACT_POSITION
        && !diagnostics.is_empty()
        && diagnostics
            .iter()
            .all(|diagnostic| diagnostic.line == Some(failure.line))
}

fn only_private_field_unused_ignore_consequences(
    failure: &ContractPositionFailure,
    diagnostics: &[Diagnostic],
) -> bool {
    failure.code == PRIVATE_FIELD_ACCESS
        && !diagnostics.is_empty()
        && diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code == "frontend.python.typecheck.unused-ignore")
}

fn check_pinned_typecheck_rejection(
    suite_root: &Path,
    fixture: &str,
    expected: &[ExpectedDiagnostic],
) -> Result<ScalarConformanceResult, String> {
    if expected
        .iter()
        .any(|diagnostic| !is_typecheck_expectation(&diagnostic.code))
    {
        return Err(
            "type-error expectations cannot be mixed with semantic proof expectations because production issuance stops after static type rejection"
                .to_owned(),
        );
    }
    let fixture_path = suite_root.join(fixture);
    let source_root = fixture_path
        .parent()
        .ok_or_else(|| format!("pinned type-error fixture has no source parent: {fixture:?}"))?;
    let checked_path = fixture_path
        .file_name()
        .ok_or_else(|| format!("pinned type-error fixture has no file name: {fixture:?}"))?
        .to_string_lossy()
        .into_owned();
    let source_file = SourceFile {
        path: checked_path.clone(),
        language: "python".to_owned(),
        symbols: Vec::new(),
    };
    finish_typecheck_rejection(
        fixture,
        &checked_path,
        expected,
        typecheck_request_sources(source_root, &[source_file], &[]),
    )
}

fn finish_typecheck_rejection(
    fixture: &str,
    checked_path: &str,
    expected: &[ExpectedDiagnostic],
    checked: Result<Option<PythonTypecheckVerification>, PythonTypecheckFailure>,
) -> Result<ScalarConformanceResult, String> {
    let verification = checked
        .map_err(|failure| format!("{}: {}", failure.code, failure.message))?
        .ok_or_else(|| {
            "production Python typechecker returned no result for a Python fixture".to_owned()
        })?;
    typecheck_rejection_result(fixture, checked_path, expected, verification)
}

fn is_typecheck_expectation(code: &str) -> bool {
    code.starts_with("type.error:")
}

fn typecheck_rejection_result(
    fixture: &str,
    checked_path: &str,
    expected: &[ExpectedDiagnostic],
    verification: PythonTypecheckVerification,
) -> Result<ScalarConformanceResult, String> {
    validate_conformance_typechecker_identity(&verification.identity)?;
    let normalized_checked_path = checked_path.replace('\\', "/");
    let normalized_fixture = fixture.replace('\\', "/");
    let mut retained_diagnostics = verification.diagnostics.clone();
    let mut actual = Vec::with_capacity(verification.diagnostics.len());
    for (diagnostic, retained) in verification
        .diagnostics
        .iter()
        .zip(&mut retained_diagnostics)
    {
        if diagnostic.severity != "error" {
            return Err(format!(
                "production Python typechecker emitted unsupported severity {:?}",
                diagnostic.severity
            ));
        }
        let path = diagnostic.path.as_deref().ok_or_else(|| {
            "production Python typechecker emitted an unlocated diagnostic".to_owned()
        })?;
        if path.replace('\\', "/") != normalized_checked_path {
            return Err(format!(
                "production Python typechecker diagnostic escaped requested fixture: expected {normalized_checked_path:?}, found {path:?}"
            ));
        }
        retained.path = Some(normalized_fixture.clone());
        let line = diagnostic.line.ok_or_else(|| {
            format!(
                "production Python typechecker emitted a diagnostic without a source line: {diagnostic:?}"
            )
        })?;
        let mypy_code = diagnostic
            .code
            .strip_prefix("frontend.python.typecheck.")
            .ok_or_else(|| {
                format!(
                    "production Python typechecker emitted noncanonical code {:?}",
                    diagnostic.code
                )
            })?;
        actual.push(ExpectedDiagnostic {
            code: nagini_typecheck_diagnostic_code(&diagnostic.message, mypy_code),
            line,
        });
    }
    let mut expected = expected.to_vec();
    expected.sort();
    actual.sort();
    Ok(ScalarConformanceResult {
        schema: "maledictus-nagini-scalar-conformance/v3".to_owned(),
        fixture: fixture.to_owned(),
        passed: expected == actual,
        expected,
        actual,
        analysis_kind: ConformanceMatchKind::ProductionTypecheckRejection,
        python_typechecker: Some(verification.identity),
        python_typecheck_diagnostics: retained_diagnostics,
        annotation_profile: None,
    })
}

fn nagini_typecheck_diagnostic_code(message: &str, mypy_code: &str) -> String {
    if mypy_code == "no-untyped-def" && message == "Function is missing a return type annotation" {
        // Nagini 1.3.1 reports this same source defect from its typed-AST boundary rather than
        // exposing mypy's diagnostic spelling. Preserve the production mypy diagnostic in
        // `python_typecheck_diagnostics`; only the pinned compatibility projection is canonicalized.
        return "type.error:Encountered Any type. Type annotation missing?".to_owned();
    }
    format!("type.error:{message}  [{mypy_code}]")
}

fn validate_conformance_typechecker_identity(
    identity: &PythonTypecheckerIdentity,
) -> Result<(), String> {
    if identity.checker != "mypy"
        || identity.checker_version != MYPY_VERSION
        || identity.profile != PYTHON_TYPECHECK_PROFILE
    {
        return Err(format!(
            "production Python typechecker identity is not the pinned conformance checker: {:?} {} profile {:?}",
            identity.checker, identity.checker_version, identity.profile
        ));
    }
    Ok(())
}

pub fn check_pinned_scalar_suite(
    suite_root: &Path,
    pin_path: &Path,
    manifest_path: &Path,
) -> Result<ScalarSuiteConformanceResult, String> {
    let source = fs::read_to_string(manifest_path).map_err(|error| {
        format!(
            "cannot read scalar fixture manifest {}: {error}",
            manifest_path.display()
        )
    })?;
    let manifest: ScalarFixtureManifest = serde_json::from_str(&source).map_err(|error| {
        format!(
            "invalid scalar fixture manifest {}: {error}",
            manifest_path.display()
        )
    })?;
    if manifest.schema != "maledictus-scalar-fixtures/v1" {
        return Err(format!(
            "unsupported scalar fixture manifest schema {:?}",
            manifest.schema
        ));
    }
    if manifest.fixtures.is_empty() {
        return Err("scalar fixture manifest cannot be empty".to_owned());
    }
    let unique: BTreeSet<_> = manifest.fixtures.iter().collect();
    if unique.len() != manifest.fixtures.len() {
        return Err("scalar fixture manifest contains duplicate paths".to_owned());
    }

    let mut fixtures = Vec::with_capacity(manifest.fixtures.len());
    for fixture in manifest.fixtures {
        fixtures.push(check_pinned_scalar_fixture(suite_root, pin_path, &fixture)?);
    }
    let passed = fixtures.iter().all(|fixture| fixture.passed);
    Ok(ScalarSuiteConformanceResult {
        schema: "maledictus-nagini-scalar-suite-conformance/v2".to_owned(),
        fixtures,
        passed,
    })
}

pub fn check_pinned_heap_fixture(
    suite_root: &Path,
    pin_path: &Path,
    fixture: &str,
) -> Result<HeapConformanceResult, String> {
    let pin = load_pin(pin_path)?;
    let actual_commit = git_commit(suite_root)?;
    if actual_commit != pin.commit {
        return Err(format!(
            "Nagini suite commit mismatch: expected {}, found {actual_commit}",
            pin.commit
        ));
    }
    let relative = Path::new(fixture);
    if relative.is_absolute()
        || relative
            .components()
            .any(|part| matches!(part, std::path::Component::ParentDir))
    {
        return Err(format!("fixture path escapes suite root: {fixture:?}"));
    }
    let path = suite_root.join(relative);
    let source = fs::read_to_string(&path)
        .map_err(|error| format!("cannot read heap fixture {}: {error}", path.display()))?;
    let annotations = evaluate_pinned_annotations(&pin, relative, &source)?;
    if annotations.ignored {
        return Ok(profile_ignored_heap(fixture, annotations));
    }
    let information_flow = information_flow_profile_for_fixture(&pin, relative)?;
    let mut result = check_pinned_heap_source_graph(
        suite_root,
        &path,
        &source,
        fixture,
        selected_symbols_from_fixture(relative).as_ref(),
        information_flow,
    )?;
    result.annotation_profile = retained_annotation_profile(annotations);
    Ok(result)
}

pub fn check_pinned_heap_suite(
    suite_root: &Path,
    pin_path: &Path,
    manifest_path: &Path,
) -> Result<HeapSuiteConformanceResult, String> {
    let source = fs::read_to_string(manifest_path).map_err(|error| {
        format!(
            "cannot read heap fixture manifest {}: {error}",
            manifest_path.display()
        )
    })?;
    let manifest: ScalarFixtureManifest = serde_json::from_str(&source).map_err(|error| {
        format!(
            "invalid heap fixture manifest {}: {error}",
            manifest_path.display()
        )
    })?;
    if manifest.schema != "maledictus-heap-fixtures/v1" {
        return Err(format!(
            "unsupported heap fixture manifest schema {:?}",
            manifest.schema
        ));
    }
    if manifest.fixtures.is_empty() {
        return Err("heap fixture manifest cannot be empty".to_owned());
    }
    let unique: BTreeSet<_> = manifest.fixtures.iter().collect();
    if unique.len() != manifest.fixtures.len() {
        return Err("heap fixture manifest contains duplicate paths".to_owned());
    }
    let mut fixtures = Vec::with_capacity(manifest.fixtures.len());
    for fixture in manifest.fixtures {
        fixtures.push(check_pinned_heap_fixture(suite_root, pin_path, &fixture)?);
    }
    let passed = fixtures.iter().all(|fixture| fixture.passed);
    Ok(HeapSuiteConformanceResult {
        schema: "maledictus-nagini-heap-suite-conformance/v1".to_owned(),
        fixtures,
        passed,
    })
}

pub fn check_pinned_reference_fixture(
    suite_root: &Path,
    pin_path: &Path,
    fixture: &str,
) -> Result<ReferenceConformanceResult, String> {
    let pin = load_pin(pin_path)?;
    let actual_commit = git_commit(suite_root)?;
    if actual_commit != pin.commit {
        return Err(format!(
            "Nagini suite commit mismatch: expected {}, found {actual_commit}",
            pin.commit
        ));
    }
    let relative = Path::new(fixture);
    if relative.is_absolute()
        || relative
            .components()
            .any(|part| matches!(part, std::path::Component::ParentDir))
    {
        return Err(format!("fixture path escapes suite root: {fixture:?}"));
    }
    let path = suite_root.join(relative);
    let source = fs::read_to_string(&path)
        .map_err(|error| format!("cannot read reference fixture {}: {error}", path.display()))?;
    let annotations = evaluate_pinned_annotations(&pin, relative, &source)?;
    if annotations.ignored {
        return Ok(profile_ignored_reference(fixture, annotations));
    }
    validate_reference_source_ownership(&source, fixture)
        .map_err(|error| format!("{}: {}", error.code, error.message))?;
    let information_flow = information_flow_profile_for_fixture(&pin, relative)?;
    if let Err(failure) =
        validate_contract_positions_with_profile(&source, fixture, information_flow)
    {
        let expected = parse_expected_diagnostics(&source)?;
        let checked =
            check_pinned_source_wellformedness_rejection(suite_root, fixture, &expected, failure)?;
        return Ok(ReferenceConformanceResult {
            schema: "maledictus-nagini-reference-conformance/v1".to_owned(),
            fixture: fixture.to_owned(),
            expected: checked.expected,
            actual: checked.actual,
            passed: checked.passed,
            annotation_profile: retained_annotation_profile(annotations),
        });
    }
    let mut result = check_reference_source(&source, fixture)?;
    result.annotation_profile = retained_annotation_profile(annotations);
    Ok(result)
}

pub fn check_pinned_reference_suite(
    suite_root: &Path,
    pin_path: &Path,
    manifest_path: &Path,
) -> Result<ReferenceSuiteConformanceResult, String> {
    let source = fs::read_to_string(manifest_path).map_err(|error| {
        format!(
            "cannot read reference fixture manifest {}: {error}",
            manifest_path.display()
        )
    })?;
    let manifest: ScalarFixtureManifest = serde_json::from_str(&source).map_err(|error| {
        format!(
            "invalid reference fixture manifest {}: {error}",
            manifest_path.display()
        )
    })?;
    if manifest.schema != "maledictus-reference-fixtures/v1" {
        return Err(format!(
            "unsupported reference fixture manifest schema {:?}",
            manifest.schema
        ));
    }
    if manifest.fixtures.is_empty() {
        return Err("reference fixture manifest cannot be empty".to_owned());
    }
    let unique: BTreeSet<_> = manifest.fixtures.iter().collect();
    if unique.len() != manifest.fixtures.len() {
        return Err("reference fixture manifest contains duplicate paths".to_owned());
    }
    let mut fixtures = Vec::with_capacity(manifest.fixtures.len());
    for fixture in manifest.fixtures {
        fixtures.push(check_pinned_reference_fixture(
            suite_root, pin_path, &fixture,
        )?);
    }
    let passed = fixtures.iter().all(|fixture| fixture.passed);
    Ok(ReferenceSuiteConformanceResult {
        schema: "maledictus-nagini-reference-suite-conformance/v1".to_owned(),
        fixtures,
        passed,
    })
}

pub fn classify_pinned_scalar_tree(
    suite_root: &Path,
    pin_path: &Path,
    fixture_root: &str,
) -> Result<ScalarClassificationReport, String> {
    classify_pinned_scalar_tree_with_progress(suite_root, pin_path, fixture_root, &mut |_| {})
}

fn classify_pinned_scalar_tree_with_progress(
    suite_root: &Path,
    pin_path: &Path,
    fixture_root: &str,
    progress: &mut dyn FnMut(ClassificationProgressEvent),
) -> Result<ScalarClassificationReport, String> {
    let mut forward_progress = |event| {
        progress(event);
        Ok(())
    };
    classify_pinned_scalar_tree_with_progress_and_cache(
        suite_root,
        pin_path,
        fixture_root,
        &mut forward_progress,
        None,
    )
}

fn classify_pinned_scalar_tree_with_progress_and_cache(
    suite_root: &Path,
    pin_path: &Path,
    fixture_root: &str,
    progress: &mut dyn FnMut(ClassificationProgressEvent) -> Result<(), String>,
    cache: Option<&ClassifierCache>,
) -> Result<ScalarClassificationReport, String> {
    let pin = match cache {
        Some(cache) => cache.pin.clone(),
        None => load_pin(pin_path)?,
    };
    let actual_commit = match cache {
        Some(cache) => cache.suite_commit.clone(),
        None => git_commit(suite_root)?,
    };
    if actual_commit != pin.commit {
        return Err(format!(
            "Nagini suite commit mismatch: expected {}, found {actual_commit}",
            pin.commit
        ));
    }
    let relative_root = Path::new(fixture_root);
    if relative_root.is_absolute()
        || relative_root
            .components()
            .any(|part| matches!(part, std::path::Component::ParentDir))
    {
        return Err(format!("fixture root escapes suite root: {fixture_root:?}"));
    }
    let root = suite_root.join(relative_root);
    if !root.is_dir() {
        return Err(format!(
            "fixture root is not a directory: {}",
            root.display()
        ));
    }
    let mut paths = Vec::new();
    collect_nagini_test_files(&root, &mut paths)?;
    paths.sort();

    let mut report = ScalarClassificationReport {
        schema: "maledictus-nagini-scalar-classification/v3".to_owned(),
        suite_commit: actual_commit,
        root: fixture_root.replace('\\', "/"),
        matched: 0,
        semantic_matched: 0,
        production_typecheck_rejection_matched: 0,
        source_wellformedness_rejection_matched: 0,
        production_typecheck_divergent: 0,
        mismatched: 0,
        refused: 0,
        profile_ignored: 0,
        fixtures: Vec::with_capacity(paths.len()),
    };
    let total =
        u64::try_from(paths.len()).map_err(|_| "scalar fixture count exceeds u64".to_owned())?;
    for (index, path) in paths.into_iter().enumerate() {
        let relative = path.strip_prefix(suite_root).map_err(|_| {
            format!(
                "fixture escaped suite root unexpectedly: {}",
                path.display()
            )
        })?;
        let fixture = relative.to_string_lossy().replace('\\', "/");
        progress(ClassificationProgressEvent::FixtureStarted {
            lane: ClassificationLane::Scalar,
            root: report.root.clone(),
            fixture: fixture.clone(),
            ordinal: u64::try_from(index + 1)
                .map_err(|_| "scalar fixture ordinal exceeds u64".to_owned())?,
            total,
        })?;
        let source = fs::read_to_string(&path)
            .map_err(|error| format!("cannot read scalar fixture {}: {error}", path.display()))?;
        let cached = match cache {
            Some(cache) => cache.load(ClassificationLane::Scalar, &fixture, &path, &source)?,
            None => None,
        };
        let classification = match cached {
            Some(classification) => classification,
            None => {
                let information_flow = information_flow_profile_for_fixture(&pin, relative)?;
                let annotations = evaluate_pinned_annotations(&pin, relative, &source)?;
                let annotation_audit = retained_annotation_profile(annotations.clone());
                let checked = if annotations.ignored {
                    Ok(profile_ignored_scalar(&fixture, annotations))
                } else {
                    check_pinned_scalar_source(
                        suite_root,
                        relative,
                        &fixture,
                        &source,
                        information_flow,
                        annotations,
                    )
                };
                let mut classification = scalar_fixture_classification(&fixture, checked)?;
                if classification.annotation_profile.is_none() {
                    classification.annotation_profile = annotation_audit;
                }
                if let Some(cache) = cache {
                    let typechecker_required =
                        scalar_source_may_invoke_typechecker(&source, &fixture, information_flow);
                    if !typechecker_required || classification.python_typechecker.is_some() {
                        cache.store(
                            ClassificationLane::Scalar,
                            &fixture,
                            &path,
                            classification.python_typechecker.clone(),
                            &classification,
                        )?;
                    }
                }
                classification
            }
        };
        append_scalar_fixture(&mut report, classification)?;
    }
    validate_scalar_classification_counts(&report)?;
    progress(ClassificationProgressEvent::LaneCompleted {
        lane: ClassificationLane::Scalar,
        root: report.root.clone(),
        total,
    })?;
    Ok(report)
}

fn scalar_source_may_invoke_typechecker(
    source: &str,
    fixture: &str,
    information_flow: InformationFlowVerificationProfile,
) -> bool {
    validate_contract_positions_with_profile(source, fixture, information_flow).is_err()
        || parse_expected_diagnostics(source)
            .map(|expected| {
                expected
                    .iter()
                    .any(|diagnostic| is_typecheck_expectation(&diagnostic.code))
            })
            .unwrap_or(false)
}

fn scalar_fixture_classification(
    fixture: &str,
    checked: Result<ScalarConformanceResult, String>,
) -> Result<ScalarFixtureClassification, String> {
    let classification = match checked {
        Ok(result) if result.analysis_kind == ConformanceMatchKind::ProfileIgnored => {
            ScalarFixtureClassification {
                fixture: fixture.to_owned(),
                status: "profile-ignored".to_owned(),
                detail: "fixture excluded by an active source annotation under the explicitly selected conformance profile"
                    .to_owned(),
                expected: result.expected,
                actual: result.actual,
                match_kind: Some(ConformanceMatchKind::ProfileIgnored),
                python_typechecker: result.python_typechecker,
                python_typecheck_diagnostics: result.python_typecheck_diagnostics,
                annotation_profile: result.annotation_profile,
            }
        }
        Ok(result) if result.passed => {
            if result.analysis_kind == ConformanceMatchKind::SupersededUpstreamUnsupported {
                return Err(
                    "scalar conformance cannot classify a superseded upstream unsupported result"
                        .to_owned(),
                );
            }
            ScalarFixtureClassification {
                fixture: fixture.to_owned(),
                status: "matched".to_owned(),
                detail: format!("{} expected diagnostics matched", result.expected.len()),
                expected: result.expected,
                actual: result.actual,
                match_kind: Some(result.analysis_kind),
                python_typechecker: result.python_typechecker,
                python_typecheck_diagnostics: result.python_typecheck_diagnostics,
                annotation_profile: result.annotation_profile,
            }
        }
        Ok(result) => ScalarFixtureClassification {
            fixture: fixture.to_owned(),
            status: if result.analysis_kind == ConformanceMatchKind::ProductionTypecheckRejection {
                "production-typecheck-divergence".to_owned()
            } else {
                "mismatched".to_owned()
            },
            detail: format!("expected {:?}, actual {:?}", result.expected, result.actual),
            expected: result.expected,
            actual: result.actual,
            match_kind: None,
            python_typechecker: result.python_typechecker,
            python_typecheck_diagnostics: result.python_typecheck_diagnostics,
            annotation_profile: result.annotation_profile,
        },
        Err(error) => ScalarFixtureClassification {
            fixture: fixture.to_owned(),
            status: "refused".to_owned(),
            detail: error,
            expected: Vec::new(),
            actual: Vec::new(),
            match_kind: None,
            python_typechecker: None,
            python_typecheck_diagnostics: Vec::new(),
            annotation_profile: None,
        },
    };
    Ok(classification)
}

fn append_scalar_fixture(
    report: &mut ScalarClassificationReport,
    classification: ScalarFixtureClassification,
) -> Result<(), String> {
    match classification.status.as_str() {
        "matched" => {
            report.matched += 1;
            match classification.match_kind {
                Some(ConformanceMatchKind::SemanticVerification) => report.semantic_matched += 1,
                Some(ConformanceMatchKind::ProductionTypecheckRejection) => {
                    report.production_typecheck_rejection_matched += 1;
                }
                Some(ConformanceMatchKind::SourceWellformednessRejection) => {
                    report.source_wellformedness_rejection_matched += 1;
                }
                _ => return Err("matched scalar fixture has invalid analysis kind".to_owned()),
            }
        }
        "production-typecheck-divergence" => report.production_typecheck_divergent += 1,
        "mismatched" => report.mismatched += 1,
        "refused" => report.refused += 1,
        "profile-ignored" => report.profile_ignored += 1,
        _ => return Err("scalar fixture has invalid classification status".to_owned()),
    }
    report.fixtures.push(classification);
    Ok(())
}

fn validate_scalar_classification_counts(
    report: &ScalarClassificationReport,
) -> Result<(), String> {
    if report.matched
        != report.semantic_matched
            + report.production_typecheck_rejection_matched
            + report.source_wellformedness_rejection_matched
    {
        return Err("scalar matched count does not reconcile by analysis kind".to_owned());
    }
    let total = u64::try_from(report.fixtures.len())
        .map_err(|_| "scalar fixture count exceeds u64".to_owned())?;
    if total
        != report.matched
            + report.production_typecheck_divergent
            + report.mismatched
            + report.refused
            + report.profile_ignored
    {
        return Err("scalar classification counts do not cover every fixture".to_owned());
    }
    Ok(())
}

pub fn classify_pinned_heap_tree(
    suite_root: &Path,
    pin_path: &Path,
    fixture_root: &str,
) -> Result<HeapClassificationReport, String> {
    classify_pinned_heap_tree_with_progress(suite_root, pin_path, fixture_root, &mut |_| {})
}

fn classify_pinned_heap_tree_with_progress(
    suite_root: &Path,
    pin_path: &Path,
    fixture_root: &str,
    progress: &mut dyn FnMut(ClassificationProgressEvent),
) -> Result<HeapClassificationReport, String> {
    let mut forward_progress = |event| {
        progress(event);
        Ok(())
    };
    classify_pinned_heap_tree_with_progress_and_cache(
        suite_root,
        pin_path,
        fixture_root,
        &mut forward_progress,
        None,
    )
}

fn classify_pinned_heap_tree_with_progress_and_cache(
    suite_root: &Path,
    pin_path: &Path,
    fixture_root: &str,
    progress: &mut dyn FnMut(ClassificationProgressEvent) -> Result<(), String>,
    cache: Option<&ClassifierCache>,
) -> Result<HeapClassificationReport, String> {
    let pin = match cache {
        Some(cache) => cache.pin.clone(),
        None => load_pin(pin_path)?,
    };
    let actual_commit = match cache {
        Some(cache) => cache.suite_commit.clone(),
        None => git_commit(suite_root)?,
    };
    if actual_commit != pin.commit {
        return Err(format!(
            "Nagini suite commit mismatch: expected {}, found {actual_commit}",
            pin.commit
        ));
    }
    let relative_root = Path::new(fixture_root);
    if relative_root.is_absolute()
        || relative_root
            .components()
            .any(|part| matches!(part, std::path::Component::ParentDir))
    {
        return Err(format!("fixture root escapes suite root: {fixture_root:?}"));
    }
    let root = suite_root.join(relative_root);
    if !root.is_dir() {
        return Err(format!(
            "fixture root is not a directory: {}",
            root.display()
        ));
    }
    let mut paths = Vec::new();
    collect_nagini_test_files(&root, &mut paths)?;
    paths.sort();

    let mut report = HeapClassificationReport {
        schema: "maledictus-nagini-heap-classification/v2".to_owned(),
        suite_commit: actual_commit,
        root: fixture_root.replace('\\', "/"),
        matched: 0,
        superseded_upstream_unsupported: 0,
        mismatched: 0,
        refused: 0,
        profile_ignored: 0,
        fixtures: Vec::with_capacity(paths.len()),
    };
    let total =
        u64::try_from(paths.len()).map_err(|_| "heap fixture count exceeds u64".to_owned())?;
    for (index, path) in paths.into_iter().enumerate() {
        let relative = path.strip_prefix(suite_root).map_err(|_| {
            format!(
                "fixture escaped suite root unexpectedly: {}",
                path.display()
            )
        })?;
        let fixture = relative.to_string_lossy().replace('\\', "/");
        progress(ClassificationProgressEvent::FixtureStarted {
            lane: ClassificationLane::Heap,
            root: report.root.clone(),
            fixture: fixture.clone(),
            ordinal: u64::try_from(index + 1)
                .map_err(|_| "heap fixture ordinal exceeds u64".to_owned())?,
            total,
        })?;
        let source = fs::read_to_string(&path)
            .map_err(|error| format!("cannot read heap fixture {}: {error}", path.display()))?;
        let cached = match cache {
            Some(cache) => cache.load(ClassificationLane::Heap, &fixture, &path, &source)?,
            None => None,
        };
        let classification = match cached {
            Some(classification) => classification,
            None => {
                let selected = selected_symbols_from_fixture(relative);
                let information_flow = information_flow_profile_for_fixture(&pin, relative)?;
                let annotations = evaluate_pinned_annotations(&pin, relative, &source)?;
                let annotation_audit = retained_annotation_profile(annotations.clone());
                let checked = if annotations.ignored {
                    Ok(profile_ignored_heap(&fixture, annotations))
                } else {
                    check_pinned_heap_source_graph(
                        suite_root,
                        &path,
                        &source,
                        &fixture,
                        selected.as_ref(),
                        information_flow,
                    )
                    .map(|mut result| {
                        result.annotation_profile = retained_annotation_profile(annotations);
                        result
                    })
                };
                let mut classification = heap_fixture_classification(&fixture, checked);
                if classification.annotation_profile.is_none() {
                    classification.annotation_profile = annotation_audit;
                }
                if let Some(cache) = cache {
                    let typechecker_required =
                        heap_source_may_invoke_typechecker(&source, &fixture, information_flow);
                    if !typechecker_required || classification.python_typechecker.is_some() {
                        cache.store(
                            ClassificationLane::Heap,
                            &fixture,
                            &path,
                            classification.python_typechecker.clone(),
                            &classification,
                        )?;
                    }
                }
                classification
            }
        };
        append_heap_fixture(&mut report, classification)?;
    }
    progress(ClassificationProgressEvent::LaneCompleted {
        lane: ClassificationLane::Heap,
        root: report.root.clone(),
        total,
    })?;
    Ok(report)
}

fn heap_source_may_invoke_typechecker(
    source: &str,
    fixture: &str,
    information_flow: InformationFlowVerificationProfile,
) -> bool {
    if validate_contract_positions_with_profile(source, fixture, information_flow).is_err() {
        return true;
    }
    parse_expected_diagnostics(source)
        .map(|expected| {
            !expected.is_empty()
                && expected
                    .iter()
                    .all(|diagnostic| diagnostic.code.starts_with("unsupported:"))
        })
        .unwrap_or(false)
}

fn heap_fixture_classification(
    fixture: &str,
    checked: Result<HeapConformanceResult, String>,
) -> ScalarFixtureClassification {
    match checked {
        Ok(result) if result.analysis_kind == ConformanceMatchKind::ProfileIgnored => {
            ScalarFixtureClassification {
                fixture: fixture.to_owned(),
                status: "profile-ignored".to_owned(),
                detail: "fixture excluded by an active source annotation under the explicitly selected conformance profile"
                    .to_owned(),
                expected: result.expected,
                actual: result.actual,
                match_kind: Some(ConformanceMatchKind::ProfileIgnored),
                python_typechecker: result.python_typechecker,
                python_typecheck_diagnostics: result.python_typecheck_diagnostics,
                annotation_profile: result.annotation_profile,
            }
        }
        Ok(result)
            if result.analysis_kind == ConformanceMatchKind::SupersededUpstreamUnsupported =>
        {
            ScalarFixtureClassification {
                fixture: fixture.to_owned(),
                status: "superseded-upstream-unsupported".to_owned(),
                detail: "strictly typed semantic verification supersedes the upstream unsupported diagnostic"
                    .to_owned(),
                expected: result.expected,
                actual: result.actual,
                match_kind: Some(ConformanceMatchKind::SupersededUpstreamUnsupported),
                python_typechecker: result.python_typechecker,
                python_typecheck_diagnostics: result.python_typecheck_diagnostics,
                annotation_profile: result.annotation_profile,
            }
        }
        Ok(result) if result.passed => ScalarFixtureClassification {
            fixture: fixture.to_owned(),
            status: "matched".to_owned(),
            detail: format!("{} expected diagnostics matched", result.expected.len()),
            expected: result.expected,
            actual: result.actual,
            match_kind: Some(result.analysis_kind),
            python_typechecker: result.python_typechecker,
            python_typecheck_diagnostics: result.python_typecheck_diagnostics,
            annotation_profile: result.annotation_profile,
        },
        Ok(result) => ScalarFixtureClassification {
            fixture: fixture.to_owned(),
            status: "mismatched".to_owned(),
            detail: format!("expected {:?}, actual {:?}", result.expected, result.actual),
            expected: result.expected,
            actual: result.actual,
            match_kind: None,
            python_typechecker: result.python_typechecker,
            python_typecheck_diagnostics: result.python_typecheck_diagnostics,
            annotation_profile: result.annotation_profile,
        },
        Err(error) => ScalarFixtureClassification {
            fixture: fixture.to_owned(),
            status: "refused".to_owned(),
            detail: error,
            expected: Vec::new(),
            actual: Vec::new(),
            match_kind: None,
            python_typechecker: None,
            python_typecheck_diagnostics: Vec::new(),
            annotation_profile: None,
        },
    }
}

fn append_heap_fixture(
    report: &mut HeapClassificationReport,
    classification: ScalarFixtureClassification,
) -> Result<(), String> {
    match classification.status.as_str() {
        "matched" => report.matched += 1,
        "superseded-upstream-unsupported" => report.superseded_upstream_unsupported += 1,
        "mismatched" => report.mismatched += 1,
        "refused" => report.refused += 1,
        "profile-ignored" => report.profile_ignored += 1,
        _ => return Err("heap fixture has invalid classification status".to_owned()),
    }
    report.fixtures.push(classification);
    Ok(())
}

pub fn classify_pinned_reference_tree(
    suite_root: &Path,
    pin_path: &Path,
    fixture_root: &str,
) -> Result<ReferenceClassificationReport, String> {
    classify_pinned_reference_tree_with_progress(suite_root, pin_path, fixture_root, &mut |_| {})
}

fn classify_pinned_reference_tree_with_progress(
    suite_root: &Path,
    pin_path: &Path,
    fixture_root: &str,
    progress: &mut dyn FnMut(ClassificationProgressEvent),
) -> Result<ReferenceClassificationReport, String> {
    let mut forward_progress = |event| {
        progress(event);
        Ok(())
    };
    classify_pinned_reference_tree_with_progress_and_cache(
        suite_root,
        pin_path,
        fixture_root,
        &mut forward_progress,
        None,
    )
}

fn classify_pinned_reference_tree_with_progress_and_cache(
    suite_root: &Path,
    pin_path: &Path,
    fixture_root: &str,
    progress: &mut dyn FnMut(ClassificationProgressEvent) -> Result<(), String>,
    cache: Option<&ClassifierCache>,
) -> Result<ReferenceClassificationReport, String> {
    let pin = match cache {
        Some(cache) => cache.pin.clone(),
        None => load_pin(pin_path)?,
    };
    let actual_commit = match cache {
        Some(cache) => cache.suite_commit.clone(),
        None => git_commit(suite_root)?,
    };
    if actual_commit != pin.commit {
        return Err(format!(
            "Nagini suite commit mismatch: expected {}, found {actual_commit}",
            pin.commit
        ));
    }
    let relative_root = Path::new(fixture_root);
    if relative_root.is_absolute()
        || relative_root
            .components()
            .any(|part| matches!(part, std::path::Component::ParentDir))
    {
        return Err(format!("fixture root escapes suite root: {fixture_root:?}"));
    }
    let root = suite_root.join(relative_root);
    if !root.is_dir() {
        return Err(format!(
            "fixture root is not a directory: {}",
            root.display()
        ));
    }
    let mut paths = Vec::new();
    collect_nagini_test_files(&root, &mut paths)?;
    paths.sort();
    let mut report = ReferenceClassificationReport {
        schema: "maledictus-nagini-reference-classification/v1".to_owned(),
        suite_commit: actual_commit,
        root: fixture_root.replace('\\', "/"),
        matched: 0,
        mismatched: 0,
        refused: 0,
        profile_ignored: 0,
        fixtures: Vec::with_capacity(paths.len()),
    };
    let total =
        u64::try_from(paths.len()).map_err(|_| "reference fixture count exceeds u64".to_owned())?;
    for (index, path) in paths.into_iter().enumerate() {
        let relative = path.strip_prefix(suite_root).map_err(|_| {
            format!(
                "fixture escaped suite root unexpectedly: {}",
                path.display()
            )
        })?;
        let fixture = relative.to_string_lossy().replace('\\', "/");
        progress(ClassificationProgressEvent::FixtureStarted {
            lane: ClassificationLane::Reference,
            root: report.root.clone(),
            fixture: fixture.clone(),
            ordinal: u64::try_from(index + 1)
                .map_err(|_| "reference fixture ordinal exceeds u64".to_owned())?,
            total,
        })?;
        let source = fs::read_to_string(&path).map_err(|error| {
            format!("cannot read reference fixture {}: {error}", path.display())
        })?;
        let cached = match cache {
            Some(cache) => cache.load(ClassificationLane::Reference, &fixture, &path, &source)?,
            None => None,
        };
        let classification = match cached {
            Some(classification) => classification,
            None => {
                let information_flow = information_flow_profile_for_fixture(&pin, relative)?;
                let annotations = evaluate_pinned_annotations(&pin, relative, &source)?;
                let annotation_audit = retained_annotation_profile(annotations.clone());
                if annotations.ignored {
                    let classification = reference_fixture_classification(
                        &fixture,
                        Ok(profile_ignored_reference(&fixture, annotations)),
                    );
                    if let Some(cache) = cache {
                        cache.store(
                            ClassificationLane::Reference,
                            &fixture,
                            &path,
                            None,
                            &classification,
                        )?;
                    }
                    append_reference_fixture(&mut report, classification)?;
                    continue;
                }
                let position_failure =
                    validate_contract_positions_with_profile(&source, &fixture, information_flow)
                        .err();
                let checked = match position_failure.clone() {
                    None => check_reference_source(&source, &fixture),
                    Some(failure) => parse_expected_diagnostics(&source).and_then(|expected| {
                        check_pinned_source_wellformedness_rejection(
                            suite_root, &fixture, &expected, failure,
                        )
                        .map(|checked| ReferenceConformanceResult {
                            schema: "maledictus-nagini-reference-conformance/v1".to_owned(),
                            fixture: fixture.clone(),
                            expected: checked.expected,
                            actual: checked.actual,
                            passed: checked.passed,
                            annotation_profile: None,
                        })
                    }),
                };
                let checked = checked.map(|mut result| {
                    result.annotation_profile = retained_annotation_profile(annotations);
                    result
                });
                let mut classification = reference_fixture_classification(&fixture, checked);
                if classification.annotation_profile.is_none() {
                    classification.annotation_profile = annotation_audit;
                }
                if let Some(cache) = cache {
                    let typechecker_identity = if position_failure.is_some() {
                        match probe_classifier_typechecker_identity(suite_root, &fixture, &source) {
                            Ok(identity) => Some(identity),
                            Err(_) if classification.status == "refused" => None,
                            Err(error) => return Err(error),
                        }
                    } else {
                        None
                    };
                    if position_failure.is_none() || typechecker_identity.is_some() {
                        cache.store(
                            ClassificationLane::Reference,
                            &fixture,
                            &path,
                            typechecker_identity,
                            &classification,
                        )?;
                    }
                }
                classification
            }
        };
        append_reference_fixture(&mut report, classification)?;
    }
    progress(ClassificationProgressEvent::LaneCompleted {
        lane: ClassificationLane::Reference,
        root: report.root.clone(),
        total,
    })?;
    Ok(report)
}

fn reference_fixture_classification(
    fixture: &str,
    checked: Result<ReferenceConformanceResult, String>,
) -> ScalarFixtureClassification {
    match checked {
        Ok(result) if result.annotation_profile.as_ref().is_some_and(|profile| profile.ignored) => {
            ScalarFixtureClassification {
                fixture: fixture.to_owned(),
                status: "profile-ignored".to_owned(),
                detail: "fixture excluded by an active source annotation under the explicitly selected conformance profile"
                    .to_owned(),
                expected: result.expected,
                actual: result.actual,
                match_kind: Some(ConformanceMatchKind::ProfileIgnored),
                python_typechecker: None,
                python_typecheck_diagnostics: Vec::new(),
                annotation_profile: result.annotation_profile,
            }
        }
        Ok(result) if result.passed => ScalarFixtureClassification {
            fixture: fixture.to_owned(),
            status: "matched".to_owned(),
            detail: format!("{} expected diagnostics matched", result.expected.len()),
            expected: Vec::new(),
            actual: Vec::new(),
            match_kind: Some(ConformanceMatchKind::SemanticVerification),
            python_typechecker: None,
            python_typecheck_diagnostics: Vec::new(),
            annotation_profile: result.annotation_profile,
        },
        Ok(result) => ScalarFixtureClassification {
            fixture: fixture.to_owned(),
            status: "mismatched".to_owned(),
            detail: format!("expected {:?}, actual {:?}", result.expected, result.actual),
            expected: Vec::new(),
            actual: Vec::new(),
            match_kind: None,
            python_typechecker: None,
            python_typecheck_diagnostics: Vec::new(),
            annotation_profile: result.annotation_profile,
        },
        Err(error) => ScalarFixtureClassification {
            fixture: fixture.to_owned(),
            status: "refused".to_owned(),
            detail: error,
            expected: Vec::new(),
            actual: Vec::new(),
            match_kind: None,
            python_typechecker: None,
            python_typecheck_diagnostics: Vec::new(),
            annotation_profile: None,
        },
    }
}

fn append_reference_fixture(
    report: &mut ReferenceClassificationReport,
    classification: ScalarFixtureClassification,
) -> Result<(), String> {
    match classification.status.as_str() {
        "matched" => report.matched += 1,
        "mismatched" => report.mismatched += 1,
        "refused" => report.refused += 1,
        "profile-ignored" => report.profile_ignored += 1,
        _ => return Err("reference fixture has invalid classification status".to_owned()),
    }
    report.fixtures.push(classification);
    Ok(())
}

pub fn classify_pinned_combined_suite(
    suite_root: &Path,
    pin_path: &Path,
) -> Result<CombinedClassificationReport, String> {
    classify_pinned_combined_suite_with_progress(suite_root, pin_path, &mut |_| {})
}

pub fn classify_pinned_combined_suite_with_progress(
    suite_root: &Path,
    pin_path: &Path,
    progress: &mut dyn FnMut(ClassificationProgressEvent),
) -> Result<CombinedClassificationReport, String> {
    let pin = load_pin(pin_path)?;
    let actual_commit = git_commit(suite_root)?;
    if actual_commit != pin.commit {
        return Err(format!(
            "Nagini suite commit mismatch: expected {}, found {actual_commit}",
            pin.commit
        ));
    }
    let mut paired_reports = Vec::with_capacity(pin.fixture_roots.len());
    for root in &pin.fixture_roots {
        paired_reports.push((
            classify_pinned_scalar_tree_with_progress(suite_root, pin_path, root, progress)?,
            classify_pinned_heap_tree_with_progress(suite_root, pin_path, root, progress)?,
            classify_pinned_reference_tree_with_progress(suite_root, pin_path, root, progress)?,
        ));
    }
    combine_classification_reports(&actual_commit, &pin.fixture_roots, paired_reports)
}

pub fn classify_pinned_combined_suite_with_progress_and_cache(
    suite_root: &Path,
    pin_path: &Path,
    cache_root: &Path,
    progress: &mut dyn FnMut(ClassificationProgressEvent),
) -> Result<CombinedClassificationReport, String> {
    let cache = ClassifierCache::new(suite_root, pin_path, cache_root)?;
    let pin = cache.pin.clone();
    let actual_commit = cache.suite_commit.clone();
    let analysis_root = cache.analysis_root.clone();
    let mut paired_reports = Vec::with_capacity(pin.fixture_roots.len());
    for root in &pin.fixture_roots {
        let scalar = {
            let mut forward_progress = |event| {
                progress(event);
                Ok(())
            };
            classify_pinned_scalar_tree_with_progress_and_cache(
                &analysis_root,
                pin_path,
                root,
                &mut forward_progress,
                Some(&cache),
            )?
        };
        let heap = {
            let mut forward_progress = |event| {
                progress(event);
                Ok(())
            };
            classify_pinned_heap_tree_with_progress_and_cache(
                &analysis_root,
                pin_path,
                root,
                &mut forward_progress,
                Some(&cache),
            )?
        };
        let reference = {
            let mut forward_progress = |event| {
                progress(event);
                Ok(())
            };
            classify_pinned_reference_tree_with_progress_and_cache(
                &analysis_root,
                pin_path,
                root,
                &mut forward_progress,
                Some(&cache),
            )?
        };
        paired_reports.push((scalar, heap, reference));
    }
    combine_classification_reports(&actual_commit, &pin.fixture_roots, paired_reports)
}

/// Classify the three independent semantic lanes concurrently while retaining fixture order
/// inside each lane. Progress is delivered by the calling thread; only the interleaving between
/// lane-qualified event streams is schedule-dependent. Final report construction and error
/// selection retain the canonical scalar/heap/reference precedence.
pub fn classify_pinned_combined_suite_parallel_with_progress_and_cache(
    suite_root: &Path,
    pin_path: &Path,
    cache_root: &Path,
    progress: &mut dyn FnMut(ClassificationProgressEvent),
) -> Result<CombinedClassificationReport, String> {
    let cache = ClassifierCache::new(suite_root, pin_path, cache_root)?;
    let pin = cache.pin.clone();
    let actual_commit = cache.suite_commit.clone();
    let analysis_root = cache.analysis_root.clone();
    let roots = &pin.fixture_roots;
    let (progress_sender, progress_receiver) = sync_channel(ClassificationLane::ALL.len());

    let (scalar, heap, reference) = thread::scope(|scope| {
        let cache = &cache;
        let analysis_root = &analysis_root;
        let scalar_sender = progress_sender.clone();
        let scalar_worker = scope.spawn(move || {
            let mut reports = Vec::with_capacity(roots.len());
            let mut worker_progress = |event| {
                scalar_sender
                    .send(event)
                    .map_err(|_| "scalar classification progress receiver dropped".to_owned())
            };
            for root in roots {
                reports.push(classify_pinned_scalar_tree_with_progress_and_cache(
                    analysis_root,
                    pin_path,
                    root,
                    &mut worker_progress,
                    Some(cache),
                )?);
            }
            Ok::<_, String>(reports)
        });

        let heap_sender = progress_sender.clone();
        let heap_worker = scope.spawn(move || {
            let mut reports = Vec::with_capacity(roots.len());
            let mut worker_progress = |event| {
                heap_sender
                    .send(event)
                    .map_err(|_| "heap classification progress receiver dropped".to_owned())
            };
            for root in roots {
                reports.push(classify_pinned_heap_tree_with_progress_and_cache(
                    analysis_root,
                    pin_path,
                    root,
                    &mut worker_progress,
                    Some(cache),
                )?);
            }
            Ok::<_, String>(reports)
        });

        let reference_sender = progress_sender.clone();
        let reference_worker = scope.spawn(move || {
            let mut reports = Vec::with_capacity(roots.len());
            let mut worker_progress = |event| {
                reference_sender
                    .send(event)
                    .map_err(|_| "reference classification progress receiver dropped".to_owned())
            };
            for root in roots {
                reports.push(classify_pinned_reference_tree_with_progress_and_cache(
                    analysis_root,
                    pin_path,
                    root,
                    &mut worker_progress,
                    Some(cache),
                )?);
            }
            Ok::<_, String>(reports)
        });

        drop(progress_sender);
        for event in progress_receiver {
            progress(event);
        }

        (
            scalar_worker
                .join()
                .map_err(|_| "scalar classification worker panicked".to_owned())
                .and_then(|result| result),
            heap_worker
                .join()
                .map_err(|_| "heap classification worker panicked".to_owned())
                .and_then(|result| result),
            reference_worker
                .join()
                .map_err(|_| "reference classification worker panicked".to_owned())
                .and_then(|result| result),
        )
    });

    let (scalar, heap, reference) = select_parallel_lane_results(scalar, heap, reference)?;
    let mut paired_reports = Vec::with_capacity(roots.len());
    for ((scalar, heap), reference) in scalar.into_iter().zip(heap).zip(reference) {
        paired_reports.push((scalar, heap, reference));
    }
    combine_classification_reports(&actual_commit, roots, paired_reports)
}

fn select_parallel_lane_results<Scalar, Heap, Reference>(
    scalar: Result<Scalar, String>,
    heap: Result<Heap, String>,
    reference: Result<Reference, String>,
) -> Result<(Scalar, Heap, Reference), String> {
    let scalar = scalar?;
    let heap = heap?;
    let reference = reference?;
    Ok((scalar, heap, reference))
}

fn combine_classification_reports(
    suite_commit: &str,
    roots: &[String],
    paired_reports: Vec<(
        ScalarClassificationReport,
        HeapClassificationReport,
        ReferenceClassificationReport,
    )>,
) -> Result<CombinedClassificationReport, String> {
    if paired_reports.len() != roots.len() {
        return Err(format!(
            "combined classification received {} report groups for {} pinned roots",
            paired_reports.len(),
            roots.len()
        ));
    }
    let mut combined = CombinedClassificationReport {
        schema: "maledictus-nagini-combined-classification/v4".to_owned(),
        suite_commit: suite_commit.to_owned(),
        roots: roots.to_vec(),
        total: 0,
        matched: 0,
        semantic_matched: 0,
        production_typecheck_rejection_matched: 0,
        source_wellformedness_rejection_matched: 0,
        superseded_upstream_unsupported: 0,
        production_typecheck_divergent: 0,
        mismatched: 0,
        refused: 0,
        profile_ignored: 0,
        scalar_matched: 0,
        scalar_mismatched: 0,
        scalar_refused: 0,
        scalar_profile_ignored: 0,
        heap_matched: 0,
        heap_superseded_upstream_unsupported: 0,
        heap_mismatched: 0,
        heap_refused: 0,
        heap_profile_ignored: 0,
        reference_matched: 0,
        reference_mismatched: 0,
        reference_refused: 0,
        reference_profile_ignored: 0,
        fixtures: Vec::new(),
    };
    let mut seen = BTreeSet::new();
    for (root_index, (scalar, heap, reference)) in paired_reports.into_iter().enumerate() {
        validate_scalar_classification_counts(&scalar)?;
        let expected_root = roots[root_index].replace('\\', "/");
        if scalar.suite_commit != suite_commit
            || heap.suite_commit != suite_commit
            || reference.suite_commit != suite_commit
        {
            return Err(format!(
                "classification report for {expected_root:?} does not bind pinned commit {suite_commit}"
            ));
        }
        if scalar.root != expected_root
            || heap.root != expected_root
            || reference.root != expected_root
        {
            return Err(format!(
                "classification root mismatch: expected {expected_root:?}, scalar {:?}, heap {:?}, reference {:?}",
                scalar.root, heap.root, reference.root
            ));
        }
        let heap_by_fixture = heap
            .fixtures
            .into_iter()
            .map(|fixture| (fixture.fixture.clone(), fixture))
            .collect::<BTreeMap<_, _>>();
        if heap_by_fixture.len() != scalar.fixtures.len() {
            return Err(format!(
                "scalar/heap fixture count differs for {expected_root:?}: {} versus {}",
                scalar.fixtures.len(),
                heap_by_fixture.len()
            ));
        }
        let reference_by_fixture = reference
            .fixtures
            .into_iter()
            .map(|fixture| (fixture.fixture.clone(), fixture))
            .collect::<BTreeMap<_, _>>();
        if reference_by_fixture.len() != scalar.fixtures.len() {
            return Err(format!(
                "scalar/reference fixture count differs for {expected_root:?}: {} versus {}",
                scalar.fixtures.len(),
                reference_by_fixture.len()
            ));
        }
        combined.scalar_matched += scalar.matched;
        combined.scalar_mismatched += scalar.mismatched;
        combined.scalar_refused += scalar.refused;
        combined.scalar_profile_ignored += scalar.profile_ignored;
        combined.heap_matched += heap.matched;
        combined.heap_superseded_upstream_unsupported += heap.superseded_upstream_unsupported;
        combined.heap_mismatched += heap.mismatched;
        combined.heap_refused += heap.refused;
        combined.heap_profile_ignored += heap.profile_ignored;
        combined.reference_matched += reference.matched;
        combined.reference_mismatched += reference.mismatched;
        combined.reference_refused += reference.refused;
        combined.reference_profile_ignored += reference.profile_ignored;
        for scalar_fixture in scalar.fixtures {
            if !seen.insert(scalar_fixture.fixture.clone()) {
                return Err(format!(
                    "pinned fixture roots overlap at {:?}",
                    scalar_fixture.fixture
                ));
            }
            let heap_fixture = heap_by_fixture
                .get(&scalar_fixture.fixture)
                .ok_or_else(|| {
                    format!(
                        "heap classification omitted fixture {:?}",
                        scalar_fixture.fixture
                    )
                })?;
            let reference_fixture = reference_by_fixture
                .get(&scalar_fixture.fixture)
                .ok_or_else(|| {
                    format!(
                        "reference classification omitted fixture {:?}",
                        scalar_fixture.fixture
                    )
                })?;
            let ignored_lanes = [
                scalar_fixture.status.as_str(),
                heap_fixture.status.as_str(),
                reference_fixture.status.as_str(),
            ]
            .into_iter()
            .filter(|status| *status == "profile-ignored")
            .count();
            if ignored_lanes != 0 && ignored_lanes != 3 {
                return Err(format!(
                    "annotation-profile classification differs between analysis lanes for {:?}",
                    scalar_fixture.fixture
                ));
            }
            if ignored_lanes == 3
                && (scalar_fixture.annotation_profile != heap_fixture.annotation_profile
                    || scalar_fixture.annotation_profile != reference_fixture.annotation_profile)
            {
                return Err(format!(
                    "annotation-profile audit differs between analysis lanes for {:?}",
                    scalar_fixture.fixture
                ));
            }
            let status = if ignored_lanes == 3 {
                combined.profile_ignored += 1;
                "profile-ignored"
            } else if scalar_fixture.status == "production-typecheck-divergence" {
                combined.production_typecheck_divergent += 1;
                "production-typecheck-divergence"
            } else if scalar_fixture.status == "matched"
                || heap_fixture.status == "matched"
                || reference_fixture.status == "matched"
            {
                combined.matched += 1;
                "matched"
            } else if scalar_fixture.status == "superseded-upstream-unsupported"
                || heap_fixture.status == "superseded-upstream-unsupported"
                || reference_fixture.status == "superseded-upstream-unsupported"
            {
                combined.superseded_upstream_unsupported += 1;
                "superseded-upstream-unsupported"
            } else if scalar_fixture.status == "mismatched"
                || heap_fixture.status == "mismatched"
                || reference_fixture.status == "mismatched"
            {
                combined.mismatched += 1;
                "mismatched"
            } else {
                combined.refused += 1;
                "refused"
            };
            let match_kind = if scalar_fixture.status == "matched"
                && scalar_fixture.match_kind
                    == Some(ConformanceMatchKind::ProductionTypecheckRejection)
            {
                combined.production_typecheck_rejection_matched += 1;
                Some(ConformanceMatchKind::ProductionTypecheckRejection)
            } else if scalar_fixture.status == "matched"
                && scalar_fixture.match_kind
                    == Some(ConformanceMatchKind::SourceWellformednessRejection)
            {
                combined.source_wellformedness_rejection_matched += 1;
                Some(ConformanceMatchKind::SourceWellformednessRejection)
            } else if status == "matched" {
                combined.semantic_matched += 1;
                Some(ConformanceMatchKind::SemanticVerification)
            } else if status == "superseded-upstream-unsupported" {
                Some(ConformanceMatchKind::SupersededUpstreamUnsupported)
            } else if status == "profile-ignored" {
                Some(ConformanceMatchKind::ProfileIgnored)
            } else {
                None
            };
            let superseded_heap = status == "superseded-upstream-unsupported"
                && heap_fixture.status == "superseded-upstream-unsupported";
            combined.fixtures.push(CombinedFixtureClassification {
                fixture: scalar_fixture.fixture,
                status: status.to_owned(),
                expected: if superseded_heap {
                    heap_fixture.expected.clone()
                } else {
                    scalar_fixture.expected
                },
                actual: if superseded_heap {
                    heap_fixture.actual.clone()
                } else {
                    scalar_fixture.actual
                },
                match_kind,
                python_typechecker: if superseded_heap {
                    heap_fixture.python_typechecker.clone()
                } else {
                    scalar_fixture.python_typechecker
                },
                python_typecheck_diagnostics: if superseded_heap {
                    heap_fixture.python_typecheck_diagnostics.clone()
                } else {
                    scalar_fixture.python_typecheck_diagnostics
                },
                scalar_status: scalar_fixture.status,
                scalar_detail: scalar_fixture.detail,
                heap_status: heap_fixture.status.clone(),
                heap_detail: heap_fixture.detail.clone(),
                reference_status: reference_fixture.status.clone(),
                reference_detail: reference_fixture.detail.clone(),
                annotation_profile: scalar_fixture.annotation_profile,
            });
        }
    }
    combined
        .fixtures
        .sort_by(|left, right| left.fixture.cmp(&right.fixture));
    combined.total = u64::try_from(combined.fixtures.len())
        .map_err(|_| "combined fixture count exceeds u64".to_owned())?;
    if combined.matched
        + combined.superseded_upstream_unsupported
        + combined.mismatched
        + combined.refused
        + combined.profile_ignored
        + combined.production_typecheck_divergent
        != combined.total
    {
        return Err("combined classification counts do not cover every fixture".to_owned());
    }
    Ok(combined)
}

pub fn check_scalar_source(source: &str, fixture: &str) -> Result<ScalarConformanceResult, String> {
    check_scalar_source_internal(source, fixture, None, false)
}

#[cfg(test)]
fn check_scalar_source_selected(
    source: &str,
    fixture: &str,
    selected_symbols: &BTreeSet<String>,
) -> Result<ScalarConformanceResult, String> {
    check_scalar_source_internal(source, fixture, Some(selected_symbols), false)
}

fn check_scalar_source_internal(
    source: &str,
    fixture: &str,
    selected_symbols: Option<&BTreeSet<String>>,
    annotation_profile_selected: bool,
) -> Result<ScalarConformanceResult, String> {
    if !annotation_profile_selected && has_ignore_file_annotation(source)? {
        return Err(
            "version-conditioned IgnoreFile annotations require an explicitly selected Nagini backend profile"
                .to_owned(),
        );
    }
    let mut expected = parse_expected_diagnostics(source)?;
    if expected
        .iter()
        .any(|diagnostic| is_typecheck_expectation(&diagnostic.code))
    {
        return Err(
            "type-error conformance requires the source-bound pinned production Python typechecker"
                .to_owned(),
        );
    }
    let verification = verify_contract_module_for_conformance(source, fixture, selected_symbols)
        .map_err(|error| format!("{}: {}", error.code, error.message))?;
    let mut actual: Vec<ExpectedDiagnostic> = verification
        .obligations
        .iter()
        .filter(|obligation| !obligation.satisfied())
        .map(|obligation| {
            let code = if obligation.expectation == ObligationExpectation::Refute {
                "refute.failed:refutation.true".to_owned()
            } else if obligation.id.contains(":purity-violation:") {
                "invalid.program:purity.violated".to_owned()
            } else if obligation.id.contains(":undefined-local:") {
                "expression.undefined:undefined.local.variable".to_owned()
            } else if obligation.id.contains(":invariant-establishment:") {
                "invariant.not.established:assertion.false".to_owned()
            } else if obligation.id.contains(":invariant-preservation:") {
                "invariant.not.preserved:assertion.false".to_owned()
            } else if obligation.id.contains(":call-permission-precondition:") {
                "call.precondition:insufficient.permission".to_owned()
            } else if obligation.id.contains(":call-precondition:") {
                "call.precondition:assertion.false".to_owned()
            } else if obligation.id.contains(":application-precondition:")
                || obligation.id.contains(":exception-undeclared:IndexError:")
            {
                "application.precondition:assertion.false".to_owned()
            } else if obligation.id.contains(":field-write-permission:")
                || obligation.id.contains(":assignment-read-permission:")
            {
                "assignment.failed:insufficient.permission".to_owned()
            } else if obligation.id.contains(":exception-undeclared:") {
                "exhale.failed:assertion.false".to_owned()
            } else if obligation.id.contains(":postcondition:")
                || obligation.id.contains(":function-totality:runtime-path:")
            {
                "postcondition.violated:assertion.false".to_owned()
            } else if obligation.id.contains(":function-totality:")
                || obligation.id.contains(":pure-assert:")
            {
                "function.not.wellformed:assertion.false".to_owned()
            } else {
                "assert.failed:assertion.false".to_owned()
            };
            ExpectedDiagnostic {
                code,
                line: obligation.line,
            }
        })
        .collect();
    expected.sort();
    expected.dedup();
    actual.sort();
    actual.dedup();
    Ok(ScalarConformanceResult {
        schema: "maledictus-nagini-scalar-conformance/v2".to_owned(),
        fixture: fixture.to_owned(),
        passed: expected == actual,
        expected,
        actual,
        analysis_kind: ConformanceMatchKind::SemanticVerification,
        python_typechecker: None,
        python_typecheck_diagnostics: Vec::new(),
        annotation_profile: None,
    })
}

fn selected_symbols_from_fixture(relative: &Path) -> Option<BTreeSet<String>> {
    if !relative
        .components()
        .any(|part| part.as_os_str() == "select")
    {
        return None;
    }
    let stem = relative.file_stem()?.to_string_lossy();
    Some(
        stem.split('-')
            .filter(|name| !name.is_empty())
            .map(str::to_owned)
            .collect(),
    )
}

pub fn check_heap_source(source: &str, fixture: &str) -> Result<HeapConformanceResult, String> {
    check_heap_source_internal(
        source,
        fixture,
        None,
        &[],
        InformationFlowVerificationProfile::Ordinary,
    )
}

#[cfg(test)]
fn check_heap_source_selection(
    source: &str,
    fixture: &str,
    selected_symbols: &BTreeSet<String>,
) -> Result<HeapConformanceResult, String> {
    check_heap_source_internal(
        source,
        fixture,
        Some(selected_symbols),
        &[],
        InformationFlowVerificationProfile::Ordinary,
    )
}

fn check_pinned_heap_source_graph(
    suite_root: &Path,
    fixture_path: &Path,
    source: &str,
    fixture: &str,
    selected_symbols: Option<&BTreeSet<String>>,
    information_flow: InformationFlowVerificationProfile,
) -> Result<HeapConformanceResult, String> {
    let expected = parse_expected_diagnostics(source)?;
    if let Err(failure) =
        validate_contract_positions_with_profile(source, fixture, information_flow)
    {
        let checked =
            check_pinned_source_wellformedness_rejection(suite_root, fixture, &expected, failure)?;
        return Ok(HeapConformanceResult {
            schema: "maledictus-nagini-heap-conformance/v2".to_owned(),
            fixture: fixture.to_owned(),
            expected: checked.expected,
            actual: checked.actual,
            passed: checked.passed,
            semantic_verified: false,
            analysis_kind: ConformanceMatchKind::SourceWellformednessRejection,
            python_typechecker: checked.python_typechecker,
            python_typecheck_diagnostics: checked.python_typecheck_diagnostics,
            annotation_profile: None,
        });
    }
    let mut resolver = PinnedHeapSourceResolver::new(suite_root)?;
    let fixture_path = resolver
        .checked_source_path(fixture_path)
        .map_err(|error| format!("{}: {}", error.code, error.message))?;
    let fixture_module = resolver
        .source_module_context(&fixture_path)
        .map_err(|error| format!("{}: {}", error.code, error.message))?;
    let level_intrinsics = resolve_level_intrinsic_bindings_for_source(
        &mut resolver,
        &fixture_path,
        source,
        fixture,
        fixture_module.as_deref(),
    )
    .map_err(|error| format!("{}: {}", error.code, error.message))?;
    let obligation_verification =
        verify_obligation_module_with_intrinsics(source, fixture, &level_intrinsics)
            .map_err(|error| format!("{}: {}", error.code, error.message))?;
    let termination_verification = verify_sif_termination_module(source, fixture, information_flow)
        .map_err(|error| format!("{}: {}", error.code, error.message))?;
    let mut specialized_verifications = [obligation_verification, termination_verification]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    if !specialized_verifications.is_empty()
        && !source_activates_ordinary_heap_semantics(source, fixture)
            .map_err(|error| format!("{}: {}", error.code, error.message))?
    {
        return project_heap_verification(
            source,
            fixture,
            merge_heap_verifications(fixture, specialized_verifications),
        );
    }
    let mut base_verification = None;
    if has_pinned_io_imports(source, fixture)
        .map_err(|error| format!("{}: {}", error.code, error.message))?
    {
        let provider_root = suite_root.join("src").join("nagini_contracts");
        let contracts_path = resolver
            .checked_source_path(&provider_root.join("io_contracts.py"))
            .map_err(|error| format!("{}: {}", error.code, error.message))?;
        let builtins_path = resolver
            .checked_source_path(&provider_root.join("io_builtins.py"))
            .map_err(|error| format!("{}: {}", error.code, error.message))?;
        let contracts_source = fs::read_to_string(&contracts_path).map_err(|error| {
            format!(
                "cannot read pinned IO provider {}: {error}",
                contracts_path.display()
            )
        })?;
        let builtins_source = fs::read_to_string(&builtins_path).map_err(|error| {
            format!(
                "cannot read pinned IO provider {}: {error}",
                builtins_path.display()
            )
        })?;
        let requested_symbols = selected_symbols
            .map(|selected| selected.iter().cloned().collect::<Vec<_>>())
            .unwrap_or_default();
        base_verification = verify_pinned_io_module(
            source,
            fixture,
            &contracts_source,
            &builtins_source,
            &requested_symbols,
        )
        .map_err(|error| format!("{}: {}", error.code, error.message))?;
    }
    let base_verification = if let Some(verification) = base_verification {
        verification
    } else {
        let imports = resolver
            .resolve_imports_for_source(&fixture_path, source, fixture, fixture_module.as_deref())
            .map_err(|error| format!("{}: {}", error.code, error.message))?;
        verify_heap_module_for_conformance_with_profile(
            source,
            fixture,
            &imports,
            selected_symbols,
            information_flow,
        )
        .map_err(|error| format!("{}: {}", error.code, error.message))?
    };
    prune_specialized_failures_after_absorbing_base_statements(
        source,
        &base_verification,
        &mut specialized_verifications,
    )?;
    specialized_verifications.insert(0, base_verification);
    let verification = merge_heap_verifications(fixture, specialized_verifications);
    let mut result = project_heap_verification(source, fixture, verification)?;
    if semantic_result_can_supersede_upstream_unsupported(
        &result.expected,
        &result.actual,
        result.semantic_verified,
    ) {
        let source_root = fixture_path.parent().ok_or_else(|| {
            format!(
                "pinned superseded-unsupported fixture has no source parent: {}",
                fixture_path.display()
            )
        })?;
        let checked_path = fixture_path
            .file_name()
            .ok_or_else(|| {
                format!(
                    "pinned superseded-unsupported fixture has no file name: {}",
                    fixture_path.display()
                )
            })?
            .to_string_lossy()
            .into_owned();
        let checked = typecheck_request_sources(
            source_root,
            &[SourceFile {
                path: checked_path,
                language: "python".to_owned(),
                symbols: Vec::new(),
            }],
            &[],
        )
        .map_err(|failure| format!("{}: {}", failure.code, failure.message))?
        .ok_or_else(|| {
            "superseded upstream unsupported classification requires strict Python typechecking"
                .to_owned()
        })?;
        validate_conformance_typechecker_identity(&checked.identity)?;
        if checked.passed() {
            result.analysis_kind = ConformanceMatchKind::SupersededUpstreamUnsupported;
            result.python_typechecker = Some(checked.identity);
            result.python_typecheck_diagnostics = checked.diagnostics;
        }
    }
    Ok(result)
}

fn prune_specialized_failures_after_absorbing_base_statements(
    source: &str,
    base: &HeapContractVerification,
    specialized: &mut [HeapContractVerification],
) -> Result<(), String> {
    let suite = ast::Suite::parse(source, &base.path)
        .map_err(|error| format!("frontend.python.parse-error: {error}"))?;
    let mut adjacent_statements = BTreeSet::new();
    collect_adjacent_statement_lines(source, &suite, &mut adjacent_statements);
    let absorbing_lines = base
        .obligations
        .iter()
        .filter(|obligation| {
            !obligation.satisfied()
                && (obligation.id.contains(":field-write-permission:")
                    || obligation.id.contains(":assignment-read-permission:"))
        })
        .map(|obligation| obligation.line)
        .collect::<BTreeSet<_>>();
    for verification in specialized {
        verification.obligations.retain(|obligation| {
            obligation.satisfied()
                || !obligation.id.contains(":obligation-release-precondition:")
                || !absorbing_lines
                    .iter()
                    .any(|line| adjacent_statements.contains(&(*line, obligation.line)))
        });
        verification.passed = verification
            .obligations
            .iter()
            .all(|obligation| obligation.satisfied());
    }
    Ok(())
}

fn collect_adjacent_statement_lines(
    source: &str,
    statements: &[ast::Stmt],
    adjacent: &mut BTreeSet<(u32, u32)>,
) {
    for pair in statements.windows(2) {
        adjacent.insert((
            source_line(source, pair[0].range().start().into()),
            source_line(source, pair[1].range().start().into()),
        ));
    }
    for statement in statements {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                collect_adjacent_statement_lines(source, &function.body, adjacent);
            }
            ast::Stmt::AsyncFunctionDef(function) => {
                collect_adjacent_statement_lines(source, &function.body, adjacent);
            }
            ast::Stmt::ClassDef(class) => {
                collect_adjacent_statement_lines(source, &class.body, adjacent);
            }
            ast::Stmt::If(branch) => {
                collect_adjacent_statement_lines(source, &branch.body, adjacent);
                collect_adjacent_statement_lines(source, &branch.orelse, adjacent);
            }
            ast::Stmt::For(loop_) => {
                collect_adjacent_statement_lines(source, &loop_.body, adjacent);
                collect_adjacent_statement_lines(source, &loop_.orelse, adjacent);
            }
            ast::Stmt::AsyncFor(loop_) => {
                collect_adjacent_statement_lines(source, &loop_.body, adjacent);
                collect_adjacent_statement_lines(source, &loop_.orelse, adjacent);
            }
            ast::Stmt::While(loop_) => {
                collect_adjacent_statement_lines(source, &loop_.body, adjacent);
                collect_adjacent_statement_lines(source, &loop_.orelse, adjacent);
            }
            ast::Stmt::With(with_) => {
                collect_adjacent_statement_lines(source, &with_.body, adjacent);
            }
            ast::Stmt::AsyncWith(with_) => {
                collect_adjacent_statement_lines(source, &with_.body, adjacent);
            }
            ast::Stmt::Try(try_) => {
                collect_adjacent_statement_lines(source, &try_.body, adjacent);
                collect_adjacent_statement_lines(source, &try_.orelse, adjacent);
                collect_adjacent_statement_lines(source, &try_.finalbody, adjacent);
                for handler in &try_.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    collect_adjacent_statement_lines(source, &handler.body, adjacent);
                }
            }
            ast::Stmt::TryStar(try_) => {
                collect_adjacent_statement_lines(source, &try_.body, adjacent);
                collect_adjacent_statement_lines(source, &try_.orelse, adjacent);
                collect_adjacent_statement_lines(source, &try_.finalbody, adjacent);
                for handler in &try_.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    collect_adjacent_statement_lines(source, &handler.body, adjacent);
                }
            }
            ast::Stmt::Match(match_) => {
                for case in &match_.cases {
                    collect_adjacent_statement_lines(source, &case.body, adjacent);
                }
            }
            _ => {}
        }
    }
}

fn source_line(source: &str, byte_offset: u32) -> u32 {
    source.as_bytes()[..byte_offset as usize]
        .iter()
        .filter(|byte| **byte == b'\n')
        .count() as u32
        + 1
}

fn resolve_level_intrinsic_bindings_for_source(
    resolver: &mut PinnedHeapSourceResolver,
    importer_path: &Path,
    source: &str,
    display_path: &str,
    importer_module: Option<&str>,
) -> Result<ResolvedLevelIntrinsicBindings, ContractFailure> {
    let requests = source_contract_import_requests(source, display_path)?;
    let mut descriptors = BTreeMap::new();
    let mut certified = None::<CertifiedLevelIntrinsics>;
    for request in requests.iter().filter(|request| {
        request.relative_level == 0 && request.module == CANONICAL_OBLIGATIONS_MODULE
    }) {
        let imported = resolver.resolve_import(importer_path, importer_module, request)?;
        let Some(imported_certificate) = imported.certified_level_intrinsics() else {
            continue;
        };
        if certified
            .as_ref()
            .is_some_and(|current| current != imported_certificate)
        {
            return Err(ContractFailure {
                code: "frontend.python.verifier-intrinsic.level-certificate-conflict",
                message: "source imports incompatible certified level intrinsic providers"
                    .to_owned(),
            });
        }
        certified.get_or_insert_with(|| imported_certificate.clone());
        for (imported_name, alias) in &request.imported_names {
            if imported_name == "*" {
                descriptors.extend(
                    imported
                        .verifier_intrinsics()
                        .iter()
                        .map(|(name, descriptor)| (name.clone(), descriptor.clone())),
                );
                continue;
            }
            if let Some(descriptor) = imported.verifier_intrinsics().get(imported_name) {
                descriptors.insert(
                    alias.clone().unwrap_or_else(|| imported_name.clone()),
                    descriptor.clone(),
                );
            }
        }
    }
    Ok(
        certified.map_or_else(ResolvedLevelIntrinsicBindings::default, |certified| {
            ResolvedLevelIntrinsicBindings::from_resolver_descriptors(&certified, &descriptors)
        }),
    )
}

fn merge_heap_verifications(
    fixture: &str,
    verifications: impl IntoIterator<Item = HeapContractVerification>,
) -> HeapContractVerification {
    let mut methods = Vec::new();
    let mut obligations = Vec::new();
    for verification in verifications {
        methods.extend(verification.methods);
        obligations.extend(verification.obligations);
    }
    methods.sort();
    methods.dedup();
    obligations.sort_by(|left, right| {
        (
            left.path.as_str(),
            left.line,
            left.column,
            left.byte_offset,
            left.id.as_str(),
        )
            .cmp(&(
                right.path.as_str(),
                right.line,
                right.column,
                right.byte_offset,
                right.id.as_str(),
            ))
    });
    obligations.dedup();
    let passed = obligations.iter().all(|obligation| obligation.satisfied());
    HeapContractVerification {
        schema: "maledictus-python-heap-composition/v1".to_owned(),
        path: fixture.to_owned(),
        methods,
        obligations,
        passed,
    }
}

fn semantic_result_can_supersede_upstream_unsupported(
    expected: &[ExpectedDiagnostic],
    actual: &[ExpectedDiagnostic],
    semantic_verified: bool,
) -> bool {
    semantic_verified
        && !expected.is_empty()
        && expected
            .iter()
            .all(|diagnostic| diagnostic.code.starts_with("unsupported:"))
        && actual.is_empty()
}

fn check_heap_source_internal(
    source: &str,
    fixture: &str,
    selected_symbols: Option<&BTreeSet<String>>,
    imported_modules: &[ImportedHeapContractModule],
    information_flow: InformationFlowVerificationProfile,
) -> Result<HeapConformanceResult, String> {
    let verification = verify_heap_module_for_conformance_with_profile(
        source,
        fixture,
        imported_modules,
        selected_symbols,
        information_flow,
    )
    .map_err(|error| format!("{}: {}", error.code, error.message))?;
    project_heap_verification(source, fixture, verification)
}

fn project_heap_verification(
    source: &str,
    fixture: &str,
    verification: HeapContractVerification,
) -> Result<HeapConformanceResult, String> {
    let mut expected = parse_expected_diagnostics(source)?;
    let mut actual: Vec<ExpectedDiagnostic> = verification
        .obligations
        .iter()
        .filter(|obligation| !obligation.satisfied())
        .map(|obligation| ExpectedDiagnostic {
            code: if obligation.expectation == ObligationExpectation::Refute {
                "refute.failed:refutation.true".to_owned()
            } else if obligation.id.contains(":obligation-leak:caller:") {
                "leak_check.failed:caller.has_unsatisfied_obligations".to_owned()
            } else if obligation.id.contains(":obligation-leak:method-body:") {
                "leak_check.failed:method_body.leaks_obligations".to_owned()
            } else if obligation.id.contains(":obligation-leak:loop-context:") {
                "leak_check.failed:loop_context.has_unsatisfied_obligations".to_owned()
            } else if obligation.id.contains(":obligation-leak:loop-body:") {
                "leak_check.failed:loop_body.leaks_obligations".to_owned()
            } else if obligation
                .id
                .contains(":obligation-invariant-preservation-permission:")
            {
                "invariant.not.preserved:insufficient.permission".to_owned()
            } else if obligation
                .id
                .contains(":obligation-postcondition-permission:")
            {
                "postcondition.violated:insufficient.permission".to_owned()
            } else if obligation
                .id
                .contains(":sif-termination-condition-not-low:")
            {
                "termination_channel_check.failed:sif_termination.condition_not_low".to_owned()
            } else if obligation.id.contains(":sif-termination-not-lowevent:") {
                "termination_channel_check.failed:sif_termination.not_lowevent".to_owned()
            } else if obligation
                .id
                .contains(":sif-termination-condition-not-tight:")
            {
                "termination_channel_check.failed:sif_termination.condition_not_tight".to_owned()
            } else if obligation.id.contains(":sif-loop-promise-not-kept:") {
                "leak_check.failed:must_terminate.loop_promise_not_kept".to_owned()
            } else if obligation
                .id
                .contains(":sif-call-termination-condition-not-low:")
            {
                "call.precondition:sif_termination.condition_not_low".to_owned()
            } else if obligation
                .id
                .contains(":sif-termination-caller-unsatisfied:")
            {
                "leak_check.failed:caller.has_unsatisfied_obligations".to_owned()
            } else if obligation.id.contains(":obligation-release-precondition:") {
                "call.precondition:insufficient.permission".to_owned()
            } else if obligation.id.contains(":dataclass-untyped-field") {
                "unsupported:field() requires a type annotation".to_owned()
            } else if obligation.id.contains(":dataclass-init-option") {
                "unsupported:keyword unsupported".to_owned()
            } else if obligation.id.contains(":purity-violation:") {
                "invalid.program:purity.violated".to_owned()
            } else if obligation.id.contains(":undefined-global:") {
                "expression.undefined:undefined.global.name".to_owned()
            } else if obligation.id.contains(":undefined-local:") {
                "expression.undefined:undefined.local.variable".to_owned()
            } else if obligation
                .id
                .contains(":predicate-unfold-permission-not-positive:")
            {
                "unfold.failed:permission.not.positive".to_owned()
            } else if obligation.id.contains(":predicate-fold-body:") {
                "fold.failed:assertion.false".to_owned()
            } else if obligation.id.contains(":predicate-unfolding-permission:") {
                "assignment.failed:insufficient.permission".to_owned()
            } else if obligation.id.contains("@property:")
                && obligation.id.contains(":field-permission:")
            {
                "function.not.wellformed:insufficient.permission".to_owned()
            } else if obligation.id.contains(":property-precondition:") {
                "application.precondition:insufficient.permission".to_owned()
            } else if obligation.id.contains(":property-setter-precondition:") {
                "call.precondition:insufficient.permission".to_owned()
            } else if obligation.id.contains(":field-write-permission:")
                || obligation.id.contains(":assignment-read-permission:")
            {
                "assignment.failed:insufficient.permission".to_owned()
            } else if obligation.id.contains(":field-permission:") {
                "assert.failed:insufficient.permission".to_owned()
            } else if obligation
                .id
                .contains(":precondition-not-strengthened:permission")
            {
                "call.precondition:insufficient.permission".to_owned()
            } else if obligation
                .id
                .contains(":postcondition-not-weakened:permission")
                || obligation
                    .id
                    .contains(":constructor-initialization-permission:")
            {
                "postcondition.violated:insufficient.permission".to_owned()
            } else if obligation
                .id
                .contains(":postcondition-not-weakened:exception:")
            {
                "postcondition.violated:assertion.false".to_owned()
            } else if obligation.id.contains(":invariant-establishment:") {
                "invariant.not.established:assertion.false".to_owned()
            } else if obligation.id.contains(":invariant-preservation:") {
                "invariant.not.preserved:assertion.false".to_owned()
            } else if obligation.id.contains(":exception-undeclared:") {
                "exhale.failed:assertion.false".to_owned()
            } else if obligation.id.contains(":call-permission-precondition:") {
                "call.precondition:insufficient.permission".to_owned()
            } else if obligation.id.contains(":call-precondition:")
                || obligation.id.contains(":precondition-not-strengthened")
            {
                "call.precondition:assertion.false".to_owned()
            } else if obligation.id.contains(":application-precondition:") {
                "application.precondition:assertion.false".to_owned()
            } else if obligation.id.contains(":method-call-precondition:")
                || obligation
                    .id
                    .contains(":constructor-permission-precondition:")
                || obligation
                    .id
                    .contains(":base-constructor-permission-precondition:")
            {
                "call.precondition:insufficient.permission".to_owned()
            } else if obligation.id.contains(":constructor-precondition:")
                || obligation.id.contains(":base-constructor-precondition:")
            {
                "call.precondition:assertion.false".to_owned()
            } else if obligation.id.contains(":function-totality:")
                || obligation.id.contains(":pure-assert:")
            {
                "function.not.wellformed:assertion.false".to_owned()
            } else if obligation.id.contains(":exception-postcondition:")
                || obligation.id.contains(":postcondition:")
                || obligation.id.contains(":postcondition-not-weakened")
            {
                "postcondition.violated:assertion.false".to_owned()
            } else {
                "assert.failed:assertion.false".to_owned()
            },
            line: if obligation.id.contains(":obligation-leak:")
                || obligation
                    .id
                    .contains(":sif-termination-caller-unsatisfied:")
            {
                obligation.line.saturating_sub(1)
            } else {
                obligation.line
            },
        })
        .collect();
    expected.sort();
    expected.dedup();
    actual.sort();
    actual.dedup();
    Ok(HeapConformanceResult {
        schema: "maledictus-nagini-heap-conformance/v2".to_owned(),
        fixture: fixture.to_owned(),
        passed: expected == actual,
        semantic_verified: verification.passed,
        analysis_kind: ConformanceMatchKind::SemanticVerification,
        python_typechecker: None,
        python_typecheck_diagnostics: Vec::new(),
        annotation_profile: None,
        expected,
        actual,
    })
}

pub fn check_reference_source(
    source: &str,
    fixture: &str,
) -> Result<ReferenceConformanceResult, String> {
    let mut expected = parse_expected_diagnostics(source)?;
    let verification = verify_reference_module(source, fixture, &[])
        .map_err(|error| format!("{}: {}", error.code, error.message))?;
    let mut actual: Vec<ExpectedDiagnostic> = verification
        .obligations
        .iter()
        .filter(|obligation| !obligation.satisfied())
        .map(|obligation| ExpectedDiagnostic {
            code: if obligation.id.contains(":call-precondition:") {
                "call.precondition:assertion.false".to_owned()
            } else {
                "assert.failed:assertion.false".to_owned()
            },
            line: obligation.line,
        })
        .collect();
    expected.sort();
    actual.sort();
    Ok(ReferenceConformanceResult {
        schema: "maledictus-nagini-reference-conformance/v1".to_owned(),
        fixture: fixture.to_owned(),
        passed: expected == actual,
        expected,
        actual,
        annotation_profile: None,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ExpectedOutputAnnotationComment {
    contents: String,
    line: u32,
    start: u32,
}

fn expected_output_annotation_comments(
    source: &str,
) -> Result<Vec<ExpectedOutputAnnotationComment>, String> {
    let mut comments = Vec::new();
    for token in lex(source, Mode::Module) {
        let (token, range) = token.map_err(|error| {
            format!("cannot lex Python source while locating expected diagnostics: {error:?}")
        })?;
        let Tok::Comment(comment) = token else {
            continue;
        };
        let Some(comment_body) = comment.strip_prefix('#') else {
            continue;
        };
        let comment_body = comment_body.trim_start();
        let Some(contents) = comment_body.strip_prefix("::") else {
            // A second comment marker means the apparent annotation belongs to commented-out
            // Python source, not to this comment token itself (for example `#  #:: ...`).
            continue;
        };
        if contents.find("ExpectedOutput(").is_none() {
            continue;
        }
        let start = u32::from(range.start());
        let byte_offset = usize::try_from(start)
            .unwrap_or(source.len())
            .min(source.len());
        let line = u32::try_from(
            source[..byte_offset]
                .bytes()
                .filter(|byte| *byte == b'\n')
                .count()
                + 1,
        )
        .unwrap_or(u32::MAX);
        comments.push(ExpectedOutputAnnotationComment {
            contents: contents.to_owned(),
            line,
            start,
        });
    }
    Ok(comments)
}

pub(crate) fn source_range_has_expected_output_annotation(
    source: &str,
    start: u32,
    end: u32,
) -> Result<bool, String> {
    Ok(expected_output_annotation_comments(source)?
        .iter()
        .any(|comment| comment.start >= start && comment.start < end))
}

fn parse_expected_diagnostics(source: &str) -> Result<Vec<ExpectedDiagnostic>, String> {
    fn closing_parenthesis(contents: &str) -> Option<usize> {
        let mut nested = 0_usize;
        for (index, character) in contents.char_indices() {
            match character {
                '(' => nested += 1,
                ')' if nested == 0 => return Some(index),
                ')' => nested -= 1,
                _ => {}
            }
        }
        None
    }

    let supported = [
        "assert.failed:assertion.false",
        "assert.failed:insufficient.permission",
        "function.not.wellformed:assertion.false",
        "function.not.wellformed:insufficient.permission",
        "invariant.not.established:assertion.false",
        "invariant.not.preserved:assertion.false",
        "invariant.not.preserved:insufficient.permission",
        "call.precondition:assertion.false",
        "call.precondition:insufficient.permission",
        "leak_check.failed:caller.has_unsatisfied_obligations",
        "leak_check.failed:method_body.leaks_obligations",
        "leak_check.failed:loop_context.has_unsatisfied_obligations",
        "leak_check.failed:loop_body.leaks_obligations",
        "application.precondition:insufficient.permission",
        "application.precondition:assertion.false",
        "assignment.failed:insufficient.permission",
        "fold.failed:assertion.false",
        "unfold.failed:permission.not.positive",
        "termination_channel_check.failed:sif_termination.condition_not_low",
        "termination_channel_check.failed:sif_termination.not_lowevent",
        "termination_channel_check.failed:sif_termination.condition_not_tight",
        "leak_check.failed:must_terminate.loop_promise_not_kept",
        "call.precondition:sif_termination.condition_not_low",
        "postcondition.violated:assertion.false",
        "postcondition.violated:insufficient.permission",
        "refute.failed:refutation.true",
        "expression.undefined:undefined.global.name",
        "expression.undefined:undefined.local.variable",
        "exhale.failed:assertion.false",
        "invalid.program:invalid.contract.position",
        "invalid.program:invalid.contract.call",
        "invalid.program:invalid.result",
        "invalid.program:invalid.result.type",
        "invalid.program:incorrect.declared.type",
        "invalid.program:invalid.predicate",
        "invalid.program:nested.class.declaration",
        "invalid.program:nested.function.declaration",
        "invalid.program:decorators.incompatible",
        "invalid.program:overriding.inline.method",
        "invalid.program:invalid.override",
        "invalid.program:abstract.predicate.fold",
        "invalid.program:partially.abstract.predicate.family",
        "invalid.program:contract.in.inline.method",
        "invalid.program:local.import",
        "invalid.program:local.type.alias",
        "invalid.program:function.type.none",
        "invalid.program:function.throws.exception",
        "invalid.program:function.return.missing",
        "invalid.program:function.dead.code",
        RECURSIVE_STATIC_CALL,
        PRIVATE_FIELD_ACCESS,
        "invalid.program:purity.violated",
        "invalid.program:malformed.adt",
        "invalid.program:invalid.io_operation.return_type_not_bool",
        "invalid.program:invalid.io_operation.vararg",
        "invalid.program:invalid.io_operation.kwarg",
        "invalid.program:invalid.io_operation.default_argument",
        "invalid.program:invalid.io_operation.invalid_preset",
        "invalid.program:invalid.io_operation.invalid_postset",
        "invalid.program:invalid.io_operation.misplaced_property",
        "invalid.program:invalid.io_operation.duplicate_property",
        "invalid.program:invalid.io_operation.depends_on_not_imput",
        "invalid.program:invalid.ioexists.misplaced",
        EXISTENTIAL_USE_UNDEFINED,
        EXISTENTIAL_DEFINITION_TYPE_MISMATCH,
        OPERATION_UNDEFINED_EXISTENTIAL,
        OPERATION_RESULT_NOT_VARIABLE,
        OPERATION_RESULT_NOT_EXISTENTIAL,
        "invalid.program:invalid.float.val",
        "invalid.program:invalid.get_ghost_output.multiple_targets",
        "invalid.program:invalid.get_ghost_output.target_not_variable",
        "invalid.program:invalid.get_ghost_output.result_identifier_not_str",
        "invalid.program:invalid.get_ghost_output.argument_not_io_operation",
        "invalid.program:invalid.get_ghost_output.invalid_result_identifier",
        "invalid.program:invalid.get_ghost_output.type_mismatch",
        "type.error:dead.code",
        "unsupported:Inlining constructors is currently not supported.",
        "unsupported:Multi-target assignments are not supported in pure functions.",
        "unsupported:Subclassing builtin type is currently not supported.",
        "unsupported:field() requires a type annotation",
        "unsupported:keyword unsupported",
        "unsupported:sequence patterns not yet supported",
        "unsupported:Multiple generators in list comprehension.",
        "unsupported:Multiple generators in dict comprehension.",
        "unsupported:Multiple generators in set comprehension.",
        "invalid.program:continue.in.finally",
        "unsupported:mapping patterns not yet supported",
        "unsupported:positional class patterns not yet supported",
        "unsupported:class patterns with parameters not yet supported",
        "unsupported:assignment to slice",
        "unsupported:with block may only have one item",
        "unsupported:multiple inheritance",
        "unsupported:Unsupported metaclass",
        "unsupported:Tuples longer than 9 elements are currently unsupported. Please file an issue to resolve this.",
        "invalid.program:illegal.magic.method",
        "invalid.program:wildcard.variable.read",
        "unsupported:float() is currently only supported with arguments NaN and inf.",
        "invalid.program:partial.type",
        "invalid.program:generic.constructor.without.type",
        "invalid.program:impure.list.comprehension.body",
        "invalid.program:impure.disjunction",
        "invalid.program:invalid.let",
        "invalid.program:invalid.previous",
        "invalid.program:invalid.reveal.no.function",
        "invalid.program:invalid.reveal.no.pure.function",
        "invalid.program:invalid.reveal.no.opaque.function",
        "invalid.program:invalid.may.create",
        "invalid.program:invalid.may.set",
        "invalid.program:invalid.acc",
        "invalid.program:permission.to.final.var",
        "invalid.program:invalid.thread.creation",
        "invalid.program:invalid.thread.start",
        "invalid.program:invalid.thread.join",
        "invalid.program:invalid.get.method.use",
        "invalid.program:invalid.arg.use",
        CONCURRENCY_IN_SIF,
    ];
    let mut diagnostics = Vec::new();
    for comment in expected_output_annotation_comments(source)? {
        let mut rest = comment.contents.as_str();
        while let Some(start) = rest.find("ExpectedOutput(") {
            let after = &rest[start + "ExpectedOutput(".len()..];
            let end = closing_parenthesis(after).ok_or_else(|| {
                format!(
                    "unterminated ExpectedOutput annotation on line {}",
                    comment.line
                )
            })?;
            let annotation = after[..end].trim();
            let code = if annotation.starts_with("type.error:") {
                annotation
            } else {
                annotation.split(',').next().unwrap_or("").trim()
            };
            if matches!(code, "carbon" | "silicon") {
                let backend_diagnostic = after[end + 1..].trim_start();
                let Some(backend_diagnostic) = backend_diagnostic.strip_prefix('(') else {
                    return Err(format!(
                        "backend-qualified ExpectedOutput annotation on line {} has no diagnostic group",
                        comment.line
                    ));
                };
                let diagnostic_end = backend_diagnostic.find(')').ok_or_else(|| {
                    format!(
                        "unterminated backend-qualified ExpectedOutput annotation on line {}",
                        comment.line
                    )
                })?;
                if backend_diagnostic[..diagnostic_end].trim().is_empty() {
                    return Err(format!(
                        "backend-qualified ExpectedOutput annotation on line {} has an empty diagnostic group",
                        comment.line
                    ));
                }
                rest = &backend_diagnostic[diagnostic_end + 1..];
                continue;
            }
            if !supported.contains(&code)
                && !is_typecheck_expectation(code)
                && !code.starts_with("unsupported:")
            {
                return Err(format!(
                    "scalar conformance does not implement expected diagnostic {code:?} on line {}",
                    comment.line
                ));
            }
            diagnostics.push(ExpectedDiagnostic {
                code: code.to_owned(),
                line: if is_obligation_diagnostic(code) {
                    comment.line
                } else {
                    comment.line.saturating_add(1)
                },
            });
            rest = &after[end + 1..];
        }
    }
    Ok(diagnostics)
}

fn is_obligation_diagnostic(code: &str) -> bool {
    matches!(
        code,
        "leak_check.failed:caller.has_unsatisfied_obligations"
            | "leak_check.failed:method_body.leaks_obligations"
            | "leak_check.failed:loop_context.has_unsatisfied_obligations"
            | "leak_check.failed:loop_body.leaks_obligations"
    )
}

fn git_commit(root: &Path) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["rev-parse", "HEAD"])
        .output()
        .map_err(|error| format!("cannot run git for {}: {error}", root.display()))?;
    if !output.status.success() {
        return Err(format!(
            "cannot identify suite commit at {}: {}",
            root.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn collect_python_files(root: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = fs::read_dir(root)
        .map_err(|error| format!("cannot enumerate {}: {error}", root.display()))?;
    for entry in entries {
        let entry = entry.map_err(|error| format!("cannot read directory entry: {error}"))?;
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
        if file_type.is_symlink() {
            return Err(format!(
                "conformance suite symlink is refused: {}",
                path.display()
            ));
        }
        if file_type.is_dir() {
            collect_python_files(&path, files)?;
        } else if path.extension().is_some_and(|extension| extension == "py") {
            files.push(path);
        }
    }
    Ok(())
}

/// Mirror Nagini's `_test_files` entrypoint discovery rather than treating support modules as
/// standalone fixtures.
fn collect_nagini_test_files(root: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    let manifest = root.join("tests");
    if manifest.is_file() {
        let source = fs::read_to_string(&manifest)
            .map_err(|error| format!("cannot read test list {}: {error}", manifest.display()))?;
        for line in source
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
        {
            let path = root.join(line);
            if !path.is_file() {
                return Err(format!(
                    "Nagini test list {} names missing file {line:?}",
                    manifest.display()
                ));
            }
            files.push(path);
        }
        return Ok(());
    }

    let entries = fs::read_dir(root)
        .map_err(|error| format!("cannot enumerate {}: {error}", root.display()))?;
    for entry in entries {
        let entry = entry.map_err(|error| format!("cannot read directory entry: {error}"))?;
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
        if file_type.is_symlink() {
            return Err(format!(
                "conformance suite symlink is refused: {}",
                path.display()
            ));
        }
        if file_type.is_dir() {
            if entry.file_name() != "resources" {
                collect_nagini_test_files(&path, files)?;
            }
        } else if path.extension().is_some_and(|extension| extension == "py")
            && path.file_name().is_some_and(|name| name != "__init__.py")
        {
            files.push(path);
        }
    }
    Ok(())
}

fn scan_annotations(path: &Path, counts: &mut AnnotationCounts) -> Result<(), String> {
    let source = fs::read_to_string(path)
        .map_err(|error| format!("cannot read fixture {}: {error}", path.display()))?;
    counts.expected_outputs += source.matches("ExpectedOutput").count() as u64;
    counts.unexpected_outputs += source.matches("UnexpectedOutput").count() as u64;
    counts.missing_outputs += source.matches("MissingOutput").count() as u64;
    if source.contains("IgnoreFile(") {
        counts.ignored_files += 1;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vc::{ObligationResult, ObligationStatus};

    fn failed_obligation(id: &str, line: u32) -> ObligationResult {
        ObligationResult {
            id: id.to_owned(),
            expectation: ObligationExpectation::Prove,
            status: ObligationStatus::Refuted,
            counterexample: Some("behavioral counterexample".to_owned()),
            path: "mixed.py".to_owned(),
            byte_offset: line,
            line,
            column: 1,
        }
    }

    #[test]
    fn heap_composition_preserves_ordinary_and_specialized_failures_once() {
        let ordinary_failure = failed_obligation("mixed:field-write-permission:2", 2);
        let specialized_failure = failed_obligation("mixed:obligation-leak:method-body:5", 5);
        let same_line_distinct_failure = failed_obligation("mixed:assert:2", 2);
        let ordinary = HeapContractVerification {
            schema: "ordinary".to_owned(),
            path: "mixed.py".to_owned(),
            methods: vec!["ordinary".to_owned()],
            obligations: vec![ordinary_failure.clone(), same_line_distinct_failure],
            passed: false,
        };
        let specialized = HeapContractVerification {
            schema: "specialized".to_owned(),
            path: "mixed.py".to_owned(),
            methods: vec!["specialized".to_owned()],
            obligations: vec![ordinary_failure, specialized_failure],
            passed: false,
        };

        let merged = merge_heap_verifications("mixed.py", [ordinary, specialized]);

        assert!(!merged.passed);
        assert_eq!(merged.methods, ["ordinary", "specialized"]);
        assert_eq!(merged.obligations.len(), 3);
        assert_eq!(
            merged
                .obligations
                .iter()
                .filter(|obligation| obligation.id.contains("field-write-permission"))
                .count(),
            1,
            "the same semantic failure contributed by two analyzers must be projected once"
        );
        assert!(
            merged
                .obligations
                .iter()
                .any(|obligation| obligation.id.contains("obligation-leak"))
        );
        assert_eq!(
            merged
                .obligations
                .iter()
                .filter(|obligation| obligation.line == 2)
                .count(),
            2,
            "distinct failures at one source location must remain distinct"
        );
    }

    #[test]
    fn composition_prunes_only_release_checks_after_an_adjacent_absorbing_heap_failure() {
        let source = "def direct(box: object, lock: object) -> None:\n    box.value = 1\n    lock.release()\n\ndef branches(box: object, lock: object, flag: bool) -> None:\n    if flag:\n        box.value = 1\n    else:\n        lock.release()\n";
        let base = HeapContractVerification {
            schema: "ordinary".to_owned(),
            path: "mixed.py".to_owned(),
            methods: Vec::new(),
            obligations: vec![
                failed_obligation("direct:field-write-permission:value", 2),
                failed_obligation("branches:field-write-permission:value", 7),
            ],
            passed: false,
        };
        let mut specialized = [HeapContractVerification {
            schema: "specialized".to_owned(),
            path: "mixed.py".to_owned(),
            methods: Vec::new(),
            obligations: vec![
                failed_obligation("direct:obligation-release-precondition:lock", 3),
                failed_obligation("branches:obligation-release-precondition:lock", 9),
            ],
            passed: false,
        }];

        prune_specialized_failures_after_absorbing_base_statements(source, &base, &mut specialized)
            .unwrap();

        assert_eq!(specialized[0].obligations.len(), 1);
        assert!(specialized[0].obligations[0].id.starts_with("branches:"));
    }

    fn typechecker_identity() -> PythonTypecheckerIdentity {
        PythonTypecheckerIdentity {
            checker: "mypy".to_owned(),
            checker_version: MYPY_VERSION.to_owned(),
            profile: PYTHON_TYPECHECK_PROFILE.to_owned(),
            package_sha256: "1".repeat(64),
            runtime: "python".to_owned(),
            runtime_version: "3.12.10".to_owned(),
            runtime_executable_sha256: "2".repeat(64),
            runtime_bundle_sha256: "3".repeat(64),
            configuration_sha256: "4".repeat(64),
            contract_support_sha256: Some("5".repeat(64)),
        }
    }

    fn type_error(message: &str, code: &str, line: u32) -> Diagnostic {
        Diagnostic {
            severity: "error".to_owned(),
            code: format!("frontend.python.typecheck.{code}"),
            message: message.to_owned(),
            path: Some("fixture.py".to_owned()),
            line: Some(line),
            column: Some(5),
        }
    }

    fn expected_type_error(message: &str, code: &str, line: u32) -> ExpectedDiagnostic {
        ExpectedDiagnostic {
            code: format!("type.error:{message}  [{code}]"),
            line,
        }
    }

    #[test]
    fn parallel_lane_error_precedence_is_scalar_then_heap_then_reference() {
        assert_eq!(
            select_parallel_lane_results::<(), (), ()>(
                Err("scalar".to_owned()),
                Err("heap".to_owned()),
                Err("reference".to_owned()),
            ),
            Err("scalar".to_owned())
        );
        assert_eq!(
            select_parallel_lane_results::<(), (), ()>(
                Ok(()),
                Err("heap".to_owned()),
                Err("reference".to_owned()),
            ),
            Err("heap".to_owned())
        );
        assert_eq!(
            select_parallel_lane_results::<(), (), ()>(Ok(()), Ok(()), Err("reference".to_owned()),),
            Err("reference".to_owned())
        );
    }

    #[test]
    fn local_import_precedence_is_limited_to_nonempty_same_line_misc_consequences() {
        let failure = ContractPositionFailure {
            code: LOCAL_IMPORT,
            message: "function-local imports are unsupported".to_owned(),
            byte_offset: 10,
            line: 4,
            column: 5,
        };
        assert!(only_same_line_local_import_typecheck_consequences(
            &failure,
            &[type_error("import dependency omitted", "misc", 4)]
        ));
        assert!(!only_same_line_local_import_typecheck_consequences(
            &failure,
            &[]
        ));
        assert!(!only_same_line_local_import_typecheck_consequences(
            &failure,
            &[type_error("independent type error", "assignment", 4)]
        ));
        assert!(!only_same_line_local_import_typecheck_consequences(
            &failure,
            &[type_error("independent later error", "misc", 7)]
        ));

        let other_failure = ContractPositionFailure {
            code: "invalid.program:local.type.alias",
            ..failure
        };
        assert!(!only_same_line_local_import_typecheck_consequences(
            &other_failure,
            &[type_error(
                "same shape, different source failure",
                "misc",
                4
            )]
        ));
    }

    #[test]
    fn rejected_expression_precedence_never_hides_other_lines_or_source_failures() {
        let failure = ContractPositionFailure {
            code: INVALID_CONTRACT_POSITION,
            message: "contract expression is invalid at this position".to_owned(),
            byte_offset: 20,
            line: 8,
            column: 9,
        };
        assert!(only_same_line_rejected_expression_typecheck_consequences(
            &failure,
            &[type_error("nested invalid expression", "union-attr", 8)]
        ));
        assert!(!only_same_line_rejected_expression_typecheck_consequences(
            &failure,
            &[]
        ));
        assert!(!only_same_line_rejected_expression_typecheck_consequences(
            &failure,
            &[
                type_error("nested invalid expression", "union-attr", 8),
                type_error("independent later error", "assignment", 11),
            ]
        ));

        let other_failure = ContractPositionFailure {
            code: "invalid.program:invalid.contract.call",
            ..failure
        };
        assert!(!only_same_line_rejected_expression_typecheck_consequences(
            &other_failure,
            &[type_error(
                "same line, different source failure",
                "union-attr",
                8
            )]
        ));
    }

    #[test]
    fn private_field_precedence_accepts_only_nonempty_unused_ignore_diagnostics() {
        let failure = ContractPositionFailure {
            code: PRIVATE_FIELD_ACCESS,
            message: "private field access is outside its declaring class".to_owned(),
            byte_offset: 20,
            line: 8,
            column: 9,
        };
        let unused_ignore = type_error("unused verifier-only ignore", "unused-ignore", 4);
        assert!(only_private_field_unused_ignore_consequences(
            &failure,
            std::slice::from_ref(&unused_ignore)
        ));
        assert!(!only_private_field_unused_ignore_consequences(
            &failure,
            &[]
        ));
        assert!(!only_private_field_unused_ignore_consequences(
            &failure,
            &[
                unused_ignore,
                type_error("independent assignment error", "assignment", 11),
            ]
        ));

        let other_failure = ContractPositionFailure {
            code: INVALID_CONTRACT_POSITION,
            ..failure
        };
        assert!(!only_private_field_unused_ignore_consequences(
            &other_failure,
            &[type_error(
                "unused verifier-only ignore",
                "unused-ignore",
                4
            )]
        ));
    }

    #[test]
    fn superseded_unsupported_requires_only_unsupported_expectations_and_real_semantic_success() {
        let unsupported = ExpectedDiagnostic {
            code: "unsupported:old frontend gap".to_owned(),
            line: 4,
        };
        let semantic_failure = ExpectedDiagnostic {
            code: "assert.failed:assertion.false".to_owned(),
            line: 7,
        };
        assert!(semantic_result_can_supersede_upstream_unsupported(
            std::slice::from_ref(&unsupported),
            &[],
            true,
        ));
        assert!(!semantic_result_can_supersede_upstream_unsupported(
            &[],
            &[],
            true,
        ));
        assert!(!semantic_result_can_supersede_upstream_unsupported(
            std::slice::from_ref(&semantic_failure),
            &[],
            true,
        ));
        assert!(!semantic_result_can_supersede_upstream_unsupported(
            std::slice::from_ref(&unsupported),
            std::slice::from_ref(&semantic_failure),
            true,
        ));
        assert!(!semantic_result_can_supersede_upstream_unsupported(
            &[unsupported],
            &[],
            false,
        ));
    }

    #[test]
    fn arbitrary_upstream_unsupported_diagnostics_can_be_parsed_for_semantic_supersession() {
        let diagnostics = parse_expected_diagnostics(
            "#:: ExpectedOutput(unsupported:future upstream frontend limitation)\npass\n",
        )
        .expect("an upstream unsupported label is evidence to compare, not a local capability");

        assert_eq!(
            diagnostics,
            vec![ExpectedDiagnostic {
                code: "unsupported:future upstream frontend limitation".to_owned(),
                line: 2,
            }]
        );
        assert!(semantic_result_can_supersede_upstream_unsupported(
            &diagnostics,
            &[],
            true,
        ));
        assert!(!semantic_result_can_supersede_upstream_unsupported(
            &diagnostics,
            &[],
            false,
        ));
    }

    #[test]
    fn production_typecheck_rejection_retains_exact_identity_and_location() {
        let identity = typechecker_identity();
        let diagnostic = type_error("Incompatible return value type", "return-value", 4);
        let result = typecheck_rejection_result(
            "fixture.py",
            "fixture.py",
            &[expected_type_error(
                "Incompatible return value type",
                "return-value",
                4,
            )],
            PythonTypecheckVerification {
                identity: identity.clone(),
                diagnostics: vec![diagnostic.clone()],
            },
        )
        .unwrap();
        assert!(result.passed);
        assert_eq!(
            result.analysis_kind,
            ConformanceMatchKind::ProductionTypecheckRejection
        );
        assert_eq!(result.python_typechecker, Some(identity));
        assert_eq!(result.python_typecheck_diagnostics, vec![diagnostic]);
    }

    #[test]
    fn production_typecheck_rejection_requires_exact_diagnostic_multiset() {
        let expected = [expected_type_error(
            "Incompatible return value type",
            "return-value",
            4,
        )];
        let result = |diagnostics| {
            typecheck_rejection_result(
                "fixture.py",
                "fixture.py",
                &expected,
                PythonTypecheckVerification {
                    identity: typechecker_identity(),
                    diagnostics,
                },
            )
            .unwrap()
        };
        assert!(!result(Vec::new()).passed, "missing errors must mismatch");
        assert!(
            !result(vec![
                type_error("Incompatible return value type", "return-value", 4),
                type_error("Extra error", "misc", 5),
            ])
            .passed,
            "extra errors must mismatch"
        );
        assert!(
            !result(vec![type_error(
                "Incompatible return value type",
                "return-value",
                5,
            )])
            .passed,
            "wrong lines must mismatch"
        );
        assert!(
            !result(vec![type_error(
                "Incompatible return value type",
                "assignment",
                4,
            )])
            .passed,
            "wrong codes must mismatch"
        );
    }

    #[test]
    fn production_typecheck_rejection_refuses_wrong_identity_or_tool_failure() {
        let expected = [expected_type_error("error", "misc", 1)];
        let mut identity = typechecker_identity();
        identity.checker_version = "2.3.0".to_owned();
        let wrong_identity = typecheck_rejection_result(
            "fixture.py",
            "fixture.py",
            &expected,
            PythonTypecheckVerification {
                identity,
                diagnostics: vec![type_error("error", "misc", 1)],
            },
        )
        .unwrap_err();
        assert!(wrong_identity.contains("not the pinned conformance checker"));

        let tool_failure = finish_typecheck_rejection(
            "fixture.py",
            "fixture.py",
            &expected,
            Err(PythonTypecheckFailure {
                code: "frontend.python.typecheck.protocol",
                message: "checker output was malformed".to_owned(),
            }),
        )
        .unwrap_err();
        assert!(tool_failure.contains("frontend.python.typecheck.protocol"));
        assert!(tool_failure.contains("checker output was malformed"));
    }

    #[test]
    fn typecheck_divergence_metadata_serializes_and_counts_separately() {
        let expected = vec![expected_type_error("expected", "assignment", 2)];
        let actual = vec![expected_type_error("actual", "arg-type", 3)];
        let identity = typechecker_identity();
        let report = ScalarClassificationReport {
            schema: "maledictus-nagini-scalar-classification/v2".to_owned(),
            suite_commit: "commit".to_owned(),
            root: "tests".to_owned(),
            matched: 0,
            semantic_matched: 0,
            production_typecheck_rejection_matched: 0,
            source_wellformedness_rejection_matched: 0,
            production_typecheck_divergent: 1,
            mismatched: 0,
            refused: 0,
            profile_ignored: 0,
            fixtures: vec![ScalarFixtureClassification {
                fixture: "fixture.py".to_owned(),
                status: "production-typecheck-divergence".to_owned(),
                detail: "production diagnostics differ".to_owned(),
                expected: expected.clone(),
                actual: actual.clone(),
                match_kind: None,
                python_typechecker: Some(identity.clone()),
                python_typecheck_diagnostics: vec![type_error("actual", "arg-type", 3)],
                annotation_profile: None,
            }],
        };
        validate_scalar_classification_counts(&report).unwrap();
        let encoded = serde_json::to_value(&report).unwrap();
        assert_eq!(encoded["matched"], 0);
        assert_eq!(encoded["production_typecheck_divergent"], 1);
        assert_eq!(
            encoded["fixtures"][0]["expected"],
            serde_json::json!(expected)
        );
        assert_eq!(encoded["fixtures"][0]["actual"], serde_json::json!(actual));
        assert_eq!(
            encoded["fixtures"][0]["python_typechecker"],
            serde_json::json!(identity)
        );

        let mut invalid = report;
        invalid.matched = 1;
        assert!(validate_scalar_classification_counts(&invalid).is_err());
    }

    #[test]
    fn type_error_expectations_require_source_bound_checker_and_preserve_commas() {
        let source = "#:: ExpectedOutput(type.error:Argument 1 has incompatible type \"int\", expected \"str\"  [arg-type])\nvalue = 1\n";
        assert_eq!(
            parse_expected_diagnostics(source).unwrap(),
            vec![expected_type_error(
                "Argument 1 has incompatible type \"int\", expected \"str\"",
                "arg-type",
                2,
            )]
        );
        let error = check_scalar_source(source, "fixture.py").unwrap_err();
        assert!(error.contains("source-bound pinned production Python typechecker"));
    }

    #[test]
    fn scans_nagini_annotations_without_treating_missing_as_expected() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join("fixture.py");
        fs::write(
            &fixture,
            "#:: ExpectedOutput(assert.failed)\n#:: UnexpectedOutput(assert.failed, 1)\n#:: MissingOutput(assert.failed, 2)\n#:: IgnoreFile(3)\n",
        )
        .unwrap();
        let mut counts = AnnotationCounts::default();
        scan_annotations(&fixture, &mut counts).unwrap();
        assert_eq!(
            counts,
            AnnotationCounts {
                expected_outputs: 1,
                unexpected_outputs: 1,
                missing_outputs: 1,
                ignored_files: 1,
            }
        );
    }

    #[test]
    fn pinned_resolver_leaves_canonical_builtin_imports_to_heap_semantics() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join("fixture.py");
        fs::write(&fixture, "from enum import IntEnum\n").unwrap();
        let mut resolver = PinnedHeapSourceResolver::new(directory.path()).unwrap();
        for source in [
            "from enum import IntEnum\n",
            "from nagini_contracts.adt import ADT\n",
        ] {
            let imports = resolver
                .resolve_imports_for_source(&fixture, source, "fixture.py", None)
                .unwrap();
            assert!(imports.is_empty());
        }

        for source in [
            "from enum import IntEnum as E\n",
            "from enum import *\n",
            "from enum import Enum\n",
            "from nagini_contracts.adt import ADT as Algebraic\n",
            "from nagini_contracts.adt import *\n",
            "from nagini_contracts.adt import Other\n",
        ] {
            let error = resolver
                .resolve_imports_for_source(&fixture, source, "fixture.py", None)
                .unwrap_err();
            assert_eq!(error.code, "frontend.python.heap.unbound-module");
        }
    }

    #[test]
    fn pinned_resolver_supports_repository_src_import_layout() {
        let directory = tempfile::tempdir().unwrap();
        let fixture_directory = directory.path().join("tests").join("functional");
        let provider_directory = directory.path().join("src").join("library");
        fs::create_dir_all(&fixture_directory).unwrap();
        fs::create_dir_all(&provider_directory).unwrap();
        let fixture = fixture_directory.join("fixture.py");
        let provider = provider_directory.join("support.py");
        fs::write(&fixture, "from library.support import value\n").unwrap();
        fs::write(&provider, "value = 1\n").unwrap();

        let resolver = PinnedHeapSourceResolver::new(directory.path()).unwrap();
        let located = resolver.locate_module(&fixture, "library.support").unwrap();

        assert_eq!(located.path, fs::canonicalize(provider).unwrap());
        assert_eq!(
            located.import_root,
            fs::canonicalize(directory.path().join("src")).unwrap()
        );
    }

    #[test]
    fn pinned_resolver_selects_only_canonical_obligations_intrinsic_provider() {
        let directory = tempfile::tempdir().unwrap();
        let fixture_directory = directory.path().join("tests").join("functional");
        let provider_directory = directory.path().join("src").join("nagini_contracts");
        fs::create_dir_all(&fixture_directory).unwrap();
        fs::create_dir_all(&provider_directory).unwrap();
        let fixture = fixture_directory.join("fixture.py");
        let consumer =
            "from nagini_contracts.obligations import Level as Rank, WaitLevel as Ambient\n";
        fs::write(&fixture, consumer).unwrap();
        fs::write(
            provider_directory.join("obligations.py"),
            include_str!("../.upstream/nagini/src/nagini_contracts/obligations.py"),
        )
        .unwrap();

        let mut resolver = PinnedHeapSourceResolver::new(directory.path()).unwrap();
        let imported = resolver
            .resolve_module(&fixture, "nagini_contracts.obligations")
            .expect("the exact canonical path and ABI select verifier-intrinsic origin");
        assert_eq!(
            imported
                .verifier_intrinsics()
                .keys()
                .cloned()
                .collect::<Vec<_>>(),
            vec!["Level", "MustRelease", "MustTerminate", "WaitLevel"]
        );
        assert_eq!(
            imported
                .verifier_intrinsic_classes()
                .keys()
                .cloned()
                .collect::<Vec<_>>(),
            vec!["BaseLock", "LevelType"]
        );
        assert!(imported.certified_level_intrinsics().is_some());
        assert!(imported.class_names().is_empty());

        let bindings = resolve_level_intrinsic_bindings_for_source(
            &mut resolver,
            &fixture,
            consumer,
            "tests/functional/fixture.py",
            None,
        )
        .expect("consumer aliases are resolved from the certified descriptor catalog");
        assert_eq!(
            bindings.event("Rank").map(|event| event.kind()),
            Some(crate::python_obligation_levels::LevelIntrinsicEventKind::Level)
        );
        assert_eq!(
            bindings.event("Ambient").map(|event| event.kind()),
            Some(crate::python_obligation_levels::LevelIntrinsicEventKind::WaitLevel)
        );
        assert!(bindings.event("Level").is_none());
        assert!(bindings.event("WaitLevel").is_none());
    }

    #[test]
    fn resolver_certified_level_bindings_support_exact_star_exports_only() {
        let directory = tempfile::tempdir().unwrap();
        let provider_directory = directory.path().join("src").join("nagini_contracts");
        fs::create_dir_all(&provider_directory).unwrap();
        let fixture = directory.path().join("fixture.py");
        let consumer = "from nagini_contracts.obligations import *\n";
        fs::write(&fixture, consumer).unwrap();
        fs::write(
            provider_directory.join("obligations.py"),
            include_str!("../.upstream/nagini/src/nagini_contracts/obligations.py"),
        )
        .unwrap();

        let mut resolver = PinnedHeapSourceResolver::new(directory.path()).unwrap();
        let bindings = resolve_level_intrinsic_bindings_for_source(
            &mut resolver,
            &fixture,
            consumer,
            "fixture.py",
            None,
        )
        .expect("the canonical __all__ supplies certified star bindings");
        assert_eq!(
            bindings.event("Level").map(|event| event.kind()),
            Some(crate::python_obligation_levels::LevelIntrinsicEventKind::Level)
        );
        assert_eq!(
            bindings.event("WaitLevel").map(|event| event.kind()),
            Some(crate::python_obligation_levels::LevelIntrinsicEventKind::WaitLevel)
        );
        for spelling in ["Rank", "Ambient", "BaseLock", "LevelType"] {
            assert!(bindings.event(spelling).is_none());
        }
    }

    #[test]
    fn pinned_resolver_does_not_promote_nearer_shadow_obligations_module() {
        let directory = tempfile::tempdir().unwrap();
        let fixture_directory = directory.path().join("tests").join("functional");
        let shadow_directory = fixture_directory.join("nagini_contracts");
        let canonical_directory = directory.path().join("src").join("nagini_contracts");
        fs::create_dir_all(&shadow_directory).unwrap();
        fs::create_dir_all(&canonical_directory).unwrap();
        let fixture = fixture_directory.join("fixture.py");
        fs::write(
            &fixture,
            "from nagini_contracts.obligations import LevelType\n",
        )
        .unwrap();
        let provider = include_str!("../.upstream/nagini/src/nagini_contracts/obligations.py");
        fs::write(
            shadow_directory.join("obligations.py"),
            "class LevelType:\n    def __lt__(self, other: 'LevelType') -> bool:\n        \"\"\"Application declaration with no executable return.\"\"\"\n",
        )
        .unwrap();
        fs::write(canonical_directory.join("obligations.py"), provider).unwrap();

        let mut resolver = PinnedHeapSourceResolver::new(directory.path()).unwrap();
        let failure = resolver
            .resolve_module(&fixture, "nagini_contracts.obligations")
            .expect_err("a nearer same-named application module remains ordinary source");
        assert_eq!(failure.code, "frontend.python.heap.return-value-missing");
    }

    #[test]
    fn pinned_resolver_rejects_canonical_obligations_abi_drift() {
        let directory = tempfile::tempdir().unwrap();
        let fixture_directory = directory.path().join("tests");
        let provider_directory = directory.path().join("src").join("nagini_contracts");
        fs::create_dir_all(&fixture_directory).unwrap();
        fs::create_dir_all(&provider_directory).unwrap();
        let fixture = fixture_directory.join("fixture.py");
        fs::write(
            &fixture,
            "from nagini_contracts.obligations import MustTerminate\n",
        )
        .unwrap();
        let drifted = include_str!("../.upstream/nagini/src/nagini_contracts/obligations.py")
            .replace(
                "def MustTerminate(measure: int) -> bool:",
                "def MustTerminate(measure: object) -> bool:",
            );
        fs::write(provider_directory.join("obligations.py"), drifted).unwrap();

        let mut resolver = PinnedHeapSourceResolver::new(directory.path()).unwrap();
        let failure = resolver
            .resolve_module(&fixture, "nagini_contracts.obligations")
            .expect_err("canonical path alone cannot authorize a changed verifier ABI");
        assert_eq!(
            failure.code,
            "frontend.python.verifier-intrinsic.obligations-signature-drift"
        );
    }

    #[test]
    fn pinned_resolver_prefers_nearest_fixture_provider_over_src_layout() {
        let directory = tempfile::tempdir().unwrap();
        let fixture_directory = directory.path().join("tests").join("functional");
        let local_provider_directory = fixture_directory.join("library");
        let src_provider_directory = directory.path().join("src").join("library");
        fs::create_dir_all(&local_provider_directory).unwrap();
        fs::create_dir_all(&src_provider_directory).unwrap();
        let fixture = fixture_directory.join("fixture.py");
        let local_provider = local_provider_directory.join("support.py");
        fs::write(&fixture, "from library.support import value\n").unwrap();
        fs::write(&local_provider, "value = 1\n").unwrap();
        fs::write(src_provider_directory.join("support.py"), "value = 2\n").unwrap();

        let resolver = PinnedHeapSourceResolver::new(directory.path()).unwrap();
        let located = resolver.locate_module(&fixture, "library.support").unwrap();

        assert_eq!(located.path, fs::canonicalize(local_provider).unwrap());
        assert_eq!(
            located.import_root,
            fs::canonicalize(&fixture_directory).unwrap()
        );
    }

    #[test]
    fn pinned_resolver_refuses_ambiguous_src_layout_provider() {
        let directory = tempfile::tempdir().unwrap();
        let fixture_directory = directory.path().join("tests");
        let source_root = directory.path().join("src");
        fs::create_dir_all(&fixture_directory).unwrap();
        fs::create_dir_all(source_root.join("library")).unwrap();
        let fixture = fixture_directory.join("fixture.py");
        fs::write(&fixture, "from library import value\n").unwrap();
        fs::write(source_root.join("library.py"), "value = 1\n").unwrap();
        fs::write(
            source_root.join("library").join("__init__.py"),
            "value = 2\n",
        )
        .unwrap();

        let resolver = PinnedHeapSourceResolver::new(directory.path()).unwrap();
        let failure = resolver.locate_module(&fixture, "library").unwrap_err();

        assert_eq!(failure.code, "frontend.python.heap.import-module-ambiguous");
    }

    #[test]
    fn scalar_conformance_matches_expected_refutation_line() {
        let result = check_scalar_source(
            "from nagini_contracts.contracts import *\n\n@Pure\ndef wrong() -> int:\n    #:: ExpectedOutput(postcondition.violated:assertion.false)\n    Ensures(Result() == 2)\n    return 1\n",
            "wrong.py",
        )
        .unwrap();
        assert!(result.passed);
        assert_eq!(result.actual[0].line, 6);
    }

    #[test]
    fn backend_qualified_expected_outputs_do_not_become_backend_neutral_claims() {
        let diagnostics = parse_expected_diagnostics(
            "#:: ExpectedOutput(carbon)(postcondition.violated:assertion.false)\n#:: ExpectedOutput(expression.undefined:undefined.local.variable)\nvalue = missing\n",
        )
        .unwrap();
        assert_eq!(
            diagnostics,
            vec![ExpectedDiagnostic {
                code: "expression.undefined:undefined.local.variable".to_owned(),
                line: 3,
            }]
        );

        let error = parse_expected_diagnostics("#:: ExpectedOutput(carbon)\n").unwrap_err();
        assert!(error.contains("has no diagnostic group"));
    }

    #[test]
    fn scalar_conformance_matches_source_call_precondition_line() {
        let result = check_scalar_source(
            "from nagini_contracts.contracts import *\n\ndef positive(value: int) -> None:\n    Requires(value > 0)\n\ndef client() -> None:\n    positive(1)\n    #:: ExpectedOutput(call.precondition:assertion.false)\n    positive(0)\n",
            "calls.py",
        )
        .unwrap();
        assert!(result.passed);
        assert_eq!(result.actual[0].line, 9);
    }

    #[test]
    fn scalar_conformance_ignores_only_literal_module_print_effects() {
        let source = "def value() -> int:\n    return abs(-2)\n\nprint('fixture output')\n";
        let result = check_scalar_source(source, "literal_print.py").unwrap();
        assert!(result.passed);

        let dynamic = "def value() -> int:\n    return 2\n\nmessage = 'output'\nprint(message)\n";
        let error = check_scalar_source(dynamic, "dynamic_print.py").unwrap_err();
        assert!(error.contains("module-statement-unsupported"));
    }

    #[test]
    fn heap_conformance_matches_constructor_and_chained_method_fixture() {
        let source = "from nagini_contracts.contracts import *\n\nclass A:\n    def __init__(self, a: int) -> None:\n        Ensures(Acc(self.a))  # type: ignore\n        Ensures(self.a == a)  # type: ignore\n        self.a = a\n\n    def m1(self, x: int) -> int:\n        Ensures(Result() == x)\n        return x\n\ndef main() -> None:\n    c = A(2).m1(5)\n";
        let result = check_heap_source(source, "issues/00071.py").unwrap();
        assert!(result.passed);
        assert!(result.expected.is_empty());
        assert!(result.actual.is_empty());
    }

    #[test]
    fn heap_conformance_maps_path_sensitive_undefined_local_at_the_read_site() {
        let source = "from nagini_contracts.contracts import *\n\nclass Marker:\n    value: int\n\ndef double(a: int) -> int:\n    if a > 0:\n        u = 14\n    #:: ExpectedOutput(expression.undefined:undefined.local.variable)\n    uu = u\n    return a\n";
        let result = check_heap_source(source, "undefined_local.py").unwrap();
        assert!(result.passed, "{result:#?}");
        assert!(result.actual.iter().any(|diagnostic| {
            diagnostic.code == "expression.undefined:undefined.local.variable"
                && diagnostic.line == 10
        }));
    }

    #[test]
    fn heap_conformance_maps_exception_postcondition_refutations() {
        let source = "from nagini_contracts.contracts import *\n\nclass Failure(Exception):\n    pass\n\ndef fail(error: Failure) -> None:\n    #:: ExpectedOutput(postcondition.violated:assertion.false)\n    Exsures(Failure, False)\n    raise error\n";
        let result = check_heap_source(source, "exception_postcondition.py").unwrap();
        assert!(result.passed, "{result:#?}");
        assert_eq!(result.actual, result.expected);
        assert_eq!(result.actual.len(), 1);
        assert_eq!(
            result.actual[0].code,
            "postcondition.violated:assertion.false"
        );
        assert_eq!(result.actual[0].line, 8);
    }

    #[test]
    fn heap_conformance_matches_pure_missing_return_fixture() {
        let source =
            include_str!("../.upstream/nagini/tests/functional/verification/issues/00229.py");
        let result =
            check_heap_source(source, "tests/functional/verification/issues/00229.py").unwrap();

        assert!(result.passed, "{result:#?}");
        assert_eq!(result.expected, result.actual);
        assert_eq!(
            result
                .actual
                .iter()
                .map(|diagnostic| (diagnostic.code.as_str(), diagnostic.line))
                .collect::<Vec<_>>(),
            vec![
                ("function.not.wellformed:assertion.false", 12),
                ("function.not.wellformed:assertion.false", 25),
            ]
        );
    }

    #[test]
    fn heap_conformance_selection_reports_only_the_selected_override() {
        let source = "from nagini_contracts.contracts import *\n\nclass SuperB:\n    #:: Label(L1)\n    def some_method(self, value: int) -> int:\n        Requires(value > 9)\n        Ensures(Result() > 9)\n        return value\n\nclass SubB(SuperB):\n    #:: ExpectedOutput(call.precondition:assertion.false,L1)|Label(L2)\n    def some_method(self, value: int) -> int:\n        Requires(value > 10)\n        Ensures(Result() > 10)\n        return value + 5\n\nclass SubSubB(SubB):\n    #ExpectedOutput(call.precondition:assertion.false,L2)\n    def some_method(self, value: int) -> int:\n        Requires(value > 11)\n        Ensures(Result() > 10)\n        return value + 5\n";
        let selected = BTreeSet::from(["SubB".to_owned()]);
        let result = check_heap_source_selection(source, "select/SubB.py", &selected).unwrap();
        assert!(result.passed, "{result:#?}");
        assert_eq!(result.actual.len(), 1);
        assert_eq!(result.actual[0].code, "call.precondition:assertion.false");
        assert_eq!(result.actual[0].line, 12);
    }

    #[test]
    fn scalar_fixture_manifest_is_nonempty_and_unique() {
        let directory = tempfile::tempdir().unwrap();
        let manifest = directory.path().join("fixtures.json");
        fs::write(
            &manifest,
            r#"{"schema":"maledictus-scalar-fixtures/v1","fixtures":["same.py","same.py"]}"#,
        )
        .unwrap();
        let error = check_pinned_scalar_suite(directory.path(), &manifest, &manifest).unwrap_err();
        assert!(error.contains("duplicate paths"));
    }

    #[test]
    fn nagini_entrypoint_discovery_skips_resources_and_honors_test_lists() {
        let directory = tempfile::tempdir().unwrap();
        fs::create_dir(directory.path().join("resources")).unwrap();
        fs::write(directory.path().join("resources/helper.py"), "pass\n").unwrap();
        fs::create_dir(directory.path().join("listed")).unwrap();
        fs::write(directory.path().join("listed/tests"), "chosen.py\n").unwrap();
        fs::write(directory.path().join("listed/chosen.py"), "pass\n").unwrap();
        fs::write(directory.path().join("listed/ignored.py"), "pass\n").unwrap();
        fs::write(directory.path().join("direct.py"), "pass\n").unwrap();

        let mut files = Vec::new();
        collect_nagini_test_files(directory.path(), &mut files).unwrap();
        files.sort();
        assert_eq!(files.len(), 2);
        assert!(files.iter().any(|path| path.ends_with("direct.py")));
        assert!(files.iter().any(|path| path.ends_with("chosen.py")));
    }

    #[test]
    fn filename_selection_verifies_only_selected_bodies_and_uses_other_contracts_modularly() {
        let source = "from nagini_contracts.contracts import *\n\ndef broken() -> int:\n    Ensures(Result() == 2)\n    return 1\n\ndef client() -> int:\n    Ensures(Result() == 2)\n    return broken()\n";
        let selected = BTreeSet::from(["client".to_owned()]);
        let result = check_scalar_source_selected(source, "select/client.py", &selected).unwrap();
        assert!(result.passed);
        assert!(result.actual.is_empty());

        let none = BTreeSet::from(["none".to_owned()]);
        let result = check_scalar_source_selected(source, "select/none.py", &none).unwrap();
        assert!(result.passed);
        assert!(result.actual.is_empty());
    }

    #[test]
    fn selection_names_are_derived_exactly_from_hyphenated_fixture_stem() {
        let selected = selected_symbols_from_fixture(Path::new(
            "tests/functional/verification/select/method2-func1.py",
        ))
        .unwrap();
        assert_eq!(
            selected,
            BTreeSet::from(["func1".to_owned(), "method2".to_owned()])
        );
        assert!(selected_symbols_from_fixture(Path::new("ordinary.py")).is_none());
    }

    #[test]
    fn reveal_expands_filename_selection_and_opaque_calls_remain_modular() {
        let source = "from nagini_contracts.contracts import *\n\n@Pure\n@Opaque\ndef hidden() -> int:\n    #:: ExpectedOutput(postcondition.violated:assertion.false)\n    Ensures(Result() == 2)\n    return 1\n\ndef client() -> int:\n    Ensures(Result() == 2)\n    return Reveal(hidden())\n";
        let selected = BTreeSet::from(["client".to_owned()]);
        let result = check_scalar_source_selected(source, "select/client.py", &selected).unwrap();
        assert!(result.passed);
        assert_eq!(result.actual, result.expected);
        assert_eq!(result.actual[0].line, 7);
    }

    fn classification_fixture(fixture: &str, status: &str) -> ScalarFixtureClassification {
        ScalarFixtureClassification {
            fixture: fixture.to_owned(),
            status: status.to_owned(),
            detail: format!("{status} detail"),
            expected: Vec::new(),
            actual: Vec::new(),
            match_kind: match status {
                "matched" => Some(ConformanceMatchKind::SemanticVerification),
                "profile-ignored" => Some(ConformanceMatchKind::ProfileIgnored),
                _ => None,
            },
            python_typechecker: None,
            python_typecheck_diagnostics: Vec::new(),
            annotation_profile: None,
        }
    }

    fn classifier_cache_key(lane: ClassificationLane, fixture: &str) -> ClassifierCacheKey {
        ClassifierCacheKey {
            base: ClassifierCacheBaseKey {
                schema: CLASSIFIER_CACHE_KEY_SCHEMA.to_owned(),
                lane: lane.label().to_owned(),
                fixture: fixture.to_owned(),
                fixture_sha256: "1".repeat(64),
                suite_pin_sha256: "2".repeat(64),
                suite_commit: "3".repeat(40),
                pinned_root_inventory_sha256: "4".repeat(64),
                suite_source_tree_sha256: "5".repeat(64),
                executable_sha256: "6".repeat(64),
                solver: ClassifierSolverIdentity {
                    solver: "z3".to_owned(),
                    solver_version: "test".to_owned(),
                    rust_binding: "test".to_owned(),
                    vc_ir: "test".to_owned(),
                },
                python_fragments: vec!["test-fragment/v1".to_owned()],
                checked_external_adapters: Vec::new(),
                external_stubs: Vec::new(),
                generated_interfaces: Vec::new(),
            },
            python_typechecker: None,
        }
    }

    #[test]
    fn classifier_cache_accepts_profile_ignored_results_in_every_lane() {
        let fixture = "tests/functional/ignored.py";
        let classification = classification_fixture(fixture, "profile-ignored");
        for lane in [
            ClassificationLane::Scalar,
            ClassificationLane::Heap,
            ClassificationLane::Reference,
        ] {
            let key = classifier_cache_key(lane, fixture);
            assert_eq!(
                validate_cached_fixture(lane, fixture, &key, &classification),
                Ok(())
            );
        }
    }

    fn run_test_git(root: &Path, arguments: &[&str]) -> String {
        let output = Command::new("git")
            .arg("-C")
            .arg(root)
            .args(arguments)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git {arguments:?} failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap().trim().to_owned()
    }

    #[test]
    fn classifier_cache_treats_well_formed_conflicting_results_as_a_miss() {
        let suite = tempfile::tempdir().unwrap();
        let fixture = "tests/functional/a.py";
        let fixture_path = suite.path().join(fixture);
        fs::create_dir_all(fixture_path.parent().unwrap()).unwrap();
        fs::write(&fixture_path, "").unwrap();
        run_test_git(suite.path(), &["init", "--quiet"]);
        run_test_git(suite.path(), &["add", "--all"]);
        run_test_git(
            suite.path(),
            &[
                "-c",
                "user.name=Maledictus Tests",
                "-c",
                "user.email=maledictus-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "classifier cache conflict fixture",
            ],
        );
        let commit = run_test_git(suite.path(), &["rev-parse", "HEAD"]);
        let pin_path = suite.path().join("pin.json");
        fs::write(
            &pin_path,
            serde_json::to_vec_pretty(&serde_json::json!({
                "schema": "maledictus-upstream-suite/v1",
                "project": "classifier cache conflict test",
                "repository": "https://example.invalid/classifier-cache-conflict.git",
                "tag": "test",
                "commit": commit.clone(),
                "license": "CC0-1.0",
                "test_entrypoint": "tests.py",
                "fixture_roots": ["tests/functional"],
                "fixture_profiles": [{
                    "root": "tests/functional",
                    "information_flow": "ordinary"
                }],
                "conformance_environment": {
                    "python": {"implementation": "cpython", "major": 3, "minor": 12},
                    "nagini_tag": "test",
                    "nagini_commit": commit,
                    "annotation_profiles": [{
                        "root": "tests/functional",
                        "phase": "verification",
                        "backend": "silicon"
                    }]
                }
            }))
            .unwrap(),
        )
        .unwrap();

        let repository_cache = Path::new(env!("CARGO_MANIFEST_DIR")).join(".cache");
        fs::create_dir_all(&repository_cache).unwrap();
        let cache_directory = tempfile::Builder::new()
            .prefix("classifier-cache-conflict-")
            .tempdir_in(&repository_cache)
            .unwrap();
        let cache = ClassifierCache::new(suite.path(), &pin_path, cache_directory.path()).unwrap();
        let snapshot_fixture_path = cache.analysis_root.join(fixture);
        let matched = classification_fixture(fixture, "matched");
        let refused = classification_fixture(fixture, "refused");
        cache
            .store(
                ClassificationLane::Scalar,
                fixture,
                &snapshot_fixture_path,
                None,
                &matched,
            )
            .unwrap();
        assert_eq!(
            cache
                .load(
                    ClassificationLane::Scalar,
                    fixture,
                    &snapshot_fixture_path,
                    "",
                )
                .unwrap(),
            Some(matched.clone())
        );
        cache
            .store(
                ClassificationLane::Scalar,
                fixture,
                &snapshot_fixture_path,
                None,
                &refused,
            )
            .unwrap();

        assert_eq!(
            cache
                .load(
                    ClassificationLane::Scalar,
                    fixture,
                    &snapshot_fixture_path,
                    "",
                )
                .unwrap(),
            None
        );
    }

    #[test]
    fn combined_classification_uses_the_union_without_hiding_mismatches() {
        let roots = vec!["tests/functional".to_owned()];
        let scalar_fixtures = vec![
            classification_fixture("tests/functional/scalar.py", "matched"),
            classification_fixture("tests/functional/heap.py", "refused"),
            classification_fixture("tests/functional/wrong.py", "mismatched"),
            classification_fixture("tests/functional/unknown.py", "refused"),
        ];
        let heap_fixtures = vec![
            classification_fixture("tests/functional/scalar.py", "refused"),
            classification_fixture("tests/functional/heap.py", "matched"),
            classification_fixture("tests/functional/wrong.py", "refused"),
            classification_fixture("tests/functional/unknown.py", "refused"),
        ];
        let reference_fixtures = vec![
            classification_fixture("tests/functional/scalar.py", "refused"),
            classification_fixture("tests/functional/heap.py", "refused"),
            classification_fixture("tests/functional/wrong.py", "refused"),
            classification_fixture("tests/functional/unknown.py", "refused"),
        ];
        let report = combine_classification_reports(
            "commit",
            &roots,
            vec![(
                ScalarClassificationReport {
                    schema: "scalar".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: roots[0].clone(),
                    matched: 1,
                    semantic_matched: 1,
                    production_typecheck_rejection_matched: 0,
                    source_wellformedness_rejection_matched: 0,
                    production_typecheck_divergent: 0,
                    mismatched: 1,
                    refused: 2,
                    profile_ignored: 0,
                    fixtures: scalar_fixtures,
                },
                HeapClassificationReport {
                    schema: "heap".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: roots[0].clone(),
                    matched: 1,
                    superseded_upstream_unsupported: 0,
                    mismatched: 0,
                    refused: 3,
                    profile_ignored: 0,
                    fixtures: heap_fixtures,
                },
                ReferenceClassificationReport {
                    schema: "reference".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: roots[0].clone(),
                    matched: 0,
                    mismatched: 0,
                    refused: 4,
                    profile_ignored: 0,
                    fixtures: reference_fixtures,
                },
            )],
        )
        .unwrap();
        assert_eq!(report.total, 4);
        assert_eq!(report.matched, 2);
        assert_eq!(report.mismatched, 1);
        assert_eq!(report.refused, 1);
        assert_eq!(report.scalar_matched, 1);
        assert_eq!(report.heap_matched, 1);
        assert_eq!(report.reference_matched, 0);
        assert_eq!(report.reference_refused, 4);
        assert_eq!(
            report
                .fixtures
                .iter()
                .find(|fixture| fixture.fixture.ends_with("wrong.py"))
                .unwrap()
                .status,
            "mismatched"
        );
    }

    #[test]
    fn combined_classification_keeps_source_wellformedness_separate_from_semantics() {
        let root = "tests/functional".to_owned();
        let mut scalar_fixture =
            classification_fixture("tests/functional/invalid_contract_position.py", "matched");
        scalar_fixture.match_kind = Some(ConformanceMatchKind::SourceWellformednessRejection);
        let refused_fixture =
            classification_fixture("tests/functional/invalid_contract_position.py", "refused");
        let report = combine_classification_reports(
            "commit",
            std::slice::from_ref(&root),
            vec![(
                ScalarClassificationReport {
                    schema: "scalar".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: root.clone(),
                    matched: 1,
                    semantic_matched: 0,
                    production_typecheck_rejection_matched: 0,
                    source_wellformedness_rejection_matched: 1,
                    production_typecheck_divergent: 0,
                    mismatched: 0,
                    refused: 0,
                    profile_ignored: 0,
                    fixtures: vec![scalar_fixture],
                },
                HeapClassificationReport {
                    schema: "heap".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: root.clone(),
                    matched: 0,
                    superseded_upstream_unsupported: 0,
                    mismatched: 0,
                    refused: 1,
                    profile_ignored: 0,
                    fixtures: vec![refused_fixture.clone()],
                },
                ReferenceClassificationReport {
                    schema: "reference".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: root.clone(),
                    matched: 0,
                    mismatched: 0,
                    refused: 1,
                    profile_ignored: 0,
                    fixtures: vec![refused_fixture],
                },
            )],
        )
        .unwrap();

        assert_eq!(report.matched, 1);
        assert_eq!(report.semantic_matched, 0);
        assert_eq!(report.production_typecheck_rejection_matched, 0);
        assert_eq!(report.source_wellformedness_rejection_matched, 1);
        assert_eq!(
            report.fixtures[0].match_kind,
            Some(ConformanceMatchKind::SourceWellformednessRejection)
        );
    }

    #[test]
    fn combined_classification_keeps_superseded_unsupported_out_of_exact_matches() {
        let root = "tests/functional".to_owned();
        let mut heap_fixture = classification_fixture(
            "tests/functional/sequence.py",
            "superseded-upstream-unsupported",
        );
        heap_fixture.expected = vec![ExpectedDiagnostic {
            code: "unsupported:sequence patterns not yet supported".to_owned(),
            line: 3,
        }];
        heap_fixture.match_kind = Some(ConformanceMatchKind::SupersededUpstreamUnsupported);
        heap_fixture.python_typechecker = Some(typechecker_identity());
        let refused_fixture = classification_fixture("tests/functional/sequence.py", "refused");
        let report = combine_classification_reports(
            "commit",
            std::slice::from_ref(&root),
            vec![(
                ScalarClassificationReport {
                    schema: "scalar".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: root.clone(),
                    matched: 0,
                    semantic_matched: 0,
                    production_typecheck_rejection_matched: 0,
                    source_wellformedness_rejection_matched: 0,
                    production_typecheck_divergent: 0,
                    mismatched: 0,
                    refused: 1,
                    profile_ignored: 0,
                    fixtures: vec![refused_fixture.clone()],
                },
                HeapClassificationReport {
                    schema: "heap".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: root.clone(),
                    matched: 0,
                    superseded_upstream_unsupported: 1,
                    mismatched: 0,
                    refused: 0,
                    profile_ignored: 0,
                    fixtures: vec![heap_fixture],
                },
                ReferenceClassificationReport {
                    schema: "reference".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: root.clone(),
                    matched: 0,
                    mismatched: 0,
                    refused: 1,
                    profile_ignored: 0,
                    fixtures: vec![refused_fixture],
                },
            )],
        )
        .unwrap();

        assert_eq!(report.total, 1);
        assert_eq!(report.matched, 0);
        assert_eq!(report.semantic_matched, 0);
        assert_eq!(report.superseded_upstream_unsupported, 1);
        assert_eq!(report.heap_superseded_upstream_unsupported, 1);
        assert_eq!(report.fixtures[0].expected.len(), 1);
        assert_eq!(
            report.fixtures[0].match_kind,
            Some(ConformanceMatchKind::SupersededUpstreamUnsupported)
        );
        assert!(report.fixtures[0].python_typechecker.is_some());
    }

    #[test]
    fn combined_classification_rejects_missing_or_overlapping_fixture_sets() {
        let roots = vec!["tests/a".to_owned(), "tests/b".to_owned()];
        let group = |root: &str| {
            let fixture = classification_fixture("tests/shared.py", "refused");
            (
                ScalarClassificationReport {
                    schema: "scalar".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: root.to_owned(),
                    matched: 0,
                    semantic_matched: 0,
                    production_typecheck_rejection_matched: 0,
                    source_wellformedness_rejection_matched: 0,
                    production_typecheck_divergent: 0,
                    mismatched: 0,
                    refused: 1,
                    profile_ignored: 0,
                    fixtures: vec![fixture.clone()],
                },
                HeapClassificationReport {
                    schema: "heap".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: root.to_owned(),
                    matched: 0,
                    superseded_upstream_unsupported: 0,
                    mismatched: 0,
                    refused: 1,
                    profile_ignored: 0,
                    fixtures: vec![fixture.clone()],
                },
                ReferenceClassificationReport {
                    schema: "reference".to_owned(),
                    suite_commit: "commit".to_owned(),
                    root: root.to_owned(),
                    matched: 0,
                    mismatched: 0,
                    refused: 1,
                    profile_ignored: 0,
                    fixtures: vec![fixture],
                },
            )
        };
        let error = combine_classification_reports(
            "commit",
            &roots,
            vec![group("tests/a"), group("tests/b")],
        )
        .unwrap_err();
        assert!(error.contains("overlap"), "{error}");

        let error =
            combine_classification_reports("commit", &roots, vec![group("tests/a")]).unwrap_err();
        assert!(error.contains("report groups"), "{error}");
    }
}
