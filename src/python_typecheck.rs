//! Fail-closed Python static type checking through the exact mypy release used by Nagini 1.3.1.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Output, Stdio};

use serde::Deserialize;
use sha2::{Digest, Sha256};

use crate::protocol::{Diagnostic, ExternalOverlay, PythonTypecheckerIdentity, SourceFile};

pub const MYPY_VERSION: &str = "1.5.0";
pub const PYTHON_TYPECHECK_PROFILE: &str = "strict-issuance";

#[derive(Clone, Debug)]
pub struct PythonTypecheckVerification {
    pub identity: PythonTypecheckerIdentity,
    pub diagnostics: Vec<Diagnostic>,
}

impl PythonTypecheckVerification {
    pub fn passed(&self) -> bool {
        self.diagnostics.is_empty()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PythonTypecheckFailure {
    pub code: &'static str,
    pub message: String,
}

#[derive(Debug, Deserialize)]
struct ToolchainProbe {
    version: String,
    distributions: Vec<DistributionProbe>,
}

#[derive(Debug, Deserialize)]
struct DistributionProbe {
    name: String,
    version: String,
    root: String,
    files: Vec<DistributionFileProbe>,
}

#[derive(Debug, Deserialize)]
struct DistributionFileProbe {
    relative: String,
    path: String,
}

#[derive(Debug)]
struct Toolchain {
    runtime: PathBuf,
    configuration: PathBuf,
    contract_support: Vec<PathBuf>,
    identity: PythonTypecheckerIdentity,
}

#[derive(Debug)]
struct OverlayWorkspace {
    _directory: tempfile::TempDir,
    root: PathBuf,
    files: Vec<PathBuf>,
    configuration: PathBuf,
    diagnostic_paths: BTreeMap<PathBuf, String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratedPythonInterface {
    pub module: String,
    pub contents: Vec<u8>,
    pub diagnostic_path: String,
}

/// Type-check every Python source in one closed mypy invocation. `Ok(None)` means the request has
/// no Python source. A toolchain/protocol failure is distinct from ordinary located type errors.
pub fn typecheck_request_sources(
    source_root: &Path,
    files: &[SourceFile],
    overlays: &[ExternalOverlay],
) -> Result<Option<PythonTypecheckVerification>, PythonTypecheckFailure> {
    typecheck_request_sources_with_interfaces(source_root, files, overlays, &[])
}

pub fn typecheck_request_sources_with_interfaces(
    source_root: &Path,
    files: &[SourceFile],
    overlays: &[ExternalOverlay],
    generated_interfaces: &[GeneratedPythonInterface],
) -> Result<Option<PythonTypecheckVerification>, PythonTypecheckFailure> {
    let python_files = files
        .iter()
        .filter(|source| source.language == "python")
        .collect::<Vec<_>>();
    if python_files.is_empty() {
        return Ok(None);
    }
    let root = fs::canonicalize(source_root).map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.source-root",
        message: format!("cannot canonicalize Python source root {source_root:?}: {error}"),
    })?;
    let mut checked_paths = Vec::with_capacity(python_files.len());
    let mut canonical_to_request = BTreeMap::new();
    for source in python_files {
        let path = confined_source_path(&root, &source.path)?;
        canonical_to_request.insert(path.clone(), source.path.clone());
        checked_paths.push(path);
    }

    let mut toolchain = resolve_toolchain()?;
    let overlay_workspace =
        materialize_overlay_stubs(&root, overlays, generated_interfaces, &toolchain)?;
    toolchain.identity.configuration_sha256 = hash_file(&overlay_workspace.configuration)?;
    let mut search_paths = vec![root.clone(), overlay_workspace.root.clone()];
    search_paths.extend(toolchain.contract_support.iter().cloned());
    let mypy_path = std::env::join_paths(search_paths).map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.import-path",
        message: format!("cannot encode confined mypy import path: {error}"),
    })?;

    let mut command = Command::new(&toolchain.runtime);
    let mypy_cache = overlay_workspace.root.join("mypy-cache");
    command
        .arg("-m")
        .arg("mypy")
        .arg("--config-file")
        .arg(&overlay_workspace.configuration)
        .arg("--cache-dir")
        .arg(&mypy_cache)
        .args(&checked_paths)
        .args(&overlay_workspace.files)
        .current_dir(&root)
        .env_remove("MYPY_CONFIG_FILE")
        .env_remove("PYTHONPATH")
        .env("PYTHONDONTWRITEBYTECODE", "1")
        .env("MYPYPATH", mypy_path)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for contract_support in &toolchain.contract_support {
        command.args(contract_support_files(contract_support)?);
    }
    let output = command.output().map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.unavailable",
        message: format!("cannot start pinned mypy {MYPY_VERSION}: {error}"),
    })?;
    interpret_typecheck_output(
        output,
        &root,
        &canonical_to_request,
        &overlay_workspace.diagnostic_paths,
        toolchain.identity,
    )
    .map(Some)
}

fn resolve_toolchain() -> Result<Toolchain, PythonTypecheckFailure> {
    let runtime = resolve_python_runtime()?;
    let probe_output = Command::new(&runtime)
        .arg("-c")
        .arg(
            "import importlib.metadata as m, json, pathlib, mypy.version; names=('mypy','mypy_extensions','typing_extensions'); distributions=[]; [(lambda d: distributions.append({'name': n, 'version': d.version, 'root': str(pathlib.Path(d.locate_file('.')).resolve()), 'files': [{'relative': str(f).replace('\\\\','/'), 'path': str(pathlib.Path(d.locate_file(f)).resolve())} for f in (d.files or ())]}))(m.distribution(n)) for n in names]; print(json.dumps({'version': mypy.version.__version__, 'distributions': distributions}))",
        )
        .env("PYTHONDONTWRITEBYTECODE", "1")
        .stdin(Stdio::null())
        .output()
        .map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.unavailable",
            message: format!("cannot inspect configured Python typechecker: {error}"),
        })?;
    if !probe_output.status.success() {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.unavailable",
            message: format!(
                "configured Python runtime cannot import mypy: {}",
                String::from_utf8_lossy(&probe_output.stderr).trim()
            ),
        });
    }
    let probe: ToolchainProbe =
        serde_json::from_slice(&probe_output.stdout).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.protocol",
            message: format!("invalid mypy toolchain probe response: {error}"),
        })?;
    validate_exact_version(&probe.version)?;
    validate_distribution_set(&probe.distributions)?;
    let configuration = resolve_configuration()?;
    let contract_support = resolve_contract_support();
    let runtime_version = command_version(&runtime)?;
    let runtime_root = runtime_bundle_root(&runtime)?;
    let identity = PythonTypecheckerIdentity {
        checker: "mypy".to_owned(),
        checker_version: MYPY_VERSION.to_owned(),
        profile: PYTHON_TYPECHECK_PROFILE.to_owned(),
        package_sha256: hash_distribution_bundle(&probe.distributions)?,
        runtime: "python".to_owned(),
        runtime_version,
        runtime_executable_sha256: hash_file(&runtime)?,
        runtime_bundle_sha256: hash_runtime_bundle(&runtime_root)?,
        configuration_sha256: hash_file(&configuration)?,
        contract_support_sha256: (!contract_support.is_empty())
            .then(|| hash_support_roots(&contract_support))
            .transpose()?,
    };
    Ok(Toolchain {
        runtime,
        configuration,
        contract_support,
        identity,
    })
}

fn validate_exact_version(version: &str) -> Result<(), PythonTypecheckFailure> {
    if version == MYPY_VERSION {
        Ok(())
    } else {
        Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.version",
            message: format!(
                "Maledictus requires mypy {MYPY_VERSION} exactly for Nagini 1.3.1 compatibility; configured runtime provides {version}"
            ),
        })
    }
}

fn validate_distribution_set(
    distributions: &[DistributionProbe],
) -> Result<(), PythonTypecheckFailure> {
    let expected = ["mypy", "mypy_extensions", "typing_extensions"];
    if distributions.len() != expected.len()
        || distributions
            .iter()
            .zip(expected)
            .any(|(distribution, name)| {
                distribution.name != name
                    || distribution.version.is_empty()
                    || distribution.files.is_empty()
            })
    {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.package-identity",
            message: format!(
                "mypy toolchain probe must return complete ordered RECORD manifests for {expected:?}"
            ),
        });
    }
    if distributions[0].version != MYPY_VERSION {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.version",
            message: format!(
                "mypy distribution metadata reports {}, expected {MYPY_VERSION}",
                distributions[0].version
            ),
        });
    }
    Ok(())
}

fn hash_distribution_bundle(
    distributions: &[DistributionProbe],
) -> Result<String, PythonTypecheckFailure> {
    let mut digest = Sha256::new();
    for distribution in distributions {
        let _root =
            fs::canonicalize(&distribution.root).map_err(|error| PythonTypecheckFailure {
                code: "frontend.python.typecheck.package-identity",
                message: format!(
                    "cannot resolve distribution root {:?}: {error}",
                    distribution.root
                ),
            })?;
        let mut files = distribution
            .files
            .iter()
            .map(|file| (file.relative.as_str(), file.path.as_str()))
            .collect::<Vec<_>>();
        files.sort_by(|left, right| left.0.cmp(right.0));
        digest_field(&mut digest, distribution.name.as_bytes());
        digest_field(&mut digest, distribution.version.as_bytes());
        for (relative, path) in files {
            if relative.is_empty() || Path::new(relative).is_absolute() {
                return Err(PythonTypecheckFailure {
                    code: "frontend.python.typecheck.package-identity",
                    message: format!(
                        "distribution {:?} contains invalid RECORD path {relative:?}",
                        distribution.name
                    ),
                });
            }
            let canonical = fs::canonicalize(path).map_err(|error| PythonTypecheckFailure {
                code: "frontend.python.typecheck.package-identity",
                message: format!(
                    "cannot resolve RECORD file {relative:?} for distribution {:?}: {error}",
                    distribution.name
                ),
            })?;
            if !canonical.is_file() {
                return Err(PythonTypecheckFailure {
                    code: "frontend.python.typecheck.package-identity",
                    message: format!(
                        "RECORD entry {relative:?} for distribution {:?} is not a file",
                        distribution.name
                    ),
                });
            }
            let bytes = fs::read(&canonical).map_err(|error| PythonTypecheckFailure {
                code: "frontend.python.typecheck.package-identity",
                message: format!("cannot hash distribution file {canonical:?}: {error}"),
            })?;
            digest_field(&mut digest, relative.as_bytes());
            digest_field(&mut digest, &bytes);
        }
    }
    Ok(digest
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn digest_field(digest: &mut Sha256, bytes: &[u8]) {
    digest.update((bytes.len() as u64).to_be_bytes());
    digest.update(bytes);
}

fn resolve_python_runtime() -> Result<PathBuf, PythonTypecheckFailure> {
    let mut candidates = Vec::new();
    if let Some(path) = std::env::var_os("MALEDICTUS_MYPY_PYTHON") {
        candidates.push(PathBuf::from(path));
    }
    if let Ok(executable) = std::env::current_exe()
        && let Some(directory) = executable.parent()
    {
        candidates.push(directory.join("python-typecheck/python.exe"));
        candidates.push(directory.join("python-typecheck/bin/python"));
    }
    let development = Path::new(env!("CARGO_MANIFEST_DIR")).join(".cache/mypy-1.5");
    candidates.push(development.join("Scripts/python.exe"));
    candidates.push(development.join("bin/python"));
    for directory in std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()) {
        candidates.push(directory.join(if cfg!(windows) {
            "python.exe"
        } else {
            "python3"
        }));
    }
    for candidate in candidates {
        if candidate.is_file() {
            return fs::canonicalize(&candidate).map_err(|error| PythonTypecheckFailure {
                code: "frontend.python.typecheck.runtime-identity",
                message: format!("cannot canonicalize Python runtime {candidate:?}: {error}"),
            });
        }
    }
    Err(PythonTypecheckFailure {
        code: "frontend.python.typecheck.unavailable",
        message: format!(
            "pinned mypy {MYPY_VERSION} runtime was not found; set MALEDICTUS_MYPY_PYTHON to its Python executable"
        ),
    })
}

fn resolve_configuration() -> Result<PathBuf, PythonTypecheckFailure> {
    let mut candidates = Vec::new();
    if let Some(path) = std::env::var_os("MALEDICTUS_MYPY_CONFIG") {
        candidates.push(PathBuf::from(path));
    }
    if let Ok(executable) = std::env::current_exe()
        && let Some(directory) = executable.parent()
    {
        candidates.push(directory.join("python-typecheck/mypy-1.5.ini"));
    }
    candidates.push(Path::new(env!("CARGO_MANIFEST_DIR")).join("python_typecheck/mypy-1.5.ini"));
    for candidate in candidates {
        if candidate.is_file() {
            return fs::canonicalize(&candidate).map_err(|error| PythonTypecheckFailure {
                code: "frontend.python.typecheck.configuration",
                message: format!("cannot canonicalize mypy configuration {candidate:?}: {error}"),
            });
        }
    }
    Err(PythonTypecheckFailure {
        code: "frontend.python.typecheck.configuration",
        message: "pinned mypy configuration was not found".to_owned(),
    })
}

fn resolve_contract_support() -> Vec<PathBuf> {
    let mut roots = Vec::new();
    if let Ok(executable) = std::env::current_exe()
        && let Some(directory) = executable.parent()
    {
        let packaged = directory.join("python-typecheck/support");
        if packaged.is_dir()
            && let Ok(canonical) = fs::canonicalize(packaged)
        {
            return vec![canonical];
        }
    }
    let built_in = Path::new(env!("CARGO_MANIFEST_DIR")).join("python_typecheck/support");
    if built_in.is_dir()
        && let Ok(canonical) = fs::canonicalize(built_in)
        && !roots.contains(&canonical)
    {
        roots.push(canonical);
    }
    let nagini = std::env::var_os("MALEDICTUS_NAGINI_CONTRACTS")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join(".upstream/nagini/src"));
    if nagini.join("nagini_contracts").is_dir()
        && let Ok(canonical) = fs::canonicalize(nagini)
        && !roots.contains(&canonical)
    {
        roots.push(canonical);
    }
    roots
}

fn confined_source_path(root: &Path, relative: &str) -> Result<PathBuf, PythonTypecheckFailure> {
    let relative_path = Path::new(relative);
    if relative_path.is_absolute()
        || relative_path.components().any(|part| {
            matches!(
                part,
                Component::ParentDir | Component::RootDir | Component::Prefix(_)
            )
        })
    {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.source-path",
            message: format!("Python typecheck path must stay below source_root: {relative:?}"),
        });
    }
    let path =
        fs::canonicalize(root.join(relative_path)).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.source-path",
            message: format!("cannot resolve Python typecheck path {relative:?}: {error}"),
        })?;
    if !path.starts_with(root) || !path.is_file() {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.source-path",
            message: format!("Python typecheck path escapes source_root: {relative:?}"),
        });
    }
    Ok(path)
}

fn materialize_overlay_stubs(
    root: &Path,
    overlays: &[ExternalOverlay],
    generated_interfaces: &[GeneratedPythonInterface],
    toolchain: &Toolchain,
) -> Result<OverlayWorkspace, PythonTypecheckFailure> {
    let directory = tempfile::Builder::new()
        .prefix("maledictus-mypy-overlays-")
        .tempdir()
        .map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-workspace",
            message: format!("cannot create isolated mypy overlay workspace: {error}"),
        })?;
    let overlay_root = directory.path().to_path_buf();
    let configuration = overlay_root.join("mypy.ini");
    let configuration_bytes =
        fs::read(&toolchain.configuration).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.configuration",
            message: format!("cannot read pinned mypy configuration: {error}"),
        })?;
    let mut diagnostic_paths = BTreeMap::new();
    let mut files = Vec::new();
    let mut modules = BTreeMap::<String, Vec<u8>>::new();
    for overlay in overlays {
        let segments = checked_module_segments(&overlay.module)?;
        reject_source_owned_overlay_module(root, &segments, &overlay.module)?;
        let stub_path = confined_source_path(root, &overlay.stub_path)?;
        let bytes = generate_external_interface(
            &toolchain.runtime,
            &stub_path,
            &overlay_root.join(format!("stubgen-{}", modules.len())),
        )?;
        if let Some(existing) = modules.get(&overlay.module) {
            if existing != &bytes {
                return Err(PythonTypecheckFailure {
                    code: "frontend.python.typecheck.overlay-conflict",
                    message: format!(
                        "external module {:?} has conflicting type contract overlays",
                        overlay.module
                    ),
                });
            }
            continue;
        }
        modules.insert(overlay.module.clone(), bytes.clone());
        let mut generated = overlay_root.clone();
        for segment in &segments[..segments.len() - 1] {
            generated.push(segment);
        }
        fs::create_dir_all(&generated).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-workspace",
            message: format!("cannot create isolated external module package: {error}"),
        })?;
        generated.push(format!("{}.pyi", segments[segments.len() - 1]));
        fs::write(&generated, bytes).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-workspace",
            message: format!("cannot write isolated external module contract: {error}"),
        })?;
        let canonical = fs::canonicalize(&generated).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-workspace",
            message: format!("cannot resolve isolated external module contract: {error}"),
        })?;
        files.push(canonical.clone());
        diagnostic_paths.insert(canonical, overlay.stub_path.clone());
    }
    for interface in generated_interfaces {
        let segments = checked_module_segments(&interface.module)?;
        reject_source_owned_overlay_module(root, &segments, &interface.module)?;
        if modules
            .insert(interface.module.clone(), interface.contents.clone())
            .is_some()
        {
            return Err(PythonTypecheckFailure {
                code: "frontend.python.typecheck.overlay-conflict",
                message: format!(
                    "generated cross-language module {:?} conflicts with another interface",
                    interface.module
                ),
            });
        }
        let mut generated = overlay_root.clone();
        for segment in &segments[..segments.len() - 1] {
            generated.push(segment);
        }
        fs::create_dir_all(&generated).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-workspace",
            message: format!("cannot create generated interface package: {error}"),
        })?;
        generated.push(format!("{}.pyi", segments[segments.len() - 1]));
        fs::write(&generated, &interface.contents).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-workspace",
            message: format!("cannot write generated cross-language interface: {error}"),
        })?;
        let canonical = fs::canonicalize(&generated).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-workspace",
            message: format!("cannot resolve generated cross-language interface: {error}"),
        })?;
        files.push(canonical.clone());
        diagnostic_paths.insert(canonical, interface.diagnostic_path.clone());
    }
    fs::write(&configuration, configuration_bytes).map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.configuration",
        message: format!("cannot write isolated mypy overlay configuration: {error}"),
    })?;
    Ok(OverlayWorkspace {
        _directory: directory,
        root: overlay_root,
        files,
        configuration,
        diagnostic_paths,
    })
}

fn generate_external_interface(
    runtime: &Path,
    contract_source: &Path,
    output_root: &Path,
) -> Result<Vec<u8>, PythonTypecheckFailure> {
    fs::create_dir_all(output_root).map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.overlay-workspace",
        message: format!("cannot create external interface workspace: {error}"),
    })?;
    let output = Command::new(runtime)
        .arg("-m")
        .arg("mypy.stubgen")
        .arg("--no-import")
        .arg("--parse-only")
        .arg("--include-private")
        .arg("--quiet")
        .arg("--output")
        .arg(output_root)
        .arg(contract_source)
        .env_remove("MYPY_CONFIG_FILE")
        .env_remove("PYTHONPATH")
        .env("PYTHONDONTWRITEBYTECODE", "1")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-interface",
            message: format!("cannot start pinned stubgen for external contract: {error}"),
        })?;
    if !output.status.success() || !output.stderr.is_empty() || !output.stdout.is_empty() {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-interface",
            message: format!(
                "pinned stubgen did not produce a clean external type interface (exit {:?}, stdout {:?}, stderr {:?})",
                output.status.code(),
                String::from_utf8_lossy(&output.stdout).trim(),
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        });
    }
    let mut generated = Vec::new();
    collect_python_interface_files(output_root, &mut generated)?;
    generated.retain(|path| path.extension().is_some_and(|extension| extension == "pyi"));
    if generated.len() != 1 {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-interface",
            message: format!(
                "pinned stubgen produced {} interfaces for one external contract",
                generated.len()
            ),
        });
    }
    fs::read(&generated[0]).map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.overlay-interface",
        message: format!("cannot read generated external type interface: {error}"),
    })
}

fn reject_source_owned_overlay_module(
    root: &Path,
    segments: &[&str],
    module: &str,
) -> Result<(), PythonTypecheckFailure> {
    let mut candidate = root.to_path_buf();
    for segment in segments {
        candidate.push(segment);
    }
    let module_file = candidate.with_extension("py");
    let module_stub = candidate.with_extension("pyi");
    let package_file = candidate.join("__init__.py");
    let package_stub = candidate.join("__init__.pyi");
    if [module_file, module_stub, package_file, package_stub]
        .iter()
        .any(|path| path.exists())
    {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-source-conflict",
            message: format!(
                "declared external module {module:?} resolves to source below source_root and cannot receive an error-suppressed external contract"
            ),
        });
    }
    Ok(())
}

fn contract_support_files(root: &Path) -> Result<Vec<PathBuf>, PythonTypecheckFailure> {
    let mut files = Vec::new();
    for package in support_package_roots(root) {
        collect_python_interface_files(&package, &mut files)?;
    }
    files.sort();
    if files.is_empty() {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.contract-support",
            message: format!("contract support root {root:?} contains no Python interfaces"),
        });
    }
    Ok(files)
}

fn support_package_roots(root: &Path) -> Vec<PathBuf> {
    ["dagcert", "nagini_contracts"]
        .into_iter()
        .map(|package| root.join(package))
        .filter(|package| package.is_dir())
        .collect()
}

fn collect_python_interface_files(
    directory: &Path,
    files: &mut Vec<PathBuf>,
) -> Result<(), PythonTypecheckFailure> {
    for entry in fs::read_dir(directory).map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.contract-support",
        message: format!("cannot enumerate Nagini contract support {directory:?}: {error}"),
    })? {
        let entry = entry.map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.contract-support",
            message: error.to_string(),
        })?;
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "__pycache__") {
                continue;
            }
            collect_python_interface_files(&path, files)?;
        } else if path.is_file()
            && path
                .extension()
                .and_then(|value| value.to_str())
                .is_some_and(|extension| matches!(extension, "py" | "pyi"))
        {
            files.push(
                fs::canonicalize(&path).map_err(|error| PythonTypecheckFailure {
                    code: "frontend.python.typecheck.contract-support",
                    message: format!("cannot resolve Nagini contract interface {path:?}: {error}"),
                })?,
            );
        }
    }
    Ok(())
}

fn checked_module_segments(module: &str) -> Result<Vec<&str>, PythonTypecheckFailure> {
    let segments = module.split('.').collect::<Vec<_>>();
    if segments.is_empty()
        || segments.iter().any(|segment| {
            segment.is_empty()
                || !segment.bytes().enumerate().all(|(index, byte)| {
                    byte == b'_'
                        || byte.is_ascii_alphabetic()
                        || (index > 0 && byte.is_ascii_digit())
                })
        })
    {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.overlay-module",
            message: format!(
                "external overlay module {module:?} is not a dotted Python identifier"
            ),
        });
    }
    Ok(segments)
}

fn interpret_typecheck_output(
    output: Output,
    root: &Path,
    source_paths: &BTreeMap<PathBuf, String>,
    overlay_paths: &BTreeMap<PathBuf, String>,
    identity: PythonTypecheckerIdentity,
) -> Result<PythonTypecheckVerification, PythonTypecheckFailure> {
    if !output.stderr.is_empty() {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.process",
            message: format!(
                "mypy wrote unexpected stderr: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        });
    }
    let stdout = String::from_utf8(output.stdout).map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.protocol",
        message: format!("mypy diagnostics are not UTF-8: {error}"),
    })?;
    let mut diagnostics = Vec::new();
    for line in stdout.lines().filter(|line| !line.trim().is_empty()) {
        let Some(parsed) = parse_mypy_diagnostic(line)? else {
            continue;
        };
        if parsed.severity == "note" {
            continue;
        }
        let reported = PathBuf::from(&parsed.path);
        let absolute = if reported.is_absolute() {
            reported
        } else {
            root.join(reported)
        };
        let canonical = fs::canonicalize(&absolute).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.diagnostic-path",
            message: format!("cannot resolve mypy diagnostic path {absolute:?}: {error}"),
        })?;
        let request_path = source_paths
            .get(&canonical)
            .or_else(|| overlay_paths.get(&canonical))
            .ok_or_else(|| PythonTypecheckFailure {
                code: "frontend.python.typecheck.import-confinement",
                message: format!(
                    "mypy reported an error in unbound source {canonical:?}; only requested source and declared external overlays may influence issuance"
                ),
            })?;
        diagnostics.push(match (parsed.line, parsed.column) {
            (Some(line), Some(column)) => Diagnostic::located_error(
                format!("frontend.python.typecheck.{}", parsed.code),
                parsed.message,
                request_path,
                line,
                column,
            ),
            (line, None) => Diagnostic {
                severity: "error".to_owned(),
                code: format!("frontend.python.typecheck.{}", parsed.code),
                message: parsed.message,
                path: Some(request_path.clone()),
                line,
                column: None,
            },
            (None, Some(_)) => unreachable!("a column cannot exist without a line"),
        });
    }
    match output.status.code() {
        Some(0) if diagnostics.is_empty() => Ok(PythonTypecheckVerification {
            identity,
            diagnostics,
        }),
        Some(0) => Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.protocol",
            message: "mypy exited successfully while reporting type errors".to_owned(),
        }),
        Some(1) if !diagnostics.is_empty() => Ok(PythonTypecheckVerification {
            identity,
            diagnostics,
        }),
        status => Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.process",
            message: format!(
                "mypy failed without located type diagnostics (exit {status:?}): {}",
                stdout.trim()
            ),
        }),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct ParsedDiagnostic {
    path: String,
    line: Option<u32>,
    column: Option<u32>,
    severity: String,
    message: String,
    code: String,
}

fn parse_mypy_diagnostic(line: &str) -> Result<Option<ParsedDiagnostic>, PythonTypecheckFailure> {
    let (prefix, severity, detail) = if let Some((prefix, detail)) = line.split_once(": error: ") {
        (prefix, "error", detail)
    } else if let Some((prefix, detail)) = line.split_once(": note: ") {
        (prefix, "note", detail)
    } else {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.protocol",
            message: format!("unrecognized mypy output line: {line:?}"),
        });
    };
    let (path, line_number, column) = match prefix.rsplit_once(':') {
        Some((before_last, last)) if last.parse::<u32>().is_ok() => {
            let last_number = parse_location_number(Some(last), "line or column", line)?;
            match before_last.rsplit_once(':') {
                Some((path, possible_line)) if possible_line.parse::<u32>().is_ok() => (
                    path,
                    Some(parse_location_number(Some(possible_line), "line", line)?),
                    Some(last_number),
                ),
                _ => (before_last, Some(last_number), None),
            }
        }
        _ if !prefix.is_empty() => (prefix, None, None),
        _ => {
            return Err(PythonTypecheckFailure {
                code: "frontend.python.typecheck.protocol",
                message: format!("mypy diagnostic has no source path: {line:?}"),
            });
        }
    };
    let coded = detail
        .strip_suffix(']')
        .and_then(|value| value.rsplit_once("  ["));
    let (message, code) = match (severity, coded) {
        (_, Some(coded)) => coded,
        ("note", None) => (detail, "note"),
        _ => {
            return Err(PythonTypecheckFailure {
                code: "frontend.python.typecheck.protocol",
                message: format!("mypy diagnostic has no error code: {line:?}"),
            });
        }
    };
    Ok(Some(ParsedDiagnostic {
        path: path.to_owned(),
        line: line_number,
        column,
        severity: severity.to_owned(),
        message: message.to_owned(),
        code: code.to_owned(),
    }))
}

fn parse_location_number(
    value: Option<&str>,
    label: &str,
    source: &str,
) -> Result<u32, PythonTypecheckFailure> {
    value
        .and_then(|value| value.parse().ok())
        .filter(|value| *value > 0)
        .ok_or_else(|| PythonTypecheckFailure {
            code: "frontend.python.typecheck.protocol",
            message: format!("mypy diagnostic has invalid {label}: {source:?}"),
        })
}

fn command_version(runtime: &Path) -> Result<String, PythonTypecheckFailure> {
    let output = Command::new(runtime)
        .arg("--version")
        .env("PYTHONDONTWRITEBYTECODE", "1")
        .stdin(Stdio::null())
        .output()
        .map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.runtime-identity",
            message: format!("cannot inspect Python runtime version: {error}"),
        })?;
    if !output.status.success() {
        return Err(PythonTypecheckFailure {
            code: "frontend.python.typecheck.runtime-identity",
            message: String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        });
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn hash_file(path: &Path) -> Result<String, PythonTypecheckFailure> {
    let bytes = fs::read(path).map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.identity",
        message: format!("cannot hash {path:?}: {error}"),
    })?;
    Ok(hex_digest(&bytes))
}

fn runtime_bundle_root(runtime: &Path) -> Result<PathBuf, PythonTypecheckFailure> {
    let parent = runtime.parent().ok_or_else(|| PythonTypecheckFailure {
        code: "frontend.python.typecheck.runtime-identity",
        message: format!("Python runtime has no containing directory: {runtime:?}"),
    })?;
    let root = if parent
        .file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name.eq_ignore_ascii_case("scripts") || name == "bin")
        && parent
            .parent()
            .is_some_and(|candidate| candidate.join("pyvenv.cfg").is_file())
    {
        parent.parent().expect("parent existence was checked")
    } else {
        parent
    };
    fs::canonicalize(root).map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.runtime-identity",
        message: format!("cannot resolve Python runtime bundle {root:?}: {error}"),
    })
}

fn hash_runtime_bundle(root: &Path) -> Result<String, PythonTypecheckFailure> {
    let mut files = Vec::new();
    collect_files(root, root, &mut files)?;
    files.sort_by(|left, right| left.0.cmp(&right.0));
    let mut digest = Sha256::new();
    for (relative, path) in files {
        let bytes = fs::read(&path).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.runtime-identity",
            message: format!("cannot hash Python runtime file {path:?}: {error}"),
        })?;
        digest_field(&mut digest, relative.as_bytes());
        digest_field(&mut digest, &Sha256::digest(bytes));
    }
    Ok(digest
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn hash_support_roots(roots: &[PathBuf]) -> Result<String, PythonTypecheckFailure> {
    let mut files = Vec::new();
    for root in roots {
        for package in support_package_roots(root) {
            let package_name = package
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or_else(|| PythonTypecheckFailure {
                    code: "frontend.python.typecheck.identity",
                    message: format!("contract support package has an invalid name: {package:?}"),
                })?;
            let mut package_files = Vec::new();
            collect_files(&package, &package, &mut package_files)?;
            files.extend(
                package_files
                    .into_iter()
                    .map(|(relative, path)| (format!("{package_name}/{relative}"), path)),
            );
        }
    }
    files.sort_by(|left, right| left.0.cmp(&right.0));
    let mut digest = Sha256::new();
    for (relative, path) in files {
        let bytes = fs::read(&path).map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.identity",
            message: format!("cannot hash contract support {path:?}: {error}"),
        })?;
        digest_field(&mut digest, relative.as_bytes());
        digest_field(&mut digest, &bytes);
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
) -> Result<(), PythonTypecheckFailure> {
    for entry in fs::read_dir(directory).map_err(|error| PythonTypecheckFailure {
        code: "frontend.python.typecheck.identity",
        message: format!("cannot enumerate {directory:?}: {error}"),
    })? {
        let entry = entry.map_err(|error| PythonTypecheckFailure {
            code: "frontend.python.typecheck.identity",
            message: error.to_string(),
        })?;
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "__pycache__") {
                continue;
            }
            collect_files(root, &path, files)?;
        } else if path.is_file() {
            if path
                .extension()
                .and_then(|value| value.to_str())
                .is_some_and(|extension| matches!(extension, "pyc" | "pyo"))
            {
                continue;
            }
            let relative = path
                .strip_prefix(root)
                .map_err(|error| PythonTypecheckFailure {
                    code: "frontend.python.typecheck.identity",
                    message: error.to_string(),
                })?
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_version_is_not_a_compatibility_range() {
        assert!(validate_exact_version("1.5.0").is_ok());
        let error = validate_exact_version("2.3.1").unwrap_err();
        assert_eq!(error.code, "frontend.python.typecheck.version");
    }

    #[test]
    fn parses_windows_and_posix_located_diagnostics_without_losing_the_drive() {
        let windows = parse_mypy_diagnostic(
            r"G:\app\source.py:12:7: error: Incompatible return value type  [return-value]",
        )
        .unwrap()
        .unwrap();
        assert_eq!(windows.path, r"G:\app\source.py");
        assert_eq!(windows.line, Some(12));
        assert_eq!(windows.column, Some(7));
        assert_eq!(windows.code, "return-value");

        let posix = parse_mypy_diagnostic(
            "/work/source.py:3:2: error: Unsupported operand types  [operator]",
        )
        .unwrap()
        .unwrap();
        assert_eq!(posix.path, "/work/source.py");
        assert_eq!(posix.code, "operator");
    }

    #[test]
    fn parses_windows_diagnostic_without_a_column() {
        let diagnostic = parse_mypy_diagnostic(
            r"\\?\G:\work\source.py:15: error: Unused type ignore  [unused-ignore]",
        )
        .unwrap()
        .unwrap();
        assert_eq!(diagnostic.path, r"\\?\G:\work\source.py");
        assert_eq!(diagnostic.line, Some(15));
        assert_eq!(diagnostic.column, None);
        assert_eq!(diagnostic.code, "unused-ignore");
    }

    #[test]
    fn parses_windows_diagnostic_without_a_line() {
        let diagnostic = parse_mypy_diagnostic(
            r#"\\?\G:\work\provider.py: error: Ancestor package "pkg" ignored  [misc]"#,
        )
        .unwrap()
        .unwrap();
        assert_eq!(diagnostic.path, r"\\?\G:\work\provider.py");
        assert_eq!(diagnostic.line, None);
        assert_eq!(diagnostic.column, None);
        assert_eq!(diagnostic.code, "misc");
    }

    #[test]
    fn arbitrary_process_output_is_not_treated_as_a_typecheck_result() {
        let error = parse_mypy_diagnostic("Success: no issues found in 1 source file").unwrap_err();
        assert_eq!(error.code, "frontend.python.typecheck.protocol");
    }

    #[test]
    fn overlay_modules_are_finite_dotted_identifiers() {
        assert_eq!(
            checked_module_segments("provider.api").unwrap(),
            vec!["provider", "api"]
        );
        assert!(checked_module_segments("../provider").is_err());
        assert!(checked_module_segments("provider-name").is_err());
        assert!(checked_module_segments("provider..api").is_err());
    }
}
