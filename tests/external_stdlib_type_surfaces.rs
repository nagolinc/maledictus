use std::fs;

use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofStatus,
    SourceFile,
};
use maledictus::python_typecheck::typecheck_request_sources;

const IO_CONTRACT: &str = r#"from nagini_contracts.contracts import ContractOnly, Exsures

class TextIOWrapper:
    @ContractOnly
    def write(self, text: str) -> int:
        Exsures(Exception, True)
        ...
"#;

const PATH_CONTRACT: &str = r#"from nagini_contracts.contracts import ContractOnly, Exsures

class Path:
    @ContractOnly
    def __init__(self, value: str) -> None:
        Exsures(Exception, True)
        ...

    @ContractOnly
    def __fspath__(self) -> str:
        Exsures(Exception, True)
        ...
"#;

fn request(directory: &std::path::Path, module: &str, source: &str) -> ProofRequest {
    fs::write(directory.join("app.py"), source).unwrap();
    fs::write(
        directory.join("contract.py"),
        match module {
            "io" => IO_CONTRACT,
            "pathlib" => PATH_CONTRACT,
            _ => panic!("unexpected stdlib contract {module}"),
        },
    )
    .unwrap();
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        external_contract_overlays: vec![ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: module.to_owned(),
            stub_path: "contract.py".to_owned(),
            exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
        }],
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    }
}

#[test]
fn partial_text_file_effects_do_not_erase_the_real_bytesio_static_api() {
    let directory = tempfile::tempdir().unwrap();
    let request = request(
        directory.path(),
        "io",
        r#"from io import BytesIO, TextIOWrapper

def run(stream: TextIOWrapper) -> bytes:
    data = BytesIO(b'payload')
    stream.write('text')
    return data.getvalue()
"#,
    );
    let result = typecheck_request_sources(
        directory.path(),
        &request.files,
        &request.external_contract_overlays,
    )
    .unwrap()
    .unwrap();
    assert!(result.passed(), "{result:#?}");
    // This checks the real static API, not undeclared BytesIO effect semantics.
}

#[test]
fn partial_path_effects_keep_actual_pathlike_and_purepath_compatibility() {
    let directory = tempfile::tempdir().unwrap();
    let request = request(
        directory.path(),
        "pathlib",
        r#"from os import PathLike
from pathlib import Path, PurePath
import sqlite3

def run() -> PathLike[str]:
    path = Path('database.sqlite3')
    pure: PurePath = path
    connection = sqlite3.connect(path)
    connection.close()
    return pure
"#,
    );
    let result = typecheck_request_sources(
        directory.path(),
        &request.files,
        &request.external_contract_overlays,
    )
    .unwrap()
    .unwrap();
    assert!(result.passed(), "{result:#?}");
}

#[test]
fn real_stdlib_interfaces_still_reject_wrong_primitive_arguments() {
    for (module, source) in [
        (
            "io",
            "from io import BytesIO\n\ndef run() -> bytes:\n    data = BytesIO('not bytes')\n    return data.getvalue()\n",
        ),
        (
            "io",
            "from io import TextIOWrapper\n\ndef run(stream: TextIOWrapper) -> int:\n    return stream.write(12)\n",
        ),
        (
            "pathlib",
            "from pathlib import Path\n\ndef run() -> Path:\n    return Path(12)\n",
        ),
    ] {
        let directory = tempfile::tempdir().unwrap();
        let request = request(directory.path(), module, source);
        let result = typecheck_request_sources(
            directory.path(),
            &request.files,
            &request.external_contract_overlays,
        )
        .unwrap()
        .unwrap();
        assert!(!result.passed(), "{module}: {result:#?}");
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "frontend.python.typecheck.arg-type"),
            "{module}: {result:#?}"
        );
    }
}

fn assert_uncontracted_method_refused(module: &str, source: &str, method: &str) {
    let directory = tempfile::tempdir().unwrap();
    let request = request(directory.path(), module, source);
    let static_result = typecheck_request_sources(
        directory.path(),
        &request.files,
        &request.external_contract_overlays,
    )
    .unwrap()
    .unwrap();
    assert!(static_result.passed(), "{static_result:#?}");

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            matches!(
                diagnostic.code.as_str(),
                "frontend.python.heap.method-call-effects-unsupported"
                    | "frontend.python.heap.conditional-statement-effect-target-unsupported"
            ) && diagnostic.message.contains(method)
        }),
        "{response:#?}"
    );
    assert!(response.obligations.is_empty(), "{response:#?}");
}

#[test]
fn preserved_io_typing_does_not_invent_flush_effects() {
    assert_uncontracted_method_refused(
        "io",
        "from io import TextIOWrapper\n\ndef run(stream: TextIOWrapper) -> int:\n    stream.flush()\n    return 1\n",
        "flush",
    );
}

#[test]
fn preserved_pathlib_typing_does_not_invent_exists_effects() {
    assert_uncontracted_method_refused(
        "pathlib",
        "from pathlib import Path\n\ndef run(path: Path) -> int:\n    path.exists()\n    return 1\n",
        "exists",
    );
}

#[test]
fn stdlib_typeshed_preservation_does_not_hide_source_owned_shadows() {
    for module in ["io", "pathlib"] {
        let directory = tempfile::tempdir().unwrap();
        let source = format!("import {module}\n\ndef run() -> int:\n    return 1\n");
        let request = request(directory.path(), module, &source);
        fs::write(
            directory.path().join(format!("{module}.py")),
            "raise RuntimeError('application code is not a native contract')\n",
        )
        .unwrap();
        let failure = typecheck_request_sources(
            directory.path(),
            &request.files,
            &request.external_contract_overlays,
        )
        .unwrap_err();
        assert_eq!(
            failure.code,
            "frontend.python.typecheck.overlay-source-conflict"
        );
    }
}
