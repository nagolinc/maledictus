use std::fs;

use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};

fn verify_packaged_operation(
    initializer: &str,
    returned: &str,
) -> maledictus::protocol::ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::create_dir(directory.path().join("application")).unwrap();
    fs::write(
        directory.path().join("application/__init__.py"),
        initializer,
    )
    .unwrap();
    fs::write(
        directory.path().join("application/worker.py"),
        format!(
            r#"from dataclasses import dataclass
from dagcert.runtime import operation

@dataclass(frozen=True)
class Request:
    enabled: bool
    value: int

@dataclass(frozen=True)
class Ready:
    value: int

@dataclass(frozen=True)
class Idle:
    reason: str

@operation
def run(request: Request) -> Ready | Idle:
    if not request.enabled:
        return Idle('disabled')
    return {returned}
"#
        ),
    )
    .unwrap();
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "application/worker.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
            SourceFile {
                path: "application/__init__.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec![],
            },
        ],
        external_contract_overlays: vec![],
        cross_language_bindings: vec![],
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
    })
}

#[test]
fn packaged_operation_root_uses_closed_operation_checker() {
    let response = verify_packaged_operation(
        "\"\"\"Application package.\"\"\"\n",
        "Ready(request.value + 1)",
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let root = response
        .files
        .iter()
        .find(|file| file.path == "application/worker.py")
        .unwrap();
    assert_eq!(
        root.fragment.as_deref(),
        Some("dagcert-closed-typed-operations/v4")
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn packaged_operation_wrong_outcome_still_fails() {
    let response = verify_packaged_operation("", "Ready('wrong type')");
    assert!(
        !matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(!response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn packaged_operation_partial_arithmetic_still_fails() {
    let response = verify_packaged_operation("", "Ready(1 // request.value)");
    assert!(
        !matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(!response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn packaged_operation_cannot_hide_failing_package_initializer() {
    let response = verify_packaged_operation(
        "raise RuntimeError('initialization failed')\n",
        "Ready(request.value + 1)",
    );
    assert!(
        !matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(!response.diagnostics.is_empty(), "{response:#?}");
}
