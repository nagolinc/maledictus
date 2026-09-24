use std::fs;
use std::path::PathBuf;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};
use maledictus::python_contracts::verify_contract_module;

fn upstream() -> (PathBuf, PathBuf) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    (
        root.join(".upstream/nagini"),
        root.join("conformance/nagini-v1.3.1.json"),
    )
}

fn verify_issuance(source: &str) -> maledictus::protocol::ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("identity_program.py"), source).unwrap();
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "identity_program.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

#[test]
fn pinned_identity_fixtures_match_exactly() {
    let (suite, pin) = upstream();
    for fixture in [
        "tests/functional/verification/test_identity.py",
        "tests/functional/verification/issues/00282.py",
    ] {
        let result = check_pinned_scalar_fixture(&suite, &pin, fixture).unwrap();
        assert!(result.passed, "{fixture}: {result:#?}");
    }
}

#[test]
fn production_proves_only_source_known_identity_relations() {
    let result = verify_contract_module(
        "def run() -> None:\n    empty = ()\n    empty_alias = empty\n    assert empty is empty_alias\n    first = (1,)\n    second = (1,)\n    assert first is not second\n    left = range(0, 2)\n    right = range(0, 2)\n    assert left is not right\n",
        "known_identity.py",
        &[],
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
}

#[test]
fn implementation_dependent_string_identity_is_an_unproved_obligation() {
    let result = verify_contract_module(
        "def run() -> None:\n    prefix = 'a'\n    combined = prefix + 'b'\n    assert combined is not 'ab'\n",
        "uncertain_string_identity.py",
        &[],
    )
    .unwrap();
    assert!(!result.passed, "{result:#?}");
    assert_eq!(
        result
            .obligations
            .iter()
            .filter(|item| !item.satisfied())
            .count(),
        1
    );
}

#[test]
fn unknown_identity_and_shadowed_constructors_fail_closed() {
    for source in [
        "def compare(left: str, right: str) -> None:\n    assert left is right\n",
        "def str(value: int) -> str:\n    return 'shadowed'\n\ntext = str(1)\n",
        "def run(range: int) -> None:\n    value = range(1)\n",
    ] {
        assert!(
            verify_contract_module(source, "identity_boundary.py", &[]).is_err(),
            "unexpectedly accepted:\n{source}"
        );
    }
}

#[test]
fn public_issuance_runs_strict_typecheck_before_identity_proof() {
    let response = verify_issuance(
        "def run() -> None:\n    value = ()\n    alias = value\n    assert value is alias\n",
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(response.verifier_identity.is_some(), "{response:#?}");
}
