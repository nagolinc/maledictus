use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};
use maledictus::python_contracts::{
    verify_and_export_source_contract_module, verify_contract_module,
};
use std::fs;

#[test]
fn public_issuance_typechecks_and_proves_entry_module_metadata() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "saved = __file__\nassert __name__ == '__main__'\nassert saved == __file__\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert_eq!(response.obligations.len(), 2);
}

#[test]
fn exact_upstream_entry_module_metadata_fixture_matches() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/verification/test_builtin_globals_1.py";
    let result = check_pinned_scalar_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap_or_else(|error| panic!("scalar {fixture} was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual, "{result:#?}");
}

#[test]
fn entry_module_metadata_is_real_and_available_to_module_assertions() {
    let verification = verify_contract_module(
        "saved = __file__\nassert __name__ == '__main__'\nassert saved == __file__\n",
        "entry.py",
        &[],
    )
    .expect("entry-module metadata should lower without an assumed contract");

    assert!(verification.passed, "{verification:#?}");
    assert_eq!(verification.obligations.len(), 2);
    assert!(
        verification
            .obligations
            .iter()
            .all(maledictus::vc::ObligationResult::satisfied)
    );
}

#[test]
fn imported_module_metadata_uses_the_canonical_module_name_and_source_path() {
    let (verification, _) = verify_and_export_source_contract_module(
        "assert __name__ == 'resources.provider'\nassert __file__ == 'resources/provider.py'\n",
        "resources/provider.py",
        "resources.provider",
        &[],
    )
    .expect("source-owned provider metadata should be verified before export");

    assert!(verification.passed, "{verification:#?}");
    assert_eq!(verification.obligations.len(), 2);
}

#[test]
fn metadata_only_star_import_executes_provider_without_leaking_its_metadata() {
    let (_, provider) = verify_and_export_source_contract_module(
        "assert __name__ == 'resources.provider'\nassert __file__ == 'resources/provider.py'\n",
        "resources/provider.py",
        "resources.provider",
        &[],
    )
    .expect("the metadata-only provider must execute before it can be imported");

    let verification = maledictus::python_contracts::verify_contract_module_with_imports(
        "from resources.provider import *\nassert __name__ == '__main__'\nassert __file__ == 'entry.py'\n",
        "entry.py",
        &[],
        &[provider],
    )
    .expect("a star import with no public exports should still preserve entry metadata");

    assert!(verification.passed, "{verification:#?}");
    assert_eq!(verification.obligations.len(), 2);
}

#[test]
fn writes_to_interpreter_module_metadata_are_refuted_not_applied() {
    for source in [
        "__name__ = 'provider'\n",
        "__file__: str = 'other.py'\n",
        "__file__ += '.bak'\n",
    ] {
        let verification = verify_contract_module(source, "entry.py", &[])
            .expect("a protected metadata write is a verification result, not a frontend crash");
        assert!(!verification.passed, "{source}\n{verification:#?}");
        let failure = verification
            .obligations
            .iter()
            .find(|obligation| !obligation.satisfied())
            .expect("the protected write must emit one failing obligation");
        assert!(
            failure.id.contains(":field-write-permission:"),
            "{source}\n{failure:#?}"
        );
    }
}

#[test]
fn module_assertions_are_real_proof_obligations() {
    let verification =
        verify_contract_module("assert __name__ == 'resources.provider'\n", "entry.py", &[])
            .expect("false module assertions should be refuted by the solver");

    assert!(!verification.passed, "{verification:#?}");
    assert_eq!(verification.obligations.len(), 1);
    assert!(!verification.obligations[0].satisfied());
    assert_eq!(verification.obligations[0].line, 1);
}
