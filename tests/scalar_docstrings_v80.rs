use std::fs;

use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofStatus,
    SourceFile,
};
use maledictus::python_contracts::verify_contract_module;

fn issue(source: &str) -> maledictus::protocol::ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("module.py"), source).unwrap();
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "module.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["choose".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

#[test]
fn public_issuance_proves_module_function_and_standalone_string_literals_inert() {
    let response = issue(
        "\"\"\"module documentation\"\"\"\nfrom nagini_contracts.contracts import Ensures, Requires, Result\n\ndef choose(flag: bool) -> int:\n    \"\"\"function documentation\"\"\"\n    Requires(flag)\n    Ensures(Result() == 1)\n    value = 1\n    \"an inert standalone literal\"\n    return value\n",
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
}

#[test]
fn a_nonleading_string_does_not_reclassify_a_late_contract_as_a_specification() {
    let error = verify_contract_module(
        "from nagini_contracts.contracts import *\n\ndef choose() -> int:\n    value = 1\n    \"not a docstring\"\n    Requires(value == 1)\n    return value\n",
        "late_contract_after_string.py",
        &["choose".to_owned()],
    )
    .unwrap_err();

    assert_eq!(error.code, "frontend.python.contracts.late-contract");
}

#[test]
fn arbitrary_expression_statements_do_not_gain_docstring_semantics() {
    let error = verify_contract_module(
        "def choose() -> int:\n    42\n    return 1\n",
        "not_a_docstring.py",
        &["choose".to_owned()],
    )
    .unwrap_err();

    assert_eq!(
        error.code,
        "frontend.python.contracts.statement-unsupported"
    );
}

#[test]
fn transitive_source_modules_preserve_docstring_semantics() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "\"\"\"provider documentation\"\"\"\nfrom nagini_contracts.contracts import Ensures\n\ndef choose(value: int) -> int:\n    \"\"\"provider function documentation\"\"\"\n    Ensures(int, lambda returned: returned == value)\n    return value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "\"\"\"application documentation\"\"\"\nfrom nagini_contracts.contracts import Ensures, Result\nfrom provider import choose\n\ndef run() -> int:\n    \"\"\"entry function documentation\"\"\"\n    Ensures(Result() == 1)\n    return choose(1)\n",
    )
    .unwrap();

    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["choose".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("transitive-source-scalar-contracts/v33")
    );
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
}

#[test]
fn checked_external_stubs_and_adapters_preserve_docstring_semantics() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "\"\"\"adapter documentation\"\"\"\nfrom nagini_contracts.contracts import Ensures, Result\nfrom provider import choose\n\ndef run() -> int:\n    \"\"\"adapter function documentation\"\"\"\n    Ensures(Result() == 1)\n    return choose()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "\"\"\"external contract documentation\"\"\"\nfrom nagini_contracts.contracts import ContractOnly, Ensures, Result\n\n@ContractOnly\ndef choose() -> int:\n    \"\"\"external function documentation\"\"\"\n    Ensures(Result() == 1)\n    ...\n",
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
            symbols: vec!["run".to_owned()],
        }],
        external_contract_overlays: vec![ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: ExternalExceptionPolicy::AssumeNoException,
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("checked-external-scalar-contracts/v26")
    );
}
