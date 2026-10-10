use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, SourceFile,
};
use std::fs;

const HEAP: &str = r#"from nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Result

class Reader:
    @ContractOnly
    def read(self) -> int:
        Ensures(Result() == 5)
        Exsures(Exception, True)
        ...

@ContractOnly
def open_reader() -> Reader:
    Exsures(Exception, True)
    ...
"#;

const SCALAR: &str = r#"from nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Result

@ContractOnly
def stamp() -> int:
    Ensures(Result() == 7)
    Exsures(Exception, True)
    ...
"#;

const SOURCE: &str = r#"from native_heap import open_reader
from native_scalar import stamp

def run() -> int:
    try:
        reader = open_reader()
        first = reader.read()
        second = stamp()
    except Exception:
        return 0
    assert first == 5
    assert second == 7
    return first + second
"#;

fn verify(heap: &str, scalar: &str, source: &str, helper: Option<&str>) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("heap_contract.py"), heap).unwrap();
    fs::write(directory.path().join("scalar_contract.py"), scalar).unwrap();
    fs::write(directory.path().join("app.py"), source).unwrap();
    let mut files = vec![SourceFile {
        path: "app.py".to_owned(),
        language: "python".to_owned(),
        symbols: vec!["run".to_owned()],
    }];
    if let Some(helper) = helper {
        fs::write(directory.path().join("helper.py"), helper).unwrap();
        files.push(SourceFile {
            path: "helper.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec![],
        });
    }
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files,
        external_contract_overlays: [
            ("native_heap", "heap_contract.py"),
            ("native_scalar", "scalar_contract.py"),
        ]
        .into_iter()
        .map(|(module, stub_path)| ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: module.to_owned(),
            stub_path: stub_path.to_owned(),
            exception_policy: if module == "native_scalar" && !scalar.contains("Exsures(") {
                ExternalExceptionPolicy::AssumeNoException
            } else {
                ExternalExceptionPolicy::DeclaredByExsures
            },
        })
        .collect(),
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    })
}

#[test]
fn one_adapter_composes_scalar_and_heap_native_calls() {
    let response = verify(HEAP, SCALAR, SOURCE, None);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(response.external_contracts.len(), 2);
    for module in ["native_heap", "native_scalar"] {
        assert!(
            response
                .external_contracts
                .iter()
                .any(|c| c.module == module && !c.declared_exceptions.is_empty())
        );
    }
}

#[test]
fn mixed_adapters_preserve_both_providers_postconditions() {
    for (before, after) in [("first == 5", "first == 6"), ("second == 7", "second == 8")] {
        let response = verify(HEAP, SCALAR, &SOURCE.replace(before, after), None);
        assert!(
            matches!(response.status, ProofStatus::Refuted),
            "{response:#?}"
        );
        assert!(
            response
                .obligations
                .iter()
                .any(|o| o.counterexample.is_some())
        );
    }
}

#[test]
fn mixed_adapters_preserve_every_declared_exception() {
    let factory = SOURCE.replace(
        "    try:\n        reader = open_reader()",
        "    reader = open_reader()\n    try:",
    );
    let method = SOURCE
        .replace("        first = reader.read()\n", "")
        .replace(
            "    assert first == 5",
            "    first = reader.read()\n    assert first == 5",
        );
    let scalar = SOURCE.replace("        second = stamp()\n", "").replace(
        "    assert first == 5",
        "    second = stamp()\n    assert first == 5",
    );
    for (stage, source) in [("factory", factory), ("method", method), ("scalar", scalar)] {
        let response = verify(HEAP, SCALAR, &source, None);
        assert!(
            matches!(response.status, ProofStatus::Refuted),
            "{stage}: {response:#?}"
        );
        assert!(
            response
                .obligations
                .iter()
                .any(|o| o.id.contains("exception-undeclared") && o.counterexample.is_some())
        );
    }
}

#[test]
fn mixed_adapter_checks_owned_helper_body_in_same_request() {
    let helper = "def plus_one(value: int) -> int:\n    return value + 1\n";
    let source = SOURCE
        .replace(
            "from native_scalar import stamp",
            "from native_scalar import stamp\nfrom helper import plus_one",
        )
        .replace(
            "return first + second",
            "third = plus_one(second)\n    assert third == 8\n    return first + third",
        );
    let response = verify(HEAP, SCALAR, &source, Some(helper));
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(
        response
            .source_imports
            .iter()
            .any(|edge| edge.provider_path == "helper.py")
    );
    let response = verify(
        HEAP,
        SCALAR,
        &source,
        Some(&helper.replace("value + 1", "value + 2")),
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}

#[test]
fn mixed_adapter_cannot_invent_native_heap_permissions() {
    let heap = HEAP.replace("class Reader:", "class Reader:\n    secret: int");
    let source = SOURCE.replace("return first + second", "return reader.secret");
    let response = verify(&heap, SCALAR, &source, None);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|o| o.id.contains("permission") && o.counterexample.is_some())
    );
}

#[test]
fn impossible_normal_postcondition_does_not_erase_scalar_exception() {
    let scalar = SCALAR.replace("Ensures(Result() == 7)", "Ensures(False)");
    let source = SOURCE.replace("        second = stamp()\n", "").replace(
        "    assert first == 5",
        "    second = stamp()\n    assert first == 5",
    );
    let response = verify(HEAP, &scalar, &source, None);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|o| o.id.contains("exception-undeclared") && o.counterexample.is_some())
    );
}

#[test]
fn impossible_normal_postcondition_does_not_erase_failed_precondition() {
    let scalar = SCALAR
        .replace("ContractOnly, Ensures", "ContractOnly, Requires, Ensures")
        .replace(
            "Ensures(Result() == 7)",
            "Requires(False)\n    Ensures(False)",
        );
    let response = verify(HEAP, &scalar, SOURCE, None);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|o| o.id.contains("precondition") && o.counterexample.is_some())
    );
}

#[test]
fn normal_only_scalar_provider_keeps_its_postcondition() {
    let scalar = SCALAR.replace("    Exsures(Exception, True)\n", "");
    let response = verify(HEAP, &scalar, SOURCE, None);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let response = verify(
        HEAP,
        &scalar,
        &SOURCE.replace("second == 7", "second == 8"),
        None,
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}
