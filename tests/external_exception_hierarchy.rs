use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofStatus,
    SourceFile,
};
use maledictus::python_heap_contracts::parse_external_heap_contract_module;
use std::fs;

fn verify_handler(raised: &str, caught: &str) -> maledictus::protocol::ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        format!(
            r#"
from nagini_contracts.contracts import ContractOnly, Exsures

class HTTPError(Exception):
    pass

class TransportError(HTTPError):
    pass

class TimeoutError(TransportError):
    pass

class ProtocolError(HTTPError):
    pass

class Client:
    @ContractOnly
    def read(self) -> int:
        Exsures({raised}, True)
        ...
"#
        ),
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        format!(
            r#"
from provider import Client, HTTPError, TransportError, TimeoutError, ProtocolError

def run(client: Client) -> bool:
    try:
        client.read()
        return True
    except {caught}:
        return False
"#
        ),
    )
    .unwrap();
    maledictus::verify(&ProofRequest {
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
            exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
        }],
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    })
}

#[test]
fn ancestor_handler_catches_native_descendant_and_seals_hierarchy() {
    let response = verify_handler("TimeoutError", "HTTPError");
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(
        response.external_contracts[0]
            .declared_exceptions
            .contains(&"provider.TimeoutError".to_owned()),
        "{response:#?}"
    );
}

#[test]
fn sibling_handler_does_not_hide_a_native_exception() {
    let response = verify_handler("TimeoutError", "ProtocolError");
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|o| o
            .id
            .contains("exception-undeclared:provider.TimeoutError")
            && o.counterexample.is_some()),
        "{response:#?}"
    );
}

#[test]
fn descendant_handler_does_not_hide_a_base_exception() {
    let response = verify_handler("HTTPError", "TransportError");
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|o| o.id.contains("exception-undeclared:provider.HTTPError")
                && o.counterexample.is_some()),
        "{response:#?}"
    );
}

#[test]
fn passive_subclass_exports_exception_identity_without_becoming_a_value_class() {
    let parsed = parse_external_heap_contract_module(
        "class Parent(Exception):\n    code: int\n\nclass Child(Parent):\n    detail: str\n",
        "contract.py",
        "provider",
    )
    .unwrap();
    assert_eq!(parsed.exception_type_names(), ["Child", "Parent"]);
    assert!(parsed.qualified_class_names().is_empty());
}

#[test]
fn unsupported_ancestry_and_field_overrides_remain_refused() {
    for source in [
        "class Parent:\n    pass\n\nclass Child(Parent):\n    pass\n",
        "class Child(Parent):\n    pass\n\nclass Parent(Exception):\n    pass\n",
        "class Parent(Child):\n    pass\n\nclass Child(Parent):\n    pass\n",
        "class Parent(Exception):\n    code: int\n\nclass Child(Parent):\n    code: str\n",
        "class Parent(Exception):\n    pass\n\nclass Child(Parent):\n    def changed(self) -> None:\n        pass\n",
    ] {
        assert!(
            parse_external_heap_contract_module(source, "contract.py", "provider").is_err(),
            "{source}"
        );
    }
}
