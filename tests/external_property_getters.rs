use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, SourceFile,
};
use std::fs;

const CONTRACT: &str = r#"
from nagini_contracts.contracts import Acc, ContractOnly, Ensures, Exsures, Requires, Result

class ReadError(Exception):
    pass

class Handle:
    state: int

    @ContractOnly
    def __init__(self, value: int) -> None:
        Ensures(Acc(self.state))
        Ensures(self.state == value)
        Exsures(Exception, True)
        ...

    @property
    @ContractOnly
    def value(self) -> int:
        Requires(Acc(self.state))
        Ensures(Acc(self.state))
        Ensures(Result() == 7)
        Exsures(ReadError, Acc(self.state))
        ...

    @property
    @ContractOnly
    def ready(self) -> bool:
        Requires(Acc(self.state))
        Ensures(Acc(self.state))
        Ensures(Result())
        Exsures(ReadError, Acc(self.state))
        ...
"#;

fn verify(contract: &str, source: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("native.py"), contract).unwrap();
    fs::write(directory.path().join("app.py"), source).unwrap();
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
            stub_path: "native.py".to_owned(),
            exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
        }],
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    })
}

const SOURCE: &str = r#"from provider import Handle

def run() -> bool:
    try:
        handle = Handle(4)
        result = handle.value
    except Exception:
        return False
    assert result == 7
    return True
"#;

#[test]
fn native_getter_composes_value_permissions_exceptions_and_sealed_metadata() {
    let response = verify(CONTRACT, SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(
        response.external_contracts.iter().any(|contract| {
            contract.functions.contains(&"Handle.value".to_owned())
                && contract
                    .declared_exceptions
                    .contains(&"provider.ReadError".to_owned())
        }),
        "{response:#?}"
    );
}

#[test]
fn getter_cannot_launder_false_postconditions_or_preserved_field_values() {
    for source in [
        SOURCE.replace("result == 7", "result == 8"),
        SOURCE.replace("assert result == 7", "assert handle.state == 4"),
    ] {
        let response = verify(CONTRACT, &source);
        assert!(
            matches!(response.status, ProofStatus::Refuted),
            "{response:#?}"
        );
        assert!(
            response
                .obligations
                .iter()
                .any(|obligation| obligation.id.contains("assert")
                    && obligation.counterexample.is_some()),
            "{response:#?}"
        );
    }
}

#[test]
fn uncaught_getter_exception_cannot_be_treated_as_a_field_read() {
    let source = r#"from provider import Handle

def run() -> bool:
    try:
        handle = Handle(4)
    except Exception:
        return False
    result = handle.value
    return True
"#;
    let response = verify(CONTRACT, source);
    assert!(
        !matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|obligation| obligation
            .id
            .contains("exception-undeclared:provider.ReadError")
            && obligation.counterexample.is_some()),
        "{response:#?}"
    );
}

#[test]
fn bool_property_return_condition_and_short_circuit_preserve_exception_paths() {
    for body in [
        "return handle.ready",
        "if handle.ready:\n            return True\n        return False",
        "if not handle.ready:\n            return False\n        return True",
        "return False and handle.ready",
    ] {
        let source = format!(
            "from provider import Handle\n\ndef run() -> bool:\n    try:\n        handle = Handle(4)\n        {body}\n    except Exception:\n        return False\n"
        );
        let response = verify(CONTRACT, &source);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{body}: {response:#?}"
        );
    }
}

#[test]
fn getter_binding_collisions_unsupported_signatures_and_method_syntax_refuse() {
    for contract in [
        CONTRACT.replace("def value(self)", "def value(self, *, extra: int = 0)"),
        CONTRACT.replace("state: int", "state: int\n    value: int"),
        CONTRACT.replace(
            "@property\n    @ContractOnly",
            "@ContractOnly\n    @property",
        ),
    ] {
        let response = verify(&contract, SOURCE);
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{response:#?}"
        );
    }
    let response = verify(
        CONTRACT,
        &SOURCE.replace("result = handle.value", "result = handle.value()"),
    );
    assert!(
        !matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
}

#[test]
fn getter_cannot_invent_required_permission() {
    let contract = CONTRACT
        .replacen("Ensures(Acc(self.state))", "Ensures(True)", 1)
        .replacen("Ensures(self.state == value)", "Ensures(True)", 1);
    let response = verify(&contract, SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|obligation| obligation
            .id
            .contains("method-call-precondition")
            && obligation.counterexample.is_some()),
        "{response:#?}"
    );
}

#[test]
fn getter_preserves_returned_heap_type_and_transfers_result_permissions() {
    let contract = CONTRACT.replace(
        "class Handle:",
        "class Child:\n    code: int\n\nclass Handle:",
    ) + r#"

    @property
    @ContractOnly
    def child(self) -> Child:
        Requires(Acc(self.state))
        Ensures(Acc(self.state))
        Ensures(Acc(Result().code))
        Ensures(Result().code == 9)
        Exsures(ReadError, Acc(self.state))
        ...
"#;
    let source = SOURCE
        .replace(
            "result = handle.value",
            "child = handle.child\n        result = child.code",
        )
        .replace("result == 7", "result == 9");
    let response = verify(&contract, &source);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let response = verify(&contract, &source.replace("result == 9", "result == 8"));
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}

#[test]
fn short_circuit_skips_a_getter_with_an_uncaught_exception() {
    let source = r#"from provider import Handle

def run() -> bool:
    try:
        handle = Handle(4)
    except Exception:
        return False
    return False and handle.ready
"#;
    let response = verify(CONTRACT, source);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let response = verify(
        CONTRACT,
        &source.replace("False and handle.ready", "True and handle.ready"),
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|obligation| obligation
            .id
            .contains("exception-undeclared:provider.ReadError")
            && obligation.counterexample.is_some()),
        "{response:#?}"
    );
}

#[test]
fn unsupported_getter_expression_positions_do_not_drop_exceptions() {
    for body in [
        "handle.value\n    return True",
        "result: int = handle.value\n    return True",
        "return handle.value == 7",
        "result = (handle.value, 1)\n    return True",
    ] {
        let source = format!(
            "from provider import Handle\n\ndef run() -> bool:\n    try:\n        handle = Handle(4)\n    except Exception:\n        return False\n    {body}\n"
        );
        let response = verify(CONTRACT, &source);
        assert!(
            !matches!(response.status, ProofStatus::Proved),
            "{body}: {response:#?}"
        );
    }
}
