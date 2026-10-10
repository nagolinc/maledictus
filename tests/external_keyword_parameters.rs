use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, SourceFile,
};
use std::fs;

const CONTRACT: &str = r#"
from nagini_contracts.contracts import Acc, ContractOnly, Ensures, Exsures, Requires, Result

class Handle:
    value: int

    @ContractOnly
    def __init__(self, value: int, /, *, extra: int = 2) -> None:
        Requires(extra >= 0)
        Ensures(Acc(self.value))
        Ensures(self.value == value + extra)
        Exsures(Exception, True)
        ...

    @ContractOnly
    def read(self, factor: int, /, *, adjustment: int = 3) -> int:
        Requires(Acc(self.value))
        Requires(adjustment >= 0)
        Ensures(Acc(self.value))
        Ensures(Result() == factor + adjustment)
        Exsures(Exception, Acc(self.value))
        ...

@ContractOnly
def make(value: int, /, *, extra: int = 2) -> Handle:
    Requires(extra >= 0)
    Ensures(Acc(Result().value))
    Ensures(Result().value == value + extra)
    Exsures(Exception, True)
    ...
"#;

fn verify(native: &str, source: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("native.py"), native).unwrap();
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

fn source(constructor: &str, method: &str, initial: i32, expected: i32) -> String {
    format!(
        "from provider import Handle, make\n\ndef run() -> bool:\n    try:\n        handle = {constructor}\n        initial = handle.value\n        result = {method}\n    except Exception:\n        return False\n    assert initial == {initial}\n    assert result == {expected}\n    return True\n"
    )
}

#[test]
fn native_constructor_and_method_bind_keyword_only_values_and_defaults() {
    for (constructor, method, initial, expected) in [
        ("Handle(4, extra=5)", "handle.read(2, adjustment=7)", 9, 9),
        ("Handle(4)", "handle.read(2)", 6, 5),
        ("Handle(4, extra=5)", "handle.read(2)", 9, 5),
    ] {
        let response = verify(CONTRACT, &source(constructor, method, initial, expected));
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
    }
}

#[test]
fn native_factory_binds_keyword_only_values_and_defaults() {
    for (constructor, initial) in [("make(4, extra=5)", 9), ("make(4)", 6)] {
        let response = verify(CONTRACT, &source(constructor, "handle.read(2)", initial, 5));
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
    }
}

#[test]
fn required_keyword_only_argument_is_bound() {
    let contract = CONTRACT
        .replace("extra: int = 2", "extra: int")
        .replace("adjustment: int = 3", "adjustment: int");
    let response = verify(
        &contract,
        &source("Handle(4, extra=5)", "handle.read(2, adjustment=7)", 9, 9),
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
}

#[test]
fn keyword_arguments_preserve_precondition_and_postcondition_checks() {
    for (constructor, method, initial, expected, obligation) in [
        (
            "Handle(4, extra=-5)",
            "handle.read(2)",
            -1,
            5,
            "constructor-precondition",
        ),
        (
            "Handle(4)",
            "handle.read(2, adjustment=-7)",
            6,
            -5,
            "call-precondition:read",
        ),
        (
            "make(4, extra=-5)",
            "handle.read(2)",
            -1,
            5,
            "constructor-precondition",
        ),
        (
            "Handle(4, extra=5)",
            "handle.read(2, adjustment=7)",
            9,
            10,
            "assert",
        ),
    ] {
        let response = verify(CONTRACT, &source(constructor, method, initial, expected));
        assert!(
            matches!(response.status, ProofStatus::Refuted),
            "{response:#?}"
        );
        assert!(
            response
                .obligations
                .iter()
                .any(|o| o.id.contains(obligation) && o.counterexample.is_some()),
            "{response:#?}"
        );
    }
}

#[test]
fn invalid_positional_keyword_and_missing_arguments_still_refuse() {
    let required = CONTRACT
        .replace("extra: int = 2", "extra: int")
        .replace("adjustment: int = 3", "adjustment: int");
    for (contract, constructor, method) in [
        (CONTRACT, "Handle(4, 5)", "handle.read(2)"),
        (CONTRACT, "Handle(value=4)", "handle.read(2)"),
        (CONTRACT, "Handle(4)", "handle.read(2, 7)"),
        (CONTRACT, "Handle(4)", "handle.read(factor=2)"),
        (CONTRACT, "make(4, 5)", "handle.read(2)"),
        (
            required.as_str(),
            "Handle(4)",
            "handle.read(2, adjustment=3)",
        ),
        (required.as_str(), "Handle(4, extra=2)", "handle.read(2)"),
    ] {
        let response = verify(contract, &source(constructor, method, 6, 5));
        assert!(
            !matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
    }
}

#[test]
fn owned_constructor_uses_the_same_keyword_binding_rules() {
    use maledictus::python_heap_contracts::verify_heap_module;
    let source = r#"
from nagini_contracts.contracts import Acc, Ensures

class Local:
    value: int

    def __init__(self, *, value: int = 3) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == value)
        self.value = value

def run() -> None:
    explicit = Local(value=7)
    default = Local()
    assert explicit.value == 7
    assert default.value == 3
"#;
    let checked = verify_heap_module(source, "owned_constructor.py", &[]).unwrap();
    assert!(checked.passed, "{checked:#?}");
    let invalid = source.replace("Local(value=7)", "Local(7)");
    match verify_heap_module(&invalid, "invalid_owned_constructor.py", &[]) {
        Ok(checked) => assert!(!checked.passed, "{checked:#?}"),
        Err(error) => assert!(error.code.contains("call"), "{error:#?}"),
    }
}

#[test]
fn native_timeout_optional_default_and_unmodeled_numeric_values_are_distinguished() {
    let contract = r#"
from nagini_contracts.contracts import ContractOnly, Exsures

class Timeout:
    @ContractOnly
    def __init__(self, timeout: float | None, *, connect: float | None = None) -> None:
        Exsures(Exception, True)
        ...
"#;
    for call in [
        "Timeout(180.0, connect=10.0)",
        "Timeout(None)",
        "Timeout(180, connect=10)",
    ] {
        let source = format!(
            "from provider import Timeout\n\ndef run() -> bool:\n    try:\n        timeout = {call}\n    except Exception:\n        return False\n    return True\n"
        );
        let response = verify(contract, &source);
        if call == "Timeout(None)" {
            assert!(
                matches!(response.status, ProofStatus::Proved),
                "{response:#?}"
            );
        } else {
            // Keyword binding must not silently add semantics for float
            // expressions or int-to-float conversion. These remain a separate
            // application-proof obligation, rather than an erased native type.
            assert!(
                matches!(response.status, ProofStatus::Refused),
                "{response:#?}"
            );
            assert!(
                response
                    .diagnostics
                    .iter()
                    .any(|d| d.code.contains("expression-unsupported")
                        || d.code.contains("argument-type")),
                "{response:#?}"
            );
        }
    }
}
