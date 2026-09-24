use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refusal(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("unsupported string semantics must refuse before proof issuance")
}

#[test]
fn strings_are_source_typed_values_with_exact_literal_concat_length_and_equality() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

@Pure
def suffix(value: str, ending: str = "!") -> str:
    Ensures(Result() == value + ending)
    return value + ending

def run() -> None:
    message: str = suffix("go")
    assert message == "go!"
    assert len(message) == 3
    assert message != "stop"
"#,
        "v62_string_values.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":assert:"))
            .count(),
        3,
        "{verification:#?}"
    );
}

#[test]
fn string_fields_are_checked_at_constructor_and_write_boundaries() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Message:
    text: str

    def __init__(self, text: str) -> None:
        Ensures(Acc(self.text))
        Ensures(self.text == text)
        self.text = text

def run() -> None:
    message = Message("ready")
    assert message.text == "ready"
    message.text = "done"
    assert message.text == "done"
"#,
        "v62_string_fields.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn module_and_function_docstrings_are_inert_string_expressions() {
    let verification = verify(
        r#""""module documentation"""

def run() -> None:
    """function documentation"""
    message: str = "ready"
    assert message == "ready"
"#,
        "v62_string_docstrings.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn unsupported_string_identity_indexing_and_mixed_addition_fail_closed() {
    let identity = refusal(
        "def run(value: str) -> None:\n    assert value is 'x'\n",
        "v62_string_identity.py",
    );
    assert_eq!(
        identity.code, "frontend.python.heap.string-identity-unsupported",
        "{identity:#?}"
    );

    let indexing = refusal(
        "def run(value: str) -> None:\n    first = value[0]\n",
        "v62_string_indexing.py",
    );
    assert_eq!(
        indexing.code, "frontend.python.heap.subscript-type-unsupported",
        "{indexing:#?}"
    );

    let mixed = refusal(
        "def run(value: str) -> str:\n    return value + 1\n",
        "v62_string_mixed_addition.py",
    );
    assert_eq!(
        mixed.code, "frontend.python.heap.arithmetic-type-mismatch",
        "{mixed:#?}"
    );
}
