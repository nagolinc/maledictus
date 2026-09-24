use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

const OPERATOR_FIXTURE: &str = "tests/functional/verification/test_operator_overloading.py";

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it was refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refusal(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("expected source to fail closed before proof issuance")
}

#[test]
fn exact_source_binary_dunders_preserve_values_permissions_and_fresh_rebinding() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Number:
    def __init__(self, value: int) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == value)
        self.value = value

    def __add__(self, other: 'Number') -> 'Number':
        Requires(Acc(self.value, 1 / 10))
        Requires(Acc(other.value, 1 / 10))
        Ensures(Acc(self.value, 1 / 10))
        Ensures(Acc(other.value, 1 / 10))
        Ensures(Acc(Result().value))
        Ensures(Result().value == self.value + other.value)
        result = Number(self.value + other.value)
        return result

    @Pure
    def __mul__(self, other: 'Number') -> int:
        Requires(Acc(self.value, 1 / 10))
        Requires(Acc(other.value, 1 / 10))
        return self.value * other.value

def run() -> None:
    left = Number(2)
    right = Number(3)
    total = left + right
    assert total.value == 5
    assert left * right == 6
    total += right
    assert total.value == 8
"#,
        "binary_dunder_values.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn open_or_mixed_runtime_classes_do_not_claim_python_binary_dispatch() {
    let open = refusal(
        r#"from nagini_contracts.contracts import *
class Number:
    def __add__(self, other: 'Number') -> 'Number':
        return self
def run(left: Number, right: Number) -> None:
    result = left + right
"#,
        "binary_dunder_open_runtime.py",
    );
    assert_eq!(
        open.code,
        "frontend.python.heap.binary-operator-dispatch-unsupported"
    );

    let mixed = refusal(
        r#"from nagini_contracts.contracts import *
class Left:
    def __add__(self, other: 'Left') -> 'Left':
        return self
class Right:
    def __radd__(self, other: Left) -> Left:
        return other
def run() -> None:
    left = Left()
    right = Right()
    result = left + right
"#,
        "binary_dunder_reflected_dispatch.py",
    );
    assert_eq!(
        mixed.code,
        "frontend.python.heap.binary-operator-dispatch-unsupported"
    );
}

#[test]
fn augmented_fallback_refuses_iadd_and_nonfresh_binary_results() {
    let inplace = refusal(
        r#"from nagini_contracts.contracts import *
class Number:
    def __add__(self, other: 'Number') -> 'Number':
        return self
    def __iadd__(self, other: 'Number') -> 'Number':
        return self
def run() -> None:
    left = Number()
    right = Number()
    left += right
"#,
        "binary_dunder_iadd_present.py",
    );
    assert_eq!(
        inplace.code,
        "frontend.python.heap.inplace-operator-dispatch-unsupported"
    );

    let nonfresh = refusal(
        r#"from nagini_contracts.contracts import *
class Number:
    def __add__(self, other: 'Number') -> 'Number':
        return self
def run() -> None:
    left = Number()
    right = Number()
    left += right
"#,
        "binary_dunder_nonfresh_fallback.py",
    );
    assert_eq!(
        nonfresh.code,
        "frontend.python.heap.inplace-operator-result-unsupported"
    );
}

#[test]
fn exact_operator_fixture_is_a_combined_heap_gain() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let heap = check_pinned_heap_fixture(&suite, &pin, OPERATOR_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {OPERATOR_FIXTURE}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.actual, heap.expected, "{heap:#?}");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, OPERATOR_FIXTURE)
        .expect_err("source classes remain outside the scalar backend");
    assert!(
        scalar.contains("frontend.python.contracts.module-statement-unsupported"),
        "{scalar}"
    );

    let reference = check_pinned_reference_fixture(&suite, &pin, OPERATOR_FIXTURE)
        .expect_err("behavioral source classes remain outside the reference backend");
    assert!(
        reference.contains("frontend.python.references.class-unsupported"),
        "{reference}"
    );
}
