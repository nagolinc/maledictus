use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_heap_contracts::verify_heap_module;

const INPLACE_FIXTURE: &str = "tests/functional/verification/test_inplace_operators.py";

#[test]
fn primitive_local_augmented_arithmetic_rebinds_in_source_order() {
    let verification = verify_heap_module(
        "def run() -> None:\n    value = 42\n    value += 42\n    assert value == 84\n    value -= 42\n    assert value == 42\n    value *= 2\n    assert value == 84\n",
        "primitive_local_augassign.py",
        &[],
    )
    .expect("primitive local augmented arithmetic should lower");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn explicit_inplace_dispatch_requires_a_proved_receiver_result() {
    let source = r#"
from nagini_contracts.contracts import *

class Counter:
    def __init__(self, value: int) -> None:
        self.value = value
        Ensures(Acc(self.value))
        Ensures(self.value == value)

    def __iadd__(self, other: 'Counter') -> 'Counter':
        Requires(Acc(self.value) and Acc(other.value, 1/2))
        Ensures(Acc(self.value) and Acc(other.value, 1/2))
        self.value += other.value
        return self

def run() -> None:
    left = Counter(1)
    right = Counter(2)
    left += right
"#;
    let failure = verify_heap_module(source, "missing_inplace_identity.py", &[])
        .expect_err("an explicit in-place method without Result() is self must be refused");
    assert_eq!(
        failure.code,
        "frontend.python.heap.inplace-operator-result-unsupported"
    );
}

#[test]
fn dynamic_inplace_rhs_is_not_silently_evaluated() {
    let source = r#"
from nagini_contracts.contracts import *

class Counter:
    def __init__(self, value: int) -> None:
        self.value = value
        Ensures(Acc(self.value))

    def __iadd__(self, other: 'Counter') -> 'Counter':
        Requires(Acc(self.value) and Acc(other.value, 1/2))
        Ensures(Acc(self.value) and Acc(other.value, 1/2))
        Ensures(Result() is self)
        self.value += other.value
        return self

def run() -> None:
    left = Counter(1)
    right = Counter(2)
    left += right if True else left
"#;
    let failure = verify_heap_module(source, "dynamic_inplace_rhs.py", &[]).expect_err(
        "effectful or dynamically dispatched RHS calls must remain outside the boundary",
    );
    assert_eq!(
        failure.code,
        "frontend.python.heap.inplace-operator-argument-unsupported"
    );
}

#[test]
fn exact_inplace_operator_fixture_converts() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let result = check_pinned_heap_fixture(&suite, &pin, INPLACE_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {INPLACE_FIXTURE}: {error}"));
    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, INPLACE_FIXTURE)
        .expect_err("behavioral source classes remain outside the scalar backend");
    assert!(
        scalar.contains("frontend.python.contracts.module-statement-unsupported"),
        "{scalar}"
    );

    let reference = check_pinned_reference_fixture(&suite, &pin, INPLACE_FIXTURE)
        .expect_err("effectful operator methods remain outside the reference backend");
    assert!(
        reference.contains("frontend.python.references.class-unsupported"),
        "{reference}"
    );
}
