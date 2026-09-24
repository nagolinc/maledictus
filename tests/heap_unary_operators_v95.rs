use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_heap_contracts::verify_heap_module;

const UNARY_FIXTURE: &str = "tests/functional/verification/test_unary_operator.py";

#[test]
fn primitive_unary_operators_follow_python_integer_and_boolean_semantics() {
    let verification = verify_heap_module(
        "def run() -> None:\n    assert +1 == 1\n    assert -1 == -1\n    assert ~1 == -2\n    assert +True == 1\n    assert +True == True\n    assert -False == 0\n    assert ~False == -1\n",
        "primitive_unary.py",
        &[],
    )
    .expect("primitive unary operators should lower");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn unary_operator_dispatch_uses_verified_dunder_contract_and_a_fresh_result() {
    let verification = verify_heap_module(
        r#"from nagini_contracts.contracts import *

class Number:
    def __init__(self, value: int) -> None:
        self.value = value
        Ensures(Acc(self.value))
        Ensures(self.value == value)

    def __neg__(self) -> 'Number':
        Requires(Acc(self.value, 1 / 2))
        Ensures(Acc(self.value, 1 / 2) and Acc(ResultT(Number).value))
        Ensures(Result().value == -self.value)
        return Number(-self.value)

def run() -> None:
    original = Number(7)
    result = -original
    assert result is not original
    assert result.value == -7
    assert original.value == 7
"#,
        "overloaded_unary.py",
        &[],
    )
    .expect("verified unary dunder dispatch should lower");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn unsupported_unary_domains_and_missing_dunder_methods_fail_closed() {
    let nonnumeric = verify_heap_module(
        "def run() -> None:\n    value = +'text'\n",
        "nonnumeric_unary.py",
        &[],
    )
    .expect_err("unary plus on a string is outside the numeric fragment");
    assert_eq!(
        nonnumeric.code,
        "frontend.python.heap.unary-numeric-type-mismatch"
    );

    let missing_dunder = verify_heap_module(
        "class Item:\n    pass\n\ndef run() -> None:\n    item = Item()\n    value = +item\n",
        "missing_dunder.py",
        &[],
    )
    .expect_err("a nominal unary operation needs a verified matching dunder method");
    assert_eq!(
        missing_dunder.code,
        "frontend.python.heap.method-call-effects-unsupported"
    );
}

#[test]
fn exact_unary_fixture_is_a_heap_gain_while_other_backends_remain_closed() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let heap = check_pinned_heap_fixture(&suite, &pin, UNARY_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {UNARY_FIXTURE}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.actual, heap.expected, "{heap:#?}");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, UNARY_FIXTURE)
        .expect_err("source classes remain outside the scalar backend");
    assert!(
        scalar.contains("frontend.python.contracts.module-statement-unsupported"),
        "{scalar}"
    );

    let reference = check_pinned_reference_fixture(&suite, &pin, UNARY_FIXTURE)
        .expect_err("behavioral source classes remain outside the reference marker backend");
    assert!(
        reference.contains("frontend.python.references.class-unsupported"),
        "{reference}"
    );
}
