use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_heap_contracts::verify_heap_module;
use maledictus::vc::ObligationStatus;

const BOOL_OBJECT_FIXTURE: &str = "tests/functional/verification/issues/00281.py";

#[test]
fn bool_conversion_preserves_ordinary_scalar_and_collection_truthiness() {
    let verification = verify_heap_module(
        r#"def run() -> None:
    values = {1: 2}
    assert bool() == False
    assert bool(False) == False
    assert bool(True) == True
    assert bool(0) == False
    assert bool(-3) == True
    assert bool('') == False
    assert bool('value') == True
    assert bool(b'') == False
    assert bool(b'value') == True
    assert bool((1,)) == True
    assert bool([1]) == True
    assert bool(values) == True
"#,
        "builtin_bool_truthiness.py",
        &[],
    )
    .expect("canonical bool conversion should lower ordinary supported values");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn object_parameter_keeps_each_actual_call_site_type_during_pure_inlining() {
    let verification = verify_heap_module(
        r#"from nagini_contracts.contracts import *

@Pure
def truthy(value: object) -> bool:
    return bool(value)

def run() -> None:
    assert truthy(False) == False
    assert truthy(0) == False
    assert truthy(4) == True
    assert truthy('') == False
    assert truthy('value') == True
"#,
        "object_parameter_truthiness.py",
        &[],
    )
    .expect("object parameters should accept and preserve concrete actual types");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn opaque_object_truthiness_remains_unknown_instead_of_becoming_true_by_fiat() {
    let verification = verify_heap_module(
        r#"from nagini_contracts.contracts import *

@Pure
def truthy(value: object) -> bool:
    return bool(value)

def claim(value: object) -> None:
    Assert(truthy(value))
"#,
        "opaque_object_truthiness.py",
        &[],
    )
    .expect("opaque truthiness should become an ordinary proof obligation");
    assert!(!verification.passed, "{verification:#?}");
    assert!(verification.obligations.iter().any(|obligation| {
        obligation.status == ObligationStatus::Refuted && obligation.id.contains(":assert:")
    }));
}

#[test]
fn malformed_bool_calls_and_non_object_parameter_mismatches_fail_closed() {
    let malformed = verify_heap_module(
        "def run() -> None:\n    value = bool(1, 2)\n",
        "malformed_bool.py",
        &[],
    )
    .expect_err("bool has a fixed zero-or-one-argument signature");
    assert_eq!(malformed.code, "frontend.python.heap.bool-arguments");

    let wrong_parameter_type = verify_heap_module(
        r#"def identity(value: int) -> int:
    return value

def run() -> None:
    value = identity('wrong')
"#,
        "non_object_parameter_mismatch.py",
        &[],
    )
    .expect_err("accepts-any behavior belongs only to an explicit object annotation");
    assert_eq!(
        wrong_parameter_type.code,
        "frontend.python.heap.function-call-argument-type-mismatch"
    );
}

#[test]
fn exact_bool_object_fixture_is_a_heap_gain_only() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let heap = check_pinned_heap_fixture(&suite, &pin, BOOL_OBJECT_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {BOOL_OBJECT_FIXTURE}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual, "{heap:#?}");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, BOOL_OBJECT_FIXTURE)
        .expect_err("object-typed parameters remain outside the scalar backend");
    assert!(
        scalar.contains("frontend.python.contracts.type-unsupported"),
        "{scalar}"
    );

    let reference = check_pinned_reference_fixture(&suite, &pin, BOOL_OBJECT_FIXTURE)
        .expect_err("the fixture has no nominal reference declarations");
    assert!(
        reference.contains("frontend.python.references.empty-module"),
        "{reference}"
    );
}
