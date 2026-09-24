use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_reference_contracts::verify_reference_module;
use maledictus::vc::ObligationStatus;

const PURE_REFERENCE_FIXTURE: &str = "tests/functional/verification/issues/00031.py";

#[test]
fn pure_reference_predicate_body_composes_into_postconditions() {
    let verification = verify_reference_module(
        r#"from nagini_contracts.contracts import *

class Item:
    pass

@Pure
def same(left: Item, right: Item) -> bool:
    return left is right

def verify(item: Item) -> None:
    Ensures(same(item, item))
"#,
        "pure_reference_predicate.py",
        &[],
    )
    .expect("a closed pure reference predicate should verify");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn false_pure_reference_postcondition_is_refuted_from_nonnull_input() {
    let verification = verify_reference_module(
        r#"from nagini_contracts.contracts import *

class Item:
    pass

@Pure
def same(left: Item, right: Item) -> bool:
    return left is right

def verify(item: Item) -> None:
    Ensures(same(item, None))
"#,
        "false_pure_reference_postcondition.py",
        &[],
    )
    .expect("a false postcondition should become a refuted obligation");
    assert!(!verification.passed, "{verification:#?}");
    assert!(verification.obligations.iter().any(|obligation| {
        obligation.status == ObligationStatus::Refuted
            && obligation.id.starts_with("verify:postcondition:")
    }));
}

#[test]
fn pure_reference_calls_preserve_nominal_argument_checks() {
    let verification = verify_reference_module(
        r#"from nagini_contracts.contracts import *

class Expected:
    pass

class Actual:
    pass

@Pure
def accepts(value: Expected) -> bool:
    return True

def verify(value: Actual) -> None:
    Ensures(accepts(value))
"#,
        "pure_reference_argument_type.py",
        &[],
    )
    .expect("an incompatible call should remain a proof failure");
    assert!(!verification.passed, "{verification:#?}");
    assert!(verification.obligations.iter().any(|obligation| {
        obligation.status == ObligationStatus::Refuted
            && obligation.id.contains("ensures-call-precondition")
    }));
}

#[test]
fn recursive_and_non_boolean_pure_reference_functions_fail_closed() {
    let recursive = verify_reference_module(
        r#"from nagini_contracts.contracts import *

class Item:
    pass

@Pure
def recurse(value: Item) -> bool:
    return recurse(value)
"#,
        "recursive_pure_reference.py",
        &[],
    )
    .expect_err("recursive pure predicates need a termination proof before expansion");
    assert_eq!(recursive.code, "frontend.python.references.pure-call-cycle");

    let non_boolean = verify_reference_module(
        r#"from nagini_contracts.contracts import *

class Item:
    pass

@Pure
def identity(value: Item) -> Item:
    return value
"#,
        "non_boolean_pure_reference.py",
        &[],
    )
    .expect_err("this pure-predicate fragment must not widen to reference-returning purity");
    assert_eq!(
        non_boolean.code,
        "frontend.python.references.signature-unsupported"
    );
}

#[test]
fn exact_pure_reference_fixture_gains_reference_coverage_only() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let reference = check_pinned_reference_fixture(&suite, &pin, PURE_REFERENCE_FIXTURE)
        .unwrap_or_else(|error| panic!("reference {PURE_REFERENCE_FIXTURE}: {error}"));
    assert!(reference.passed, "{reference:#?}");
    assert_eq!(reference.expected, reference.actual, "{reference:#?}");

    let heap = check_pinned_heap_fixture(&suite, &pin, PURE_REFERENCE_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {PURE_REFERENCE_FIXTURE}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual, "{heap:#?}");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, PURE_REFERENCE_FIXTURE)
        .expect_err("nominal reference parameters remain outside the scalar backend");
    assert!(
        scalar.contains("frontend.python.contracts.type-unsupported"),
        "{scalar}"
    );
}
