use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_heap_contracts::verify_heap_module;
use maledictus::vc::ObligationStatus;

const ENUMERATE_FIXTURE: &str = "tests/functional/verification/test_enumerate.py";

#[test]
fn concrete_enumerate_preserves_indices_values_start_and_identity() {
    let verification = verify_heap_module(
        r#"def run() -> None:
    values = [10, 11, 12]
    first = enumerate(values, 5)
    alias = first
    second = enumerate(values, 5)
    assert values is not first
    assert first is alias
    assert first is not second
    for index, value in first:
        assert index == value - 5
"#,
        "heap_enumerate.py",
        &[],
    )
    .expect("concrete builtin enumerate should lower with fresh iterator identity");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn wrong_enumerate_invariant_is_a_proof_failure_not_a_frontend_refusal() {
    let verification = verify_heap_module(
        r#"from nagini_contracts.contracts import Invariant

def run() -> None:
    values = [10, 11]
    pairs = enumerate(values, 5)
    for index, value in pairs:
        Invariant(index == value)
    assert False
"#,
        "heap_enumerate_invariant.py",
        &[],
    )
    .expect("a false enumerate invariant should remain a typed proof obligation");
    assert!(!verification.passed, "{verification:#?}");
    let refuted = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.status == ObligationStatus::Refuted)
        .collect::<Vec<_>>();
    assert_eq!(refuted.len(), 1, "{verification:#?}");
    assert!(
        refuted[0].id.contains(":invariant-establishment:"),
        "{verification:#?}"
    );
}

#[test]
fn symbolic_mutable_enumeration_reports_the_permission_boundary() {
    let verification = verify_heap_module(
        "from typing import List\n\ndef run(values: List[int]) -> None:\n    pairs = enumerate(values)\n",
        "heap_symbolic_enumerate.py",
        &[],
    )
    .expect("missing ownership should be a proof failure rather than a frontend error");
    let refuted = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.status == ObligationStatus::Refuted)
        .collect::<Vec<_>>();
    assert_eq!(refuted.len(), 1, "{verification:#?}");
    assert!(
        refuted[0]
            .id
            .contains(":call-permission-precondition:enumerate:"),
        "{verification:#?}"
    );
}

#[test]
fn enumerate_unpacking_and_source_shadowing_do_not_use_builtin_shortcuts() {
    let wrong_arity = verify_heap_module(
        "def run() -> None:\n    pairs = enumerate([10])\n    for index, value, extra in pairs:\n        pass\n",
        "heap_enumerate_wrong_arity.py",
        &[],
    )
    .expect_err("enumerate always yields exact two-element tuples");
    assert_eq!(wrong_arity.code, "frontend.python.heap.for-target-arity");

    let shadowed = verify_heap_module(
        "def enumerate(value: int) -> int:\n    return value + 1\n\ndef run() -> None:\n    result = enumerate(2)\n    assert result == 3\n",
        "heap_enumerate_shadowed.py",
        &[],
    )
    .expect("a source-defined enumerate must retain ordinary source-call semantics");
    assert!(shadowed.passed, "{shadowed:#?}");
}

#[test]
fn exact_enumerate_fixture_adds_one_heap_match_only() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let heap = check_pinned_heap_fixture(&suite, &pin, ENUMERATE_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {ENUMERATE_FIXTURE}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual, "{heap:#?}");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, ENUMERATE_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar {ENUMERATE_FIXTURE}: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(scalar.expected, scalar.actual, "{scalar:#?}");

    let reference = check_pinned_reference_fixture(&suite, &pin, ENUMERATE_FIXTURE)
        .expect_err("the enumerate fixture has no nominal reference declarations");
    assert!(
        reference.contains("frontend.python.references.empty-module"),
        "{reference}"
    );
}
