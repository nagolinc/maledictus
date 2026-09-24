use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_contracts::verify_contract_module;
use maledictus::vc::ObligationStatus;

const ENUMERATE_FIXTURE: &str = "tests/functional/verification/test_enumerate.py";

#[test]
fn concrete_enumerate_preserves_order_start_and_tuple_unpacking() {
    let verification = verify_contract_module(
        "def run() -> None:\n    values = [10, 11, 12]\n    pairs = enumerate(values, 5)\n    for index, value in pairs:\n        assert index == value - 5\n",
        "enumerate.py",
        &[],
    )
    .expect("concrete list enumeration should verify");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn symbolic_mutable_list_enumeration_requires_an_ownership_boundary() {
    let verification = verify_contract_module(
        "from typing import List\n\ndef run(values: List[int]) -> None:\n    pairs = enumerate(values)\n",
        "symbolic_enumerate.py",
        &[],
    )
    .expect("the unsupported permission is a proof obligation, not a frontend crash");
    let failures = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.status == ObligationStatus::Refuted)
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{verification:#?}");
    assert!(failures[0].id.contains(":call-permission-precondition:"));
}

#[test]
fn exact_unpacking_rejects_wrong_arity_and_preserves_starred_targets() {
    let wrong_arity = verify_contract_module(
        "def run() -> None:\n    pairs = enumerate([10], 5)\n    for index, value, extra in pairs:\n        pass\n",
        "wrong_arity.py",
        &[],
    )
    .expect_err("three targets cannot unpack an enumerate pair");
    assert_eq!(
        wrong_arity.code,
        "frontend.python.contracts.for-target-arity"
    );

    let starred = verify_contract_module(
        "def run() -> None:\n    pairs = enumerate([10], 5)\n    for index, *values in pairs:\n        assert index == 5\n        assert len(values) == 1\n        assert values[0] == 10\n",
        "starred_target.py",
        &[],
    )
    .expect("starred unpacking should preserve Python's concrete variable-arity semantics");
    assert!(starred.passed, "{starred:#?}");
}

#[test]
fn mutable_container_identity_distinguishes_aliases_from_equal_allocations() {
    let verification = verify_contract_module(
        "def run() -> None:\n    original = [1]\n    alias = original\n    separate = [1]\n    assert original is alias\n    assert original is not separate\n",
        "list_identity.py",
        &[],
    )
    .expect("list allocations and aliases have ordinary Python identity semantics");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn source_shadowing_prevents_builtin_enumerate_rebinding() {
    let verification = verify_contract_module(
        "def enumerate(value: int) -> int:\n    return value + 1\n\ndef run() -> None:\n    result = enumerate(2)\n    assert result == 3\n",
        "shadowed_enumerate.py",
        &[],
    )
    .expect("a source-defined enumerate must use the source-call semantics");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn scalar_and_heap_match_exact_enumerate_fixture_while_reference_stays_closed() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, ENUMERATE_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar {ENUMERATE_FIXTURE}: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(scalar.actual, scalar.expected, "{scalar:#?}");

    let heap = check_pinned_heap_fixture(&suite, &pin, ENUMERATE_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {ENUMERATE_FIXTURE}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual, "{heap:#?}");

    let reference = check_pinned_reference_fixture(&suite, &pin, ENUMERATE_FIXTURE)
        .expect_err("the fixture has no nominal-reference declarations");
    assert!(
        reference.contains("frontend.python.references.empty-module"),
        "{reference}"
    );
}
