use std::path::PathBuf;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_heap_contracts::verify_heap_module;

fn verify(source: &str) -> maledictus::python_heap_contracts::HeapContractVerification {
    verify_heap_module(source, "heap_range_semantics_v93.py", &[])
        .unwrap_or_else(|failure| panic!("range source was refused: {failure:#?}"))
}

#[test]
fn static_range_membership_preserves_steps_empty_ranges_and_bool_int_equality() {
    let source = r#"from nagini_contracts.contracts import *

def run() -> None:
    ascending = range(-3, 4, 2)
    descending = range(5, -2, -2)
    empty = range(4, 4)
    Assert(-1 in ascending)
    Assert(0 not in ascending)
    Assert(3 in descending)
    Assert(4 not in descending)
    Assert(1 not in empty)
    Assert(True in range(0, 2))
"#;

    let verification = verify(source);
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn finite_range_forall_and_loops_execute_every_concrete_element() {
    let source = r#"from nagini_contracts.contracts import *

def run() -> None:
    values = range(1, 7, 2)
    Assert(Forall(values, lambda item: (item > 0, [])))
    # This quantifier is intentionally false.
    Assert(Forall(values, lambda item: (item < 5, [])))
    last = -1
    for item in values:
        last = item
        Assert(item % 2 == 1)
    Assert(last == 5)
"#;

    let verification = verify(source);
    let failed_assertions: Vec<_> = verification
        .obligations
        .iter()
        .filter(|item| item.id.contains(":assert:") && !item.satisfied())
        .collect();
    assert_eq!(failed_assertions.len(), 1, "{verification:#?}");
}

#[test]
fn malformed_or_shadowed_forall_and_zero_step_ranges_fail_closed() {
    for (source, expected_code) in [
        (
            "from nagini_contracts.contracts import *\ndef run() -> None:\n    Assert(Forall(range(3), lambda item: item >= 0))\n",
            "frontend.python.heap.forall-shape-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\ndef run(Forall: object) -> None:\n    Assert(Forall(range(3), lambda item: (item >= 0, [])))\n",
            "frontend.python.heap.forall-shadowed",
        ),
        (
            "from nagini_contracts.contracts import *\ndef run() -> None:\n    values = range(0, 3, 0)\n",
            "frontend.python.heap.range-step-zero",
        ),
    ] {
        let failure = verify_heap_module(source, "heap_range_semantics_v93_bad.py", &[])
            .expect_err("unsupported range semantics must fail closed");
        assert_eq!(failure.code, expected_code, "{failure:#?}");
    }
}

#[test]
fn exact_pinned_range_fixture_matches_all_diagnostics() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/functional/verification/test_range.py";

    let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("scalar range fixture was refused: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(scalar.expected, scalar.actual);
    assert_eq!(scalar.actual.len(), 3);

    let result = check_pinned_heap_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("heap range fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual);
    assert_eq!(result.actual.len(), 3);

    let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
        .expect_err("the nominal-reference backend has no source classes to analyze");
    assert!(
        reference.contains("frontend.python.references.empty-module"),
        "{reference}"
    );
}
