use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_heap_contracts::verify_heap_module;
use maledictus::vc::ObligationStatus;

const EMPTY_ITERABLE_FIXTURE: &str = "tests/functional/verification/issues/00115.py";

#[test]
fn typed_empty_lists_execute_exactly_zero_loop_iterations() {
    let verification = verify_heap_module(
        r#"from typing import List

def run() -> None:
    value = 7
    items: List[int] = []
    for value in items:
        assert False
    assert value == 7
"#,
        "empty_list_zero_iterations.py",
        &[],
    )
    .expect("an exact empty list should have an exact zero-iteration loop");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn empty_variable_tuple_lists_do_not_invent_an_element_or_bind_unpacking_targets() {
    let verification = verify_heap_module(
        r#"from typing import List, Tuple

def run() -> None:
    entries = []  # type: List[Tuple[int, ...]]
    for head, *tail in entries:
        assert False
"#,
        "empty_variable_tuple_list.py",
        &[],
    )
    .expect("an unreachable unpacking target does not require an invented tuple width");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn variable_tuple_erasure_is_limited_to_exact_empty_literals() {
    let nonempty = verify_heap_module(
        r#"from typing import List, Tuple

def run() -> None:
    entries = [(1, 2)]  # type: List[Tuple[int, ...]]
"#,
        "nonempty_variable_tuple_list.py",
        &[],
    )
    .expect_err("a real variable-length tuple element needs a representable element shape");
    assert_eq!(
        nonempty.code,
        "frontend.python.heap.variable-tuple-list-nonempty-unsupported"
    );

    let untyped = verify_heap_module(
        "def run() -> None:\n    items = []\n",
        "untyped_empty_list.py",
        &[],
    )
    .expect_err("an untyped empty list still has no element-type boundary");
    assert_eq!(
        untyped.code,
        "frontend.python.heap.empty-list-type-unsupported"
    );
}

#[test]
fn observing_an_empty_list_element_reports_the_bounds_failure() {
    let verification = verify_heap_module(
        r#"from typing import List

def run() -> None:
    items: List[int] = []
    value = items[0]
    assert False
"#,
        "empty_list_index.py",
        &[],
    )
    .expect("empty-list indexing should become an ordinary failed precondition");
    assert!(!verification.passed, "{verification:#?}");
    assert!(
        verification.obligations.iter().any(|obligation| {
            obligation.status == ObligationStatus::Refuted
                && obligation
                    .id
                    .contains("application-precondition:IndexError")
        }),
        "{verification:#?}"
    );
    assert!(
        verification
            .obligations
            .iter()
            .all(|obligation| !obligation.id.contains(":assert:")),
        "execution must stop before the later assertion: {verification:#?}"
    );
}

#[test]
fn exact_empty_variable_tuple_fixture_matches_in_heap_and_scalar_backends() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let heap = check_pinned_heap_fixture(&suite, &pin, EMPTY_ITERABLE_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {EMPTY_ITERABLE_FIXTURE}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual, "{heap:#?}");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, EMPTY_ITERABLE_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar {EMPTY_ITERABLE_FIXTURE}: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(scalar.expected, scalar.actual, "{scalar:#?}");

    let reference = check_pinned_reference_fixture(&suite, &pin, EMPTY_ITERABLE_FIXTURE)
        .expect_err("the fixture has no nominal reference declarations");
    assert!(
        reference.contains("frontend.python.references.empty-module"),
        "{reference}"
    );
}
