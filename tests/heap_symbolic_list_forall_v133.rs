use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to verify, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refusal(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("unsupported symbolic quantifier behavior must fail closed")
}

#[test]
fn borrowed_list_forall_uses_quantified_element_semantics_with_permission() {
    let result = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def all_positive(values: List[int]) -> None:
    Requires(Acc(list_pred(values)))
    Requires(Forall(values, lambda item: (item > 0, [])))
    Assert(Forall(values, lambda item: (item >= 0, [])))
"#,
        "symbolic_list_forall.py",
    );
    assert!(result.passed, "{result:#?}");
}

#[test]
fn borrowed_list_forall_requires_list_predicate_ownership() {
    let result = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def all_positive(values: List[int]) -> None:
    Requires(Forall(values, lambda item: (item > 0, [])))
"#,
        "symbolic_list_forall_without_permission.py",
    );
    assert!(!result.passed, "{result:#?}");
    let failures = result
        .obligations
        .iter()
        .filter(|obligation| !obligation.satisfied())
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{result:#?}");
    assert!(
        failures[0]
            .id
            .contains(":property-precondition:list-predicate:"),
        "{result:#?}"
    );
}

#[test]
fn exact_finite_lists_retain_eager_forall_semantics_without_borrowed_permission() {
    let result = verify(
        r#"from nagini_contracts.contracts import *

def check() -> None:
    Assert(Forall([1, 2, 3], lambda item: (item > 0, [])))
"#,
        "finite_list_forall.py",
    );
    assert!(result.passed, "{result:#?}");
}

#[test]
fn shadowed_and_non_list_symbolic_forall_sources_fail_closed() {
    let shadowed = refusal(
        r#"from nagini_contracts.contracts import *
from typing import List

def check(values: List[int], Forall: object) -> None:
    Requires(Forall(values, lambda item: (item > 0, [])))
"#,
        "shadowed_forall.py",
    );
    assert_eq!(
        shadowed.code, "frontend.python.heap.forall-shadowed",
        "{shadowed:#?}"
    );

    let non_list = refusal(
        r#"from nagini_contracts.contracts import *

def check(value: int) -> None:
    Requires(Forall(value, lambda item: (item > 0, [])))
"#,
        "non_list_forall.py",
    );
    assert_eq!(
        non_list.code, "frontend.python.heap.forall-collection-unsupported",
        "{non_list:#?}"
    );
}

#[test]
fn symbolic_slices_are_not_claimed_as_borrowed_list_provenance() {
    let failure = refusal(
        r#"from nagini_contracts.contracts import *
from typing import List

def check(values: List[int]) -> None:
    Requires(Acc(list_pred(values)))
    Requires(Forall(values[:], lambda item: (item > 0, [])))
"#,
        "sliced_symbolic_list_forall.py",
    );
    assert_eq!(
        failure.code, "frontend.python.heap.forall-collection-unsupported",
        "{failure:#?}"
    );
}

#[test]
fn exact_symbolic_list_forall_fixture_converts() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let result = check_pinned_heap_fixture(
        &suite,
        &pin,
        "tests/functional/verification/issues/00046.py",
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual, "{result:#?}");
}
