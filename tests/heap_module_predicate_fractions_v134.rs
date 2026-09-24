use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to verify, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

#[test]
fn canonical_module_predicate_fractions_preserve_permission_ordering() {
    let result = verify(
        r#"from nagini_contracts.contracts import *

class Item:
    pass

@Predicate
def selected(item: Item) -> bool:
    return True

def require_less(item: Item) -> None:
    Requires(Acc(selected(item), 1 / 200))

def check(item: Item) -> None:
    Requires(Acc(selected(item), 1 / 100))
    require_less(item)
"#,
        "module_predicate_fractions.py",
    );
    assert!(result.passed, "{result:#?}");
}

#[test]
fn zero_fraction_predicate_preconditions_are_callable_and_permission_neutral() {
    let result = verify(
        r#"from nagini_contracts.contracts import *

class Item:
    pass

@Predicate
def selected(item: Item) -> bool:
    return True

def observe(item: Item) -> None:
    Requires(Acc(selected(item), 0 / 1))

def check(item: Item) -> None:
    observe(item)
    observe(item)
"#,
        "zero_predicate_permission_call.py",
    );
    assert!(result.passed, "{result:#?}");
}

#[test]
fn zero_fraction_does_not_skip_predicate_argument_evaluation() {
    let result = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

@Predicate
def positive(value: int) -> bool:
    return value > 0

def check(cell: Cell) -> None:
    Requires(Acc(positive(cell.value), 0 / 1))
"#,
        "zero_predicate_permission_field_argument.py",
    );
    assert!(!result.passed, "{result:#?}");
    assert!(
        result.obligations.iter().any(|obligation| {
            !obligation.satisfied() && obligation.id.contains(":field-permission:value:")
        }),
        "{result:#?}"
    );
}

#[test]
fn malformed_shadowed_and_nonpredicate_targets_fail_closed() {
    let cases = [
        (
            r#"from nagini_contracts.contracts import *
class Item:
    pass
@Predicate
def selected(item: Item) -> bool:
    return True
def check(item: Item, Acc: object) -> None:
    Requires(Acc(selected(item), 0 / 1))
"#,
            "shadowed_acc.py",
        ),
        (
            r#"from nagini_contracts.contracts import *
class Item:
    pass
@Predicate
def selected(item: Item) -> bool:
    return True
def check(item: Item, selected: object) -> None:
    Requires(Acc(selected(item), 0 / 1))
"#,
            "shadowed_predicate.py",
        ),
        (
            r#"from nagini_contracts.contracts import *
class Item:
    pass
@Predicate
def selected(item: Item) -> bool:
    return True
def check(item: Item) -> None:
    Requires(Acc(selected(), 0 / 1))
"#,
            "predicate_arity.py",
        ),
        (
            r#"from nagini_contracts.contracts import *
class Item:
    pass
def ordinary(item: Item) -> bool:
    return True
def check(item: Item) -> None:
    Requires(Acc(ordinary(item), 0 / 1))
"#,
            "nonpredicate_target.py",
        ),
    ];
    for (source, path) in cases {
        match verify_heap_module(source, path, &[]) {
            Ok(result) => assert!(!result.passed, "{path}: {result:#?}"),
            Err(failure) => assert!(
                failure.code.starts_with("frontend.python.heap."),
                "{path}: {failure:#?}"
            ),
        }
    }
}

#[test]
fn exact_zero_fraction_module_predicate_fixture_converts() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let result = check_pinned_heap_fixture(
        &suite,
        &pin,
        "tests/functional/verification/issues/00048.py",
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual, "{result:#?}");
}
