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
        .expect_err("non-subtype return sorts must remain unsupported")
}

#[test]
fn bool_returns_are_promoted_to_python_int_values() {
    let result = verify(
        r#"from nagini_contracts.contracts import *

def one() -> int:
    Ensures(Result() == 1)
    return True

def zero() -> int:
    Ensures(Result() == 0)
    return False
"#,
        "bool_int_direct_returns.py",
    );
    assert!(result.passed, "{result:#?}");
}

#[test]
fn promoted_bool_results_flow_through_reusable_scalar_calls() {
    let result = verify(
        r#"from nagini_contracts.contracts import *

@Pure
def one() -> int:
    return True

@Pure
def zero() -> int:
    return False

def use_results() -> None:
    assert one() == 1
    assert zero() == 0
    assert one() + zero() == 1
"#,
        "bool_int_scalar_calls.py",
    );
    assert!(result.passed, "{result:#?}");
}

#[test]
fn heap_effecting_functions_use_the_same_bool_to_int_return_boundary() {
    let result = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    def __init__(self) -> None:
        Ensures(Acc(self.value))
        self.value = 0

def set_and_return(cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    Ensures(Result() == 1)
    cell.value = 3
    return True
"#,
        "bool_int_heap_return.py",
    );
    assert!(result.passed, "{result:#?}");
}

#[test]
fn unrelated_return_sort_mismatches_still_fail_closed() {
    for (source, path) in [
        (
            "def wrong() -> str:\n    return True\n",
            "bool_as_string.py",
        ),
        ("def wrong() -> bool:\n    return 1\n", "int_as_bool.py"),
    ] {
        let failure = refusal(source, path);
        assert_eq!(
            failure.code, "frontend.python.heap.function-return-type-mismatch",
            "{path}: {failure:#?}"
        );
    }
}

#[test]
fn exact_bool_as_int_return_fixture_converts() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let result = check_pinned_heap_fixture(
        &suite,
        &pin,
        "tests/functional/verification/issues/00032.py",
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
    assert!(result.semantic_verified, "{result:#?}");
    assert_eq!(result.expected, result.actual, "{result:#?}");
}
