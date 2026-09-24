use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_heap_contracts::verify_heap_module;

fn verify(source: &str) -> maledictus::python_heap_contracts::HeapContractVerification {
    verify_heap_module(source, "heap_let_tuple_v89.py", &[])
        .unwrap_or_else(|failure| panic!("source was refused: {failure:#?}"))
}

fn refused(source: &str) -> maledictus::python_contracts::ContractFailure {
    verify_heap_module(source, "heap_let_tuple_v89_adversary.py", &[])
        .expect_err("unsupported Let or collection-key semantics must fail closed")
}

#[test]
fn let_binds_scalar_and_reference_values_without_losing_permissions() {
    let source = r#"from nagini_contracts.contracts import *

def below_five(value: int) -> None:
    Requires(Let(5, bool, lambda five: five > value))
    pass

class Cell:
    def __init__(self) -> None:
        self.value = 0
        Ensures(Acc(self.value))

def update(cell: Cell) -> None:
    Requires(Let(cell, bool, lambda bound: Acc(bound.value)))
    Ensures(Acc(cell.value))
    Ensures(Let(cell.value, bool, lambda value: value == 2))
    cell.value = 2

def client() -> None:
    below_five(3)
    cell = Cell()
    update(cell)
    assert cell.value == 2
"#;
    let verification = verify(source);
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn malformed_or_mistyped_let_calls_are_rejected_explicitly() {
    for (source, expected_code) in [
        (
            "from nagini_contracts.contracts import *\ndef run() -> None:\n    Requires(Let(1, bool))\n",
            "frontend.python.heap.let-call-shape-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\ndef run() -> None:\n    Requires(Let(1, bool, True))\n",
            "frontend.python.heap.let-lambda-required",
        ),
        (
            "from nagini_contracts.contracts import *\ndef run() -> None:\n    Requires(Let(1, bool, lambda value=1: value == 1))\n",
            "frontend.python.heap.let-lambda-signature-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\ndef run() -> None:\n    Requires(Let(1, int, lambda value: value == 1))\n",
            "frontend.python.heap.let-result-type-mismatch",
        ),
        (
            "from nagini_contracts.contracts import *\ndef run(Let: int) -> None:\n    Requires(Let(1, bool, lambda value: value == 1))\n",
            "frontend.python.heap.let-shadowed",
        ),
    ] {
        let failure = refused(source);
        assert_eq!(failure.code, expected_code, "{failure:#?}");
    }
}

#[test]
fn immutable_tuple_globals_and_exact_tuple_keys_are_preserved() {
    let source = r#"from nagini_contracts.contracts import *
from typing import Set, Tuple

PAIR = ('stable', 7)

def run() -> None:
    local = ('other', 9)
    values: Set[Tuple[str, int]] = {PAIR, local}
    assert PAIR in values
    assert ('missing', 7) not in values
"#;
    let verification = verify(source);
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn mutable_values_cannot_hide_inside_exact_tuple_keys() {
    let failure = refused(
        "from typing import Set, Tuple, List\ndef run() -> None:\n    values: Set[Tuple[List[int], int]] = {([1], 2)}\n",
    );
    assert_eq!(
        failure.code, "frontend.python.heap.collection-key-type-unsupported",
        "{failure:#?}"
    );
}

#[test]
fn exact_upstream_let_fixture_matches_all_diagnostics() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let result = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/verification/test_let.py",
    )
    .unwrap_or_else(|error| panic!("exact upstream Let fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual);
    assert_eq!(result.actual.len(), 3);
}
