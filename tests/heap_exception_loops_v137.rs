use std::path::Path;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

const EXCEPTION_LOOP_FIXTURE: &str = "tests/functional/verification/test_exception_loop.py";

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn terminating_exception_loop(normal_value: i64, exceptional_value: i64) -> String {
    format!(
        r#"from nagini_contracts.contracts import *

class Container:
    def __init__(self) -> None:
        Ensures(Acc(self.value) and self.value == 0)
        self.value = 0

def run(c: Container, exceptional: bool) -> None:
    Requires(Acc(c.value))
    Ensures(Acc(c.value) and c.value == {normal_value})
    Exsures(Exception, Acc(c.value) and c.value == {exceptional_value})
    while True:
        Invariant(Acc(c.value))
        if exceptional:
            c.value = 7
            raise Exception()
        c.value = 8
        break
"#
    )
}

#[test]
fn terminating_while_splits_break_and_typed_exception_paths() {
    let verification = verify(&terminating_exception_loop(8, 7), "terminating_loop.py");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn normal_and_exceptional_loop_exits_check_their_own_contracts() {
    let normal = verify(&terminating_exception_loop(9, 7), "bad_normal_loop.py");
    assert!(!normal.passed, "{normal:#?}");
    assert!(
        normal
            .obligations
            .iter()
            .any(|obligation| !obligation.satisfied() && obligation.id.contains(":postcondition:")),
        "{normal:#?}"
    );

    let exceptional = verify(&terminating_exception_loop(8, 9), "bad_exceptional_loop.py");
    assert!(!exceptional.passed, "{exceptional:#?}");
    assert!(
        exceptional
            .obligations
            .iter()
            .any(|obligation| !obligation.satisfied()
                && obligation.id.contains(":exception-postcondition:")),
        "{exceptional:#?}"
    );
}

#[test]
fn iterative_scalar_backedges_and_continue_are_proved_from_invariants() {
    for (source, path) in [
        (
            r#"from nagini_contracts.contracts import *
def run(value: int) -> None:
    while True:
        Invariant(True)
        value += 1
"#,
            "loop_backedge.py",
        ),
        (
            r#"from nagini_contracts.contracts import *
def run() -> None:
    while True:
        Invariant(True)
        continue
"#,
            "loop_continue.py",
        ),
    ] {
        let verification = verify(source, path);
        assert!(verification.passed, "{path}: {verification:#?}");
        assert!(
            verification
                .obligations
                .iter()
                .any(|obligation| obligation.id.contains(":invariant-preservation:")),
            "{path}: {verification:#?}"
        );
    }
}

#[test]
fn still_unsupported_while_shapes_fail_closed() {
    let cases = [
        (
            r#"from nagini_contracts.contracts import *
def run() -> None:
    while True:
        Invariant(True)
        break
    else:
        pass
"#,
            "loop_else.py",
            "frontend.python.heap.while-else-unsupported",
        ),
        (
            r#"from nagini_contracts.contracts import *
def run(value: int) -> None:
    while True:
        value += 1
        Invariant(True)
        break
"#,
            "late_invariant.py",
            "frontend.python.heap.loop-invariant-position-unsupported",
        ),
    ];

    for (source, path, expected_code) in cases {
        let failure = verify_heap_module(source, path, &[])
            .expect_err("unsupported loop control flow must not be approximated");
        assert_eq!(failure.code, expected_code, "{path}: {failure:#?}");
    }
}

#[test]
fn shadowed_contract_and_exception_bindings_are_not_treated_as_canonical() {
    let shadowed_invariant = verify_heap_module(
        r#"from nagini_contracts.contracts import *
def run(Invariant: object) -> None:
    while True:
        Invariant(True)
        break
"#,
        "shadowed_invariant.py",
        &[],
    )
    .expect_err("a local Invariant binding must not become a contract declaration");
    assert_eq!(
        shadowed_invariant.code,
        "frontend.python.heap.loop-invariant-shadowed"
    );

    let shadowed_exception = verify_heap_module(
        r#"from nagini_contracts.contracts import *
def run(Exception: object) -> None:
    Exsures(Exception, True)
    raise Exception()
"#,
        "shadowed_exception.py",
        &[],
    )
    .expect_err("a local Exception binding must not become the built-in allocator");
    assert_eq!(
        shadowed_exception.code,
        "frontend.python.heap.class-name-shadowed"
    );
}

#[test]
fn optional_primitive_none_subset_does_not_accept_primitive_returns() {
    let none_only = verify(
        r#"from typing import Optional
def run() -> Optional[int]:
    while True:
        break
"#,
        "optional_none_subset.py",
    );
    assert!(none_only.passed, "{none_only:#?}");

    let primitive = verify_heap_module(
        r#"from typing import Optional
def run() -> Optional[int]:
    return 1
"#,
        "optional_primitive_return.py",
        &[],
    )
    .expect_err("primitive Optional returns need a value-union representation");
    assert_eq!(
        primitive.code,
        "frontend.python.heap.function-return-type-mismatch"
    );
}

#[test]
fn exact_exception_loop_fixture_has_three_expected_diagnostics() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let result = check_pinned_heap_fixture(&suite, &pin, EXCEPTION_LOOP_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {EXCEPTION_LOOP_FIXTURE}: {error}"));
    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
    assert_eq!(result.actual.len(), 3, "{result:#?}");
}
