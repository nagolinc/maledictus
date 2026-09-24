use std::path::Path;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_heap_fixture};
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};
use maledictus::vc::ObligationStatus;

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn assert_proved(verification: &HeapContractVerification) {
    assert!(verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

fn assert_pinned_fixture(fixture: &str) {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let result = check_pinned_heap_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("heap classifier refused {fixture}: {error}"));
    assert!(result.passed, "{fixture}: {result:#?}");
    assert_eq!(result.expected, result.actual, "{fixture}: {result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SemanticVerification,
        "{fixture}: {result:#?}"
    );
}

#[test]
fn exact_sif_try_catch_fixture_matches_semantically() {
    assert_pinned_fixture("tests/sif-true/verification/test_try_catch.py");
}

#[test]
fn exact_functional_exception_fixture_matches_semantically() {
    assert_pinned_fixture("tests/functional/verification/test_exception.py");
}

#[test]
fn try_else_runs_only_after_a_normal_protected_exit() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

def run(fail: bool) -> int:
    Ensures(Implies(fail, Result() == 2))
    Ensures(Implies(not fail, Result() == 3))
    try:
        if fail:
            raise Failure()
        value = 1
    except Failure:
        value = 2
    else:
        value = 3
    return value
"#,
        "try_else_paths.py",
    );

    assert_proved(&verification);
}

#[test]
fn the_first_matching_typed_handler_wins() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class BaseFailure(Exception):
    pass

class SpecificFailure(BaseFailure):
    pass

def run() -> int:
    Ensures(Result() == 1)
    try:
        raise SpecificFailure()
    except BaseFailure:
        value = 1
    except SpecificFailure:
        value = 2
    return value
"#,
        "first_matching_handler.py",
    );

    assert_proved(&verification);
}

#[test]
fn an_unmatched_exception_propagates_to_the_function_boundary() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class HandledFailure(Exception):
    pass

class EscapingFailure(Exception):
    pass

def run() -> None:
    Ensures(False)
    Exsures(EscapingFailure, True)
    try:
        raise EscapingFailure()
    except HandledFailure:
        Assert(False)
"#,
        "unmatched_exception_propagation.py",
    );

    assert_proved(&verification);
}

#[test]
fn except_as_has_the_caught_exception_type_inside_its_handler() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class BaseFailure(Exception):
    pass

class SpecificFailure(BaseFailure):
    pass

def run() -> bool:
    Ensures(Result())
    try:
        raise SpecificFailure()
    except BaseFailure as error:
        return isinstance(error, SpecificFailure) and isinstance(error, BaseFailure)
"#,
        "typed_exception_binding.py",
    );

    assert_proved(&verification);
}

#[test]
fn except_as_binding_is_deleted_after_the_handler() {
    let verification = verify(
        r#"class AppFailure(Exception):
    pass

def run() -> None:
    try:
        raise AppFailure()
    except AppFailure as error:
        pass
    assert error is error
"#,
        "deleted_exception_binding.py",
    );
    assert!(!verification.passed, "{verification:#?}");
    assert!(
        verification.obligations.iter().any(|obligation| {
            obligation.id.contains(":undefined-local:error:")
                && obligation.status == ObligationStatus::Refuted
        }),
        "{verification:#?}"
    );
}

#[test]
fn finally_runs_on_normal_fallthrough() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def normal(cell: Cell) -> None:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value) and cell.value == 2)
    try:
        cell.value = 1
    finally:
        cell.value += 1
"#,
        "finally_normal.py",
    );

    assert_proved(&verification);
}

#[test]
fn finally_runs_on_exceptional_exit() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

class Cell:
    value: int

def run(cell: Cell) -> None:
    Requires(Acc(cell.value))
    Ensures(False)
    Exsures(Failure, Acc(cell.value) and cell.value == 2)
    try:
        cell.value = 1
        raise Failure()
    finally:
        cell.value += 1
"#,
        "finally_raise.py",
    );

    assert_proved(&verification);
}

#[test]
fn finally_runs_before_a_pending_return_completes() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def run(cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Result() == 7)
    Ensures(Acc(cell.value) and cell.value == 2)
    try:
        cell.value = 1
        return 7
    finally:
        cell.value += 1
"#,
        "finally_before_return.py",
    );

    assert_proved(&verification);
}

#[test]
fn finally_runs_before_break_transfers_control() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

def run() -> int:
    Ensures(Result() == 1)
    value = 0
    while True:
        Invariant(value >= 0 and value <= 1)
        try:
            break
        finally:
            value = 1
    return value
"#,
        "finally_before_break.py",
    );

    assert_proved(&verification);
}

#[test]
fn finally_runs_before_continue_transfers_control() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

def run() -> int:
    Ensures(Result() == 3)
    value = 0
    while value < 3:
        Invariant(value >= 0 and value <= 3)
        try:
            continue
        finally:
            value += 1
    return value
"#,
        "finally_before_continue.py",
    );

    assert_proved(&verification);
}

#[test]
fn a_finally_return_overrides_a_pending_raise() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class InitialFailure(Exception):
    pass

def run() -> int:
    Ensures(Result() == 9)
    try:
        raise InitialFailure()
    finally:
        return 9
"#,
        "finally_return_overrides_raise.py",
    );

    assert_proved(&verification);
}

#[test]
fn a_finally_raise_overrides_a_pending_return() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class FinalFailure(Exception):
    pass

def run() -> int:
    Ensures(False)
    Exsures(FinalFailure, True)
    try:
        return 9
    finally:
        raise FinalFailure()
"#,
        "finally_raise_overrides_return.py",
    );

    assert_proved(&verification);
}

#[test]
fn raising_a_class_object_constructs_and_raises_that_exception_type() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

def run() -> None:
    Ensures(False)
    Exsures(Failure, True)
    raise Failure
"#,
        "raise_exception_class.py",
    );

    assert_proved(&verification);
}

#[test]
fn raising_a_class_object_uses_its_verified_zero_argument_constructor_contract() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class VariadicFailure(Exception):
    def __init__(self, *args: object) -> None:
        Requires(len(args) == 0)

def run() -> None:
    Ensures(False)
    Exsures(VariadicFailure, True)
    raise VariadicFailure
"#,
        "raise_variadic_exception_class.py",
    );

    assert_proved(&verification);
    assert!(
        verification.obligations.iter().any(|obligation| {
            obligation
                .id
                .contains(":constructor-precondition:VariadicFailure:")
        }),
        "{verification:#?}"
    );
}

#[test]
fn bare_reraise_preserves_the_active_exception() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

def run() -> None:
    Ensures(False)
    Exsures(Failure, True)
    try:
        raise Failure()
    except Failure:
        raise
"#,
        "bare_reraise.py",
    );

    assert_proved(&verification);
}

#[test]
fn an_exception_raised_by_a_handler_replaces_the_caught_exception() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class InitialFailure(Exception):
    pass

class HandlerFailure(Exception):
    pass

def run() -> None:
    Ensures(False)
    Exsures(HandlerFailure, True)
    try:
        raise InitialFailure()
    except InitialFailure:
        raise HandlerFailure()
"#,
        "handler_raised_exception.py",
    );

    assert_proved(&verification);
}
