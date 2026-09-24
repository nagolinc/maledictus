use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};
use maledictus::vc::ObligationStatus;

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it was refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refusal(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("expected the source to be refused before proof issuance")
}

fn assert_refusal(source: &str, path: &str, expected_code: &str) {
    let failure = refusal(source, path);
    assert_eq!(failure.code, expected_code, "{failure:#?}");
}

#[test]
fn public_heap_verifier_executes_integer_field_augmented_assignment() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int
    def __init__(self) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == 2)
        self.value = 2

def run() -> None:
    cell = Cell()
    cell.value += 3
    Assert(cell.value == 5)
"#,
        "v57_augassign_valid.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert!(verification.obligations.iter().any(|obligation| {
        obligation
            .id
            .starts_with("run:augmented-field-read-permission:value")
            && obligation.satisfied()
    }));
    assert!(verification.obligations.iter().any(|obligation| {
        obligation
            .id
            .starts_with("run:field-write-permission:value")
            && obligation.satisfied()
    }));
    assert!(
        verification.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn augmented_assignment_refutes_missing_and_fractional_write_permission() {
    let missing = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def run(cell: Cell) -> None:
    cell.value += 1
"#,
        "v57_augassign_missing_permission.py",
    );
    assert!(!missing.passed, "{missing:#?}");
    assert!(missing.obligations.iter().any(|obligation| {
        obligation
            .id
            .starts_with("run:augmented-field-read-permission:value")
            && obligation.status == ObligationStatus::Refuted
    }));
    assert!(missing.obligations.iter().any(|obligation| {
        obligation
            .id
            .starts_with("run:field-write-permission:value")
            && obligation.status == ObligationStatus::Refuted
    }));

    let fractional = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def run(cell: Cell) -> None:
    Requires(Acc(cell.value, 1 / 2))
    Ensures(Acc(cell.value, 1 / 2))
    cell.value += 1
"#,
        "v57_augassign_fractional_permission.py",
    );
    assert!(!fractional.passed, "{fractional:#?}");
    assert!(fractional.obligations.iter().any(|obligation| {
        obligation
            .id
            .starts_with("run:augmented-field-read-permission:value")
            && obligation.satisfied()
    }));
    assert!(fractional.obligations.iter().any(|obligation| {
        obligation
            .id
            .starts_with("run:field-write-permission:value")
            && obligation.status == ObligationStatus::Refuted
    }));
}

#[test]
fn module_function_summaries_preserve_numeric_old_and_selected_ifexp_effects() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int
    def __init__(self) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == 0)
        self.value = 0

def update_bool(value: bool, cell: Cell) -> bool:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    Ensures(cell.value == Old(cell.value) + 1)
    Ensures(Result() == value)
    cell.value += 1
    return value

def update_int(value: int, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    Ensures(cell.value == Old(cell.value) + 1)
    Ensures(Result() == value)
    cell.value += 1
    return value

def true_case() -> None:
    first = Cell()
    second = Cell()
    selected = update_int(15, first) if update_bool(True, first) else update_int(32, second)
    Assert(selected == 15)
    Assert(first.value == 2)
    Assert(second.value == 0)

def false_case() -> None:
    first = Cell()
    second = Cell()
    selected = update_int(15, first) if update_bool(False, first) else update_int(32, second)
    Assert(selected == 32)
    Assert(first.value == 1)
    Assert(second.value == 1)
"#,
        "v57_module_summary_ifexp.py",
    );

    assert!(verification.passed, "{verification:#?}");
    for caller in ["true_case", "false_case"] {
        assert_eq!(
            verification
                .obligations
                .iter()
                .filter(|obligation| {
                    obligation.id.starts_with(&format!("{caller}:assert:"))
                        && obligation.satisfied()
                })
                .count(),
            3,
            "{verification:#?}"
        );
    }
}

#[test]
fn module_function_calls_refuse_forward_and_recursive_and_retain_unproved_failure() {
    let forward = refusal(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def caller(flag: bool, cell: Cell) -> int:
    Requires(Acc(cell.value))
    selected = update(1, cell) if flag else 0
    return selected

def update(value: int, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    cell.value += 1
    return value
"#,
        "v57_module_summary_forward.py",
    );
    assert_eq!(
        forward.code, "frontend.python.heap.module-function-call-before-verification",
        "{forward:#?}"
    );

    let recursive = refusal(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def update(flag: bool, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    cell.value += 1
    selected = update(False, cell) if flag else 0
    return selected
"#,
        "v57_module_summary_recursive.py",
    );
    assert_eq!(
        recursive.code, "frontend.python.heap.conditional-expression-call-unsupported",
        "{recursive:#?}"
    );

    let unproved = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def update(value: int, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    Ensures(Result() == value + 1)
    cell.value += 1
    return value

def caller(flag: bool, cell: Cell) -> int:
    Requires(Acc(cell.value))
    selected = update(1, cell) if flag else 0
    return selected
"#,
        "v57_module_summary_unproved.py",
    );
    assert!(!unproved.passed, "{unproved:#?}");
    assert!(unproved.obligations.iter().any(|obligation| {
        obligation.id.starts_with("update:postcondition:")
            && obligation.status == ObligationStatus::Refuted
    }));
    assert!(unproved.obligations.iter().any(|obligation| {
        obligation.id.starts_with("caller:heap-function-complete:") && obligation.satisfied()
    }));
}

#[test]
fn effectful_ifexp_refuses_exceptional_callees() {
    assert_refusal(
        r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

class Cell:
    value: int
    def risky(self) -> int:
        Requires(Acc(self.value))
        Ensures(Acc(self.value))
        Exsures(Failure, Acc(self.value))
        return self.value

def run(flag: bool, cell: Cell) -> int:
    Requires(Acc(cell.value))
    selected = cell.risky() if flag else 0
    return selected
"#,
        "v57_ifexp_exceptional_callee.py",
        "frontend.python.heap.conditional-expression-call-unsupported",
    );
}

#[test]
fn module_function_calls_refuse_lexical_shadowing_and_wrong_nominal_receivers() {
    assert_refusal(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def update(value: int, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    cell.value += 1
    return value

def run(flag: bool, cell: Cell, update: int) -> int:
    Requires(Acc(cell.value))
    selected = update(1, cell) if flag else 0
    return selected
"#,
        "v57_module_summary_shadowed.py",
        "frontend.python.heap.module-function-call-shadowed",
    );

    assert_refusal(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

class Other:
    value: int

def update(value: int, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    cell.value += 1
    return value

def run(flag: bool, other: Other) -> int:
    Requires(Acc(other.value))
    selected = update(1, other) if flag else 0
    return selected
"#,
        "v57_module_summary_nominal_mismatch.py",
        "frontend.python.heap.module-function-receiver-type-mismatch",
    );
}

#[test]
fn module_function_calls_refuse_effectful_or_nonplain_arguments() {
    for (path, argument) in [
        ("v57_module_summary_field_argument.py", "cell.value"),
        ("v57_module_summary_effectful_argument.py", "cell.read()"),
    ] {
        let source = format!(
            r#"from nagini_contracts.contracts import *

class Cell:
    value: int
    def read(self) -> int:
        Requires(Acc(self.value))
        Ensures(Acc(self.value))
        return self.value

def update(value: int, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    cell.value += 1
    return value

def run(flag: bool, cell: Cell) -> int:
    Requires(Acc(cell.value))
    selected = update({argument}, cell) if flag else 0
    return selected
"#
        );
        assert_refusal(
            &source,
            path,
            "frontend.python.heap.module-function-call-evaluation-order-unsupported",
        );
    }
}

#[test]
fn effectful_ifexp_joins_bool_and_int_in_both_source_orders() {
    for (path, expression) in [
        (
            "v57_ifexp_bool_then_int.py",
            "update_bool(True, first) if flag else update_int(7, second)",
        ),
        (
            "v57_ifexp_int_then_bool.py",
            "update_int(7, first) if flag else update_bool(True, second)",
        ),
    ] {
        let source = format!(
            r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def update_bool(value: bool, cell: Cell) -> bool:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    cell.value += 1
    return value

def update_int(value: int, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    cell.value += 1
    return value

def run(flag: bool, first: Cell, second: Cell) -> int:
    Requires(Acc(first.value))
    Requires(Acc(second.value))
    selected = {expression}
    return selected
"#
        );
        let verification = verify(&source, path);
        assert!(verification.passed, "{verification:#?}");
    }
}

#[test]
fn effectful_short_circuit_preserves_int_operand_values_and_effects() {
    for (path, operator, selected, second_increment) in [
        ("v57_short_circuit_int_and.py", "and", 9, 1),
        ("v57_short_circuit_int_or.py", "or", 7, 0),
    ] {
        let source = format!(
            r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def update_int(value: int, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    Ensures(Result() == value)
    Ensures(cell.value == Old(cell.value) + 1)
    cell.value += 1
    return value

def run(first: Cell, second: Cell) -> int:
    Requires(Acc(first.value))
    Requires(Acc(second.value))
    Requires(first is not second)
    Ensures(Acc(first.value))
    Ensures(Acc(second.value))
    Ensures(Result() == {selected})
    Ensures(first.value == Old(first.value) + 1)
    Ensures(second.value == Old(second.value) + {second_increment})
    selected = update_int(7, first) {operator} update_int(9, second)
    return selected
"#
        );
        let verification = verify(&source, path);
        assert!(verification.passed, "{verification:#?}");
    }
}

#[test]
fn old_snapshot_syntax_refuses_argument_local_and_module_shadowing() {
    for (path, source) in [
        (
            "v57_old_argument_shadow.py",
            r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def update(value: int, cell: Cell, Old: int) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    Ensures(cell.value == Old(cell.value) + 1)
    cell.value += 1
    return value
"#,
        ),
        (
            "v57_old_local_shadow.py",
            r#"from nagini_contracts.contracts import *

class Cell:
    value: int

def update(value: int, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    Ensures(cell.value == Old(cell.value) + 1)
    Old = value
    cell.value += 1
    return value
"#,
        ),
    ] {
        assert_refusal(source, path, "frontend.python.heap.old-expression-shadowed");
    }

    assert_refusal(
        r#"from nagini_contracts.contracts import *

Old = 1

class Cell:
    value: int

def update(value: int, cell: Cell) -> int:
    Requires(Acc(cell.value))
    Ensures(Acc(cell.value))
    Ensures(cell.value == Old(cell.value) + 1)
    cell.value += 1
    return value
"#,
        "v57_old_module_shadow.py",
        "frontend.python.heap.module-binding-reassigned",
    );
}
