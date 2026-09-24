use std::path::PathBuf;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_heap_fixture};
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};
use maledictus::vc::ObligationStatus;

const FIXTURES: [&str; 2] = [
    "tests/functional/verification/test_boolop.py",
    "tests/functional/verification/test_funcs_and_methods.py",
];

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refuse(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("unsupported control flow must fail closed at the frontend boundary")
}

fn has_obligation(
    verification: &HeapContractVerification,
    id_fragment: &str,
    status: ObligationStatus,
) -> bool {
    verification
        .obligations
        .iter()
        .any(|obligation| obligation.id.contains(id_fragment) && obligation.status == status)
}

#[test]
fn exact_boolop_and_funcs_and_methods_fixtures_convert_semantically() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    for fixture in FIXTURES {
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
}

#[test]
fn and_or_return_the_selected_operand_in_left_to_right_order() {
    let verification = verify(
        r#"from typing import List

def run() -> None:
    empty = []  # type: List[int]
    nonempty = [7]  # type: List[int]

    last_truthy = 3 and 4 and 5
    first_truthy = 3 or 4 or 5
    first_falsy = 3 and empty and 5
    after_falsy = empty or 4 or 5
    reference_truthy = nonempty and 9

    assert last_truthy == 5
    assert first_truthy == 3
    assert first_falsy is empty
    assert after_falsy == 4
    assert reference_truthy == 9
"#,
        "operand_valued_boolops.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":assert:"))
            .count(),
        5,
        "{verification:#?}"
    );
    assert!(
        verification
            .obligations
            .iter()
            .all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn short_circuiting_skips_rhs_calls_and_keeps_evaluated_rhs_effects() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

    def __init__(self) -> None:
        Ensures(Acc(self.value) and self.value == 0)
        self.value = 0

    def mark(self) -> int:
        Requires(Acc(self.value))
        Ensures(Acc(self.value) and self.value == Old(self.value) + 1)
        Ensures(Result() == 1)
        self.value += 1
        return 1

class Forbidden:
    def __init__(self) -> None:
        Requires(False)

def run() -> None:
    cell = Cell()
    skipped_or = 7 or Forbidden()
    skipped_and = 0 and Forbidden()
    evaluated_or = 0 or cell.mark()
    assert cell.value == 1
    evaluated_and = 7 and cell.mark()
    assert cell.value == 2
"#,
        "short_circuit_effects.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn exact_builtin_truthiness_is_available_to_operand_selection() {
    let verification = verify(
        r#"from typing import List

class Plain:
    pass

def run() -> None:
    empty = []  # type: List[int]
    nonempty = [1]  # type: List[int]
    plain = Plain()

    assert (False or 1) == 1
    assert (True and 2) == 2
    assert (None or 3) == 3
    assert (0 or 4) == 4
    assert (-1 and 5) == 5
    assert (empty or 6) == 6
    assert (nonempty and 7) == 7
    assert (plain and 8) == 8
"#,
        "exact_builtin_truthiness.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":assert:"))
            .count(),
        8,
        "{verification:#?}"
    );
}

#[test]
fn custom_or_runtime_unknown_truth_hooks_fail_closed() {
    let custom_bool = refuse(
        r#"class CustomBool:
    def __bool__(self) -> bool:
        return True

def run(value: CustomBool) -> None:
    selected = value or 1
"#,
        "custom_bool_truthiness.py",
    );
    assert_eq!(
        custom_bool.code, "frontend.python.heap.truthiness-custom-hook-unsupported",
        "{custom_bool:#?}"
    );

    let custom_length = refuse(
        r#"class CustomLength:
    def __len__(self) -> int:
        return 1

def run(value: CustomLength) -> None:
    selected = value and 1
"#,
        "custom_length_truthiness.py",
    );
    assert_eq!(
        custom_length.code, "frontend.python.heap.truthiness-custom-hook-unsupported",
        "{custom_length:#?}"
    );

    let runtime_unknown = refuse(
        r#"def run(value: object) -> None:
    selected = value or 1
"#,
        "runtime_unknown_truthiness.py",
    );
    assert_eq!(
        runtime_unknown.code, "frontend.python.heap.truthiness-runtime-hook-unknown",
        "{runtime_unknown:#?}"
    );
}

#[test]
fn typed_parameter_field_writes_are_applied_at_the_post_heap() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    value: int

    def __init__(self) -> None:
        Ensures(Acc(self.value) and self.value == 0)
        self.value = 0

class Writer:
    def write(self, cell: Cell) -> None:
        Requires(Acc(cell.value))
        Ensures(Acc(cell.value) and cell.value == 5)
        cell.value = 5

def run() -> None:
    cell = Cell()
    writer = Writer()
    writer.write(cell)
    assert cell.value == 5
    assert False
"#,
        "typed_parameter_field_write.py",
    );

    assert!(
        has_obligation(&verification, ":assert:", ObligationStatus::Refuted),
        "{verification:#?}"
    );
}

#[test]
fn scalar_while_proves_establishment_preservation_and_false_exit() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

def countdown(start: int) -> int:
    Requires(start >= 0)
    Ensures(Result() == 0)
    value = start
    while value > 0:
        Invariant(value >= 0)
        value -= 1
    assert value == 0
    return value
"#,
        "scalar_while_proof.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert!(
        has_obligation(
            &verification,
            ":invariant-establishment:",
            ObligationStatus::Proved
        ),
        "{verification:#?}"
    );
    assert!(
        has_obligation(
            &verification,
            ":invariant-preservation:",
            ObligationStatus::Proved
        ),
        "{verification:#?}"
    );
    assert!(
        has_obligation(&verification, ":assert:", ObligationStatus::Proved),
        "{verification:#?}"
    );
}

#[test]
fn scalar_while_havocs_modified_locals_instead_of_reusing_entry_values() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

def run(start: int) -> None:
    Requires(start > 0)
    original = start
    value = start
    while value > 0:
        Invariant(value >= 0)
        value -= 1
    Assert(value == original)
"#,
        "scalar_while_havoc.py",
    );

    assert!(!verification.passed, "{verification:#?}");
    assert!(
        has_obligation(&verification, ":assert:", ObligationStatus::Refuted),
        "{verification:#?}"
    );
}

#[test]
fn scalar_while_reports_the_exact_failed_invariant_obligation() {
    let establishment = verify(
        r#"from nagini_contracts.contracts import *

def run(value: int) -> None:
    Requires(value >= 0)
    while value > 0:
        Invariant(value > 0)
        value -= 1
"#,
        "failed_invariant_establishment.py",
    );
    assert!(!establishment.passed, "{establishment:#?}");
    assert!(
        has_obligation(
            &establishment,
            ":invariant-establishment:",
            ObligationStatus::Refuted
        ),
        "{establishment:#?}"
    );

    let preservation = verify(
        r#"from nagini_contracts.contracts import *

def run(value: int) -> None:
    Requires(value >= 0)
    while value > 0:
        Invariant(value >= 0)
        value -= 2
"#,
        "failed_invariant_preservation.py",
    );
    assert!(!preservation.passed, "{preservation:#?}");
    assert!(
        has_obligation(
            &preservation,
            ":invariant-preservation:",
            ObligationStatus::Refuted
        ),
        "{preservation:#?}"
    );
}

#[test]
fn scalar_while_models_break_continue_return_and_raise_exits() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

def with_break(start: int) -> int:
    Requires(start >= 0)
    Ensures(Result() == 0 or Result() == 1)
    value = start
    while value > 0:
        Invariant(value >= 0)
        if value == 1:
            break
        value -= 1
    return value

def with_continue(start: int) -> int:
    Requires(start >= 0)
    Ensures(Result() == 0)
    value = start
    while value > 0:
        Invariant(value >= 0)
        value -= 1
        continue
    return value

def with_return(start: int) -> int:
    Requires(start >= 0)
    Ensures(Result() == 0 or Result() == 1)
    value = start
    while value > 0:
        Invariant(value >= 0)
        if value == 1:
            return value
        value -= 1
    return value

def with_raise(start: int) -> int:
    Requires(start >= 0)
    Ensures(Result() == 0)
    Exsures(Exception, True)
    value = start
    while value > 0:
        Invariant(value >= 0)
        if value == 1:
            raise Exception()
        value -= 1
    return value
"#,
        "scalar_while_abrupt_exits.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn while_else_remains_an_explicit_fail_closed_boundary() {
    let failure = refuse(
        r#"from nagini_contracts.contracts import *

def run(value: int) -> None:
    while value > 0:
        Invariant(value >= 0)
        value -= 1
    else:
        value = 0
"#,
        "while_else.py",
    );
    assert_eq!(
        failure.code, "frontend.python.heap.while-else-unsupported",
        "{failure:#?}"
    );
}
