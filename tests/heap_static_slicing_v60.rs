use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};
use maledictus::vc::ObligationStatus;

fn verify(source: &str) -> HeapContractVerification {
    verify_heap_module(source, "heap_static_slicing.py", &[]).unwrap_or_else(|failure| {
        panic!(
            "expected static slicing source to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refuse(source: &str) -> ContractFailure {
    verify_heap_module(source, "heap_static_slicing_adversary.py", &[])
        .expect_err("unsupported slicing must refuse before proof issuance")
}

#[test]
fn static_list_and_tuple_slices_follow_python_bounds_steps_and_negative_indices() {
    let verification = verify(
        r#"def run() -> None:
    values = [1, 2, 3, 4, 5]
    middle = values[1:4]
    stride = values[::2]
    reverse = values[::-1]
    clipped = values[-20:20]
    empty = values[2:2]
    explicit_negative_stop = values[:-1:-1]
    extreme_reverse = values[100:-100:-3]
    huge_step = values[::100]
    huge_reverse_step = values[::-100]
    assert len(middle) == 3
    assert middle[0] == 2
    assert middle[-1] == 4
    assert len(stride) == 3
    assert stride[1] == 3
    assert reverse[0] == 5
    assert reverse[-1] == 1
    assert len(clipped) == 5
    assert len(empty) == 0
    assert len(explicit_negative_stop) == 0
    assert len(extreme_reverse) == 2
    assert extreme_reverse[0] == 5
    assert extreme_reverse[1] == 2
    assert len(huge_step) == 1
    assert huge_step[0] == 1
    assert len(huge_reverse_step) == 1
    assert huge_reverse_step[0] == 5

    pair = (10, 20, 30, 40)
    tail = pair[-3:]
    backwards = pair[3:0:-2]
    empty_pair = pair[2:2]
    empty_input = ()[::-1]
    assert len(tail) == 3
    assert tail[0] == 20
    assert tail[-1] == 40
    assert backwards[0] == 40
    assert backwards[1] == 20
    assert len(empty_pair) == 0
    assert len(empty_input) == 0
"#,
    );

    assert!(verification.passed, "{verification:#?}");
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":assert:"))
            .count(),
        24,
        "{verification:#?}"
    );
    assert!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":assert:"))
            .all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn slicing_refuses_dynamic_or_untyped_shapes_zero_steps_and_mutation() {
    for (source, code) in [
        (
            "def run(start: int) -> None:\n    values = [1, 2, 3]\n    part = values[start:]\n",
            "frontend.python.heap.slice-bound-unsupported",
        ),
        (
            "def run() -> None:\n    values = [1, 2, 3]\n    part = values[::0]\n",
            "frontend.python.heap.slice-step-zero",
        ),
        (
            "def run() -> None:\n    values = [1, 2, 3]\n    values[1:2] = [7]\n",
            "frontend.python.heap.function-assignment-target",
        ),
        (
            "def run() -> None:\n    values = [1, True]\n",
            "frontend.python.heap.list-element-type-mismatch",
        ),
    ] {
        let failure = refuse(source);
        assert_eq!(failure.code, code, "{failure:#?}");
    }
}

#[test]
fn partial_contract_index_is_checked_at_the_concrete_call_boundary() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Reader:
    def accept(self, *values: int) -> None:
        Requires(values[0] > 0)

    def invalid(self) -> None:
        self.accept()
"#,
    );

    assert!(!verification.passed, "{verification:#?}");
    let index_errors = verification
        .obligations
        .iter()
        .filter(|obligation| {
            obligation
                .id
                .contains(":application-precondition:IndexError:")
        })
        .collect::<Vec<_>>();
    assert_eq!(index_errors.len(), 1, "{verification:#?}");
    assert_eq!(
        index_errors[0].status,
        ObligationStatus::Refuted,
        "{verification:#?}"
    );
}

#[test]
fn exact_upstream_slicing_fixture_matches_lists_tuples_bytes_ranges_and_index_errors() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let result = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/verification/test_slicing.py",
    )
    .unwrap_or_else(|error| panic!("exact upstream slicing fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual);
    assert_eq!(result.actual.len(), 12);
}

#[test]
fn dynamic_indices_keep_a_typed_index_error_application_precondition() {
    let verification = verify(
        r#"def list_value(index: int) -> int:
    values = [10, 20, 30]
    return values[index]

def bytes_value(index: int) -> int:
    values = b'123'
    return values[index]

def range_value(index: int) -> int:
    values = range(3, 6)
    return values[index]
"#,
    );

    assert!(!verification.passed, "{verification:#?}");
    let index_guards = verification
        .obligations
        .iter()
        .filter(|obligation| {
            obligation
                .id
                .contains(":application-precondition:IndexError:")
        })
        .collect::<Vec<_>>();
    assert_eq!(index_guards.len(), 3, "{verification:#?}");
    assert!(
        index_guards
            .iter()
            .all(|obligation| obligation.status == ObligationStatus::Refuted),
        "{verification:#?}"
    );
}

#[test]
fn toseq_preserves_concrete_sequence_values_and_shadowing_fails_closed() {
    let verification = verify(
        r#"def run() -> None:
    values = [1, 2, 3]
    pair = (1, 2, 3)
    data = b'123'
    numbers = range(1, 4)
    assert ToSeq(values) == [1, 2, 3]
    assert ToSeq(pair) == [1, 2, 3]
    assert ToSeq(data) == [49, 50, 51]
    assert ToSeq(numbers) == [1, 2, 3]
"#,
    );
    assert!(verification.passed, "{verification:#?}");

    let shadowed =
        refuse("def run(ToSeq: int) -> None:\n    values = [1, 2, 3]\n    copy = ToSeq(values)\n");
    assert_eq!(
        shadowed.code, "frontend.python.heap.expression-unsupported",
        "{shadowed:#?}"
    );

    let heterogeneous =
        refuse("def run() -> None:\n    pair = (1, True)\n    values = ToSeq(pair)\n");
    assert_eq!(
        heterogeneous.code, "frontend.python.heap.toseq-heterogeneous-tuple",
        "{heterogeneous:#?}"
    );
}
