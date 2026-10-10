use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

const RECORDS: &str = r#"from dataclasses import dataclass
from nagini_contracts.contracts import Ensures, ResultT

@dataclass(frozen=True)
class Completed:
    values: list[int]
"#;

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| panic!("{path}: {failure:#?}"))
}

fn assert_heap_alias_refused(source: &str, path: &str) {
    let failure = verify_heap_module(source, path, &[])
        .expect_err("shared list mutation must not be treated as a local value replacement");
    assert_eq!(
        failure.code, "frontend.python.heap.list-mutation-heap-alias-unsupported",
        "{path}: {failure:#?}"
    );
}

#[test]
fn a_returned_record_cannot_snapshot_an_aliased_list_before_cleanup() {
    // Python returns a reference to the same list. Its actual length is two both before a
    // normal return and after finally. This fragment must explicitly refuse both claims
    // until it models the heap update, never prove the false pre-mutation length of one.
    for cleanup in [false, true] {
        for claimed_length in [1, 2] {
            let body = if cleanup {
                "    try:\n        return returned\n    finally:\n        values.append(2)\n"
            } else {
                "    values.append(2)\n    return returned\n"
            };
            let source = format!(
                "{RECORDS}\ndef run() -> Completed:\n    Ensures(len(ResultT(Completed).values) == {claimed_length})\n    values = [1]\n    returned = Completed(values)\n{body}"
            );
            assert_heap_alias_refused(&source, "record_list_final_return.py");
        }
    }
}

#[test]
fn every_supported_local_list_mutation_checks_heap_capture() {
    for mutation in [
        "values.append(2)",
        "list.append(values, 2)",
        "values.extend(extra)",
        "values[0] = 2",
    ] {
        let source = format!(
            "{RECORDS}\ndef run() -> None:\n    values = [1]\n    extra = [2]\n    returned = Completed(values)\n    {mutation}\n"
        );
        assert_heap_alias_refused(&source, "record_list_mutation.py");
    }
}

#[test]
fn hiding_the_record_inside_another_record_does_not_erase_the_capture() {
    let source = format!(
        "{RECORDS}\n@dataclass(frozen=True)\nclass Envelope:\n    item: Completed\n\ndef run() -> None:\n    values = [1]\n    inner = Completed(values)\n    outer = Envelope(inner)\n    inner = Completed([9])\n    values.append(2)\n"
    );
    assert_heap_alias_refused(&source, "nested_record_list_alias.py");
}

#[test]
fn mutation_before_record_construction_preserves_the_final_contents() {
    let source = format!(
        "{RECORDS}\ndef run() -> Completed:\n    Ensures(len(ResultT(Completed).values) == 2)\n    values = [1]\n    values.append(2)\n    return Completed(values)\n"
    );
    let result = verify(&source, "record_after_list_mutation.py");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn immutable_record_reads_without_mutation_remain_proved() {
    let source = format!(
        "{RECORDS}\ndef run() -> Completed:\n    Ensures(len(ResultT(Completed).values) == 1)\n    values = [1]\n    returned = Completed(values)\n    return returned\n"
    );
    let result = verify(&source, "record_list_read.py");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn independent_local_copies_keep_their_separate_allocation_identity() {
    let source = r#"def run() -> None:
    values = [1]
    copied = list(values)
    values.append(2)
    copied[0] = 3
    assert len(values) == 2
    assert values[0] == 1
    assert len(copied) == 1
    assert copied[0] == 3
"#;
    let result = verify(source, "independent_local_list_copies.py");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn a_scalar_record_snapshot_does_not_alias_the_list() {
    let source = r#"from dataclasses import dataclass

@dataclass(frozen=True)
class Count:
    value: int

def run() -> None:
    values = [1]
    count = Count(len(values))
    values.append(2)
    assert count.value == 1
    assert len(values) == 2
"#;
    let result = verify(source, "record_scalar_snapshot.py");
    assert!(result.passed, "{result:#?}");
}
