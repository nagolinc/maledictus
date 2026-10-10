//! Closed Dagcert value-record ownership must survive semantic proof lowering.

use std::fs;

use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofResponse, ProofStatus, SourceFile};

const LOCAL_RECORDS: &str = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Request:\n    value: int\n\n@dataclass(frozen=True)\nclass Completed:\n    value: int\n\n";

fn verify(source: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("worker.py"), source).unwrap();
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "worker.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["work".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        cross_language_bindings: Vec::new(),
        python_callable_bindings: Vec::new(),
        embedded_external_calls: Vec::new(),
    })
}

#[test]
fn local_frozen_input_snapshot_and_result_field_assertion_are_proved() {
    let source = format!(
        "{LOCAL_RECORDS}@operation\ndef work(request: Request) -> Completed:\n    before = request.value\n    result = Completed(request.value + 1)\n    assert result.value == before + 1\n    return result\n"
    );
    let result = verify(&source);
    assert!(matches!(result.status, ProofStatus::Proved), "{result:#?}");
    assert!(result.diagnostics.is_empty(), "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains(":assert:")),
        "The assertion must be discharged, not erased: {result:#?}"
    );
    assert!(result.obligations.iter().all(|item| item.satisfied()));
}

#[test]
fn false_postcondition_is_refuted_after_input_ownership_is_established() {
    let source = format!(
        "{LOCAL_RECORDS}@operation\ndef work(request: Request) -> Completed:\n    before = request.value\n    result = Completed(request.value + 1)\n    assert result.value == before + 2\n    return result\n"
    );
    let result = verify(&source);
    assert!(!matches!(result.status, ProofStatus::Proved), "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains(":assert:") && !item.satisfied()),
        "The false assertion itself must fail: {result:#?}"
    );
    assert!(
        result
            .obligations
            .iter()
            .filter(|item| item.id.contains("permission"))
            .all(|item| item.satisfied()),
        "Input reads must no longer be the failure: {result:#?}"
    );
}

#[test]
fn local_nested_frozen_records_receive_only_readable_value_projections() {
    let source = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Inner:\n    value: int\n\n@dataclass(frozen=True)\nclass Request:\n    inner: Inner\n\n@dataclass(frozen=True)\nclass Completed:\n    value: int\n\n@operation\ndef work(request: Request) -> Completed:\n    inner = request.inner\n    before = inner.value\n    result = Completed(before + 1)\n    assert result.value == before + 1\n    return result\n";
    let result = verify(source);
    assert!(matches!(result.status, ProofStatus::Proved), "{result:#?}");
    assert!(result.obligations.iter().all(|item| item.satisfied()));
}

#[test]
fn aliasing_an_immutable_input_preserves_its_read_access() {
    let source = format!(
        "{LOCAL_RECORDS}@operation\ndef work(request: Request) -> Completed:\n    alias = request\n    before = alias.value\n    result = Completed(before + 1)\n    assert result.value == before + 1\n    return result\n"
    );
    let result = verify(&source);
    assert!(matches!(result.status, ProofStatus::Proved), "{result:#?}");
}

#[test]
fn ordinary_heap_entry_does_not_invent_local_record_permissions() {
    let source = "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Request:\n    value: int\n\ndef read(request: Request) -> None:\n    value: int = request.value\n    assert value == value\n";
    let result = maledictus::python_heap_contracts::verify_heap_module(
        source,
        "ordinary.py",
        &["read".to_owned()],
    )
    .unwrap();
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains("permission") && !item.satisfied())
    );
}

#[test]
fn ordinary_mutable_record_does_not_receive_input_ownership() {
    let source = "class Mutable:\n    value: int\n\ndef read(request: Mutable) -> None:\n    value: int = request.value\n    assert value == value\n";
    let result = maledictus::python_heap_contracts::verify_heap_module(
        source,
        "mutable.py",
        &["read".to_owned()],
    )
    .unwrap();
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains("permission") && !item.satisfied())
    );
}

#[test]
fn closed_record_reads_do_not_authorize_writing_frozen_input_fields() {
    let source = format!(
        "{LOCAL_RECORDS}@operation\ndef work(request: Request) -> Completed:\n    request.value = 0\n    result = Completed(request.value)\n    assert result.value == 0\n    return result\n"
    );
    let result = verify(&source);
    assert!(!matches!(result.status, ProofStatus::Proved), "{result:#?}");
    assert!(!result.diagnostics.is_empty(), "{result:#?}");
}

#[test]
fn distinct_projection_annotations_do_not_bypass_strict_python_typechecking() {
    let source = format!(
        "{LOCAL_RECORDS}from nagini_contracts.contracts import Ensures, ResultT\n\n@dataclass(frozen=True)\nclass Idle:\n    value: int\n\n@operation\ndef work(request: Request) -> Completed | Idle:\n    Ensures(ResultT(Completed) is ResultT(Idle))\n    return Completed(request.value)\n"
    );
    let result = verify(&source);
    assert!(!matches!(result.status, ProofStatus::Proved), "{result:#?}");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|item| { item.code == "frontend.python.typecheck.comparison-overlap" }),
        "The full protocol must retain strict mypy's refusal: {result:#?}"
    );
}

#[test]
fn typed_result_cannot_reinterpret_a_field_with_another_scalar_sort() {
    let source = format!(
        "{LOCAL_RECORDS}from nagini_contracts.contracts import Ensures, ResultT\n\n@dataclass(frozen=True)\nclass Idle:\n    value: str\n\n@operation\ndef work(request: Request) -> Completed | Idle:\n    Ensures(ResultT(Completed).value == ResultT(Idle).value)\n    return Completed(request.value)\n"
    );
    let result = verify(&source);
    assert!(!matches!(result.status, ProofStatus::Proved), "{result:#?}");
    assert!(!result.diagnostics.is_empty(), "{result:#?}");
}

fn verify_absent_completed_field_predicate(predicate: &str) -> ProofResponse {
    let source = format!(
        "{LOCAL_RECORDS}from nagini_contracts.contracts import Ensures, ResultT\n\n@dataclass(frozen=True)\nclass Idle:\n    reason: str\n\n@operation\ndef work(request: Request) -> Completed | Idle:\n    Ensures({predicate})\n    return Idle('idle')\n"
    );
    verify(&source)
}

#[test]
fn postcondition_short_circuit_read_guards_match_the_complete_boolean_truth_table() {
    for (operator, is_and) in [("and", true), ("or", false)] {
        for first in [false, true] {
            for second in [false, true] {
                let first_literal = if first { "True" } else { "False" };
                let second_literal = if second { "True" } else { "False" };
                let predicate = format!(
                    "{first_literal} {operator} {second_literal} {operator} (ResultT(Completed).value == ResultT(Completed).value)"
                );
                let result = verify_absent_completed_field_predicate(&predicate);
                assert!(!result.obligations.is_empty(), "{predicate}: {result:#?}");
                let evaluated = if is_and {
                    first && second
                } else {
                    !first && !second
                };
                let read_failed = result
                    .obligations
                    .iter()
                    .any(|item| item.id.contains("permission:value:") && !item.satisfied());
                assert_eq!(read_failed, evaluated, "{predicate}: {result:#?}");
                assert_eq!(
                    matches!(result.status, ProofStatus::Proved),
                    !is_and && !evaluated,
                    "{predicate}: {result:#?}",
                );
            }
        }
    }
}

#[test]
fn a_short_circuit_guard_must_itself_have_permission_to_read_its_field() {
    let result = verify_absent_completed_field_predicate("ResultT(Completed).value == 0 or True");
    assert!(!matches!(result.status, ProofStatus::Proved), "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| { item.id.contains("permission:value:") && !item.satisfied() }),
        "A later true operand must not hide the guard's unowned read: {result:#?}"
    );
}
