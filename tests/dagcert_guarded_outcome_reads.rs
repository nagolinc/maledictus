//! A guard may suppress an unevaluated field read; it may never create ownership for a read.

use std::fs;

use maledictus::fragments::DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS;
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofResponse, ProofStatus, SourceFile};

fn verify(predicate: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    let source = format!(
        r#"from dataclasses import dataclass
from dagcert.runtime import operation
from nagini_contracts.contracts import Ensures, ResultT

@dataclass(frozen=True)
class Request:
    active: bool

@dataclass(frozen=True)
class Completed:
    value: int

@dataclass(frozen=True)
class Idle:
    reason: str

@operation
def work(request: Request) -> Completed | Idle:
    Ensures({predicate})
    if request.active:
        return Completed(3)
    return Idle("idle")
"#
    );
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
        python_callable_bindings: Vec::new(),
        embedded_external_calls: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

fn assert_proved(response: &ProofResponse) {
    assert!(matches!(response.status, ProofStatus::Proved), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some(DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS),
        "{response:#?}"
    );
    assert!(response.obligations.iter().all(|item| item.satisfied()), "{response:#?}");
}

fn assert_unowned_read_refuted(response: &ProofResponse) {
    assert!(!matches!(response.status, ProofStatus::Proved), "{response:#?}");
    assert!(
        response.obligations.iter().any(|item| item.id.contains("permission") && !item.satisfied()),
        "A tautology cannot hide an executed read of an absent/unowned field: {response:#?}"
    );
}

#[test]
fn inactive_outcome_field_is_not_read_by_short_circuit_or() {
    assert_proved(&verify(
        "not isinstance(ResultT(Completed), Completed) or ResultT(Completed).value == 3",
    ));
}

#[test]
fn executed_absent_field_is_not_owned_just_because_predicate_is_tautological() {
    assert_unowned_read_refuted(&verify(
        "ResultT(Completed).value == ResultT(Completed).value",
    ));
}

#[test]
fn wrong_outcome_guard_does_not_grant_other_class_field_permission() {
    assert_unowned_read_refuted(&verify(
        "not isinstance(ResultT(Idle), Idle) or ResultT(Completed).value == ResultT(Completed).value",
    ));
}

#[test]
fn false_predicate_on_an_owned_active_outcome_is_refuted() {
    let response = verify(
        "not isinstance(ResultT(Completed), Completed) or ResultT(Completed).value == 4",
    );
    assert!(!matches!(response.status, ProofStatus::Proved), "{response:#?}");
    assert!(
        response.obligations.iter().any(|item| item.id.contains(":postcondition:") && !item.satisfied()),
        "The actual false value predicate must be refuted: {response:#?}"
    );
    assert!(
        response.obligations.iter().filter(|item| item.id.contains("permission")).all(|item| item.satisfied()),
        "An inactive field access must not be diagnosed as executed: {response:#?}"
    );
}

#[test]
fn short_circuit_does_not_erase_an_unowned_read_in_its_first_operand() {
    assert_unowned_read_refuted(&verify(
        "ResultT(Completed).value == ResultT(Completed).value or True",
    ));
}

#[test]
fn conditional_expression_outcome_reads_remain_explicitly_refused() {
    // This change models Boolean short circuiting only. Conditional-expression permission
    // guards are not yet lowered, so their incomplete ownership proof must remain visible.
    let response = verify(
        "ResultT(Completed).value == 3 if isinstance(ResultT(Completed), Completed) else ResultT(Idle).reason == 'idle'",
    );
    assert!(matches!(response.status, ProofStatus::Refused), "{response:#?}");
    assert!(
        response.diagnostics.iter().any(|item| item.code == "frontend.python.heap.conditional-expression-reads-unsupported"),
        "Conditional field reads must retain their explicit unsupported diagnostic: {response:#?}"
    );
}
