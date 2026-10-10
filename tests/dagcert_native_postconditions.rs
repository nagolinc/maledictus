//! Source postconditions must be proved jointly with the closed operation boundary.

use std::fs;

use maledictus::dagcert_operations::verify_operation_module;
use maledictus::fragments::{
    DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_ASSERTIONS,
    DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofResponse, ProofStatus, SourceFile};

const RECORDS: &str = r#"from dataclasses import dataclass
from dagcert.runtime import operation

@dataclass(frozen=True)
class Request:
    active: bool
    value: int

@dataclass(frozen=True)
class Completed:
    value: int

@dataclass(frozen=True)
class Idle:
    value: int

"#;

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
        python_callable_bindings: Vec::new(),
        embedded_external_calls: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

fn assert_proved(response: &ProofResponse, fragment: &str) {
    assert!(matches!(response.status, ProofStatus::Proved), "{response:#?}");
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(response.files.len(), 1, "{response:#?}");
    assert_eq!(response.files[0].fragment.as_deref(), Some(fragment), "{response:#?}");
    assert!(!response.obligations.is_empty(), "{response:#?}");
    assert!(response.obligations.iter().all(|item| item.satisfied()), "{response:#?}");
}

fn assert_semantically_refuted(response: &ProofResponse, obligation: &str) {
    assert!(!matches!(response.status, ProofStatus::Proved), "{response:#?}");
    assert!(
        response.obligations.iter().any(|item| item.id.contains(obligation) && !item.satisfied()),
        "The predicate must fail in the semantic proof, not merely in frontend admission: {response:#?}"
    );
}

fn union_source(idle_delta: i32) -> String {
    format!(
        r#"{RECORDS}from nagini_contracts.contracts import Ensures, Old, ResultT

@operation
def work(request: Request) -> Completed | Idle:
    Ensures(not isinstance(ResultT(Completed), Completed) or ResultT(Completed).value == Old(request.value))
    Ensures(not isinstance(ResultT(Idle), Idle) or ResultT(Idle).value == Old(request.value) + {idle_delta})
    if request.active:
        return Completed(request.value)
    return Idle(request.value + 1)
"#
    )
}

#[test]
fn native_postcondition_is_proved_and_false_version_is_refuted() {
    let source = format!(
        r#"{RECORDS}from nagini_contracts.contracts import Ensures, Old, ResultT

@operation
def work(request: Request) -> Completed:
    Ensures(ResultT(Completed).value == Old(request.value) + 1)
    before = request.value
    result = Completed(request.value + 1)
    assert result.value == before + 1
    return result
"#
    );
    assert_proved(&verify(&source), DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS);
    let false_source = source.replace(
        "ResultT(Completed).value == Old(request.value) + 1",
        "ResultT(Completed).value == Old(request.value) + 2",
    );
    assert_semantically_refuted(&verify(&false_source), ":postcondition:");
}

#[test]
fn native_union_postconditions_preserve_one_actual_return_reference() {
    let response = verify(&union_source(1));
    assert_proved(&response, DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS);
    assert!(response.obligations.iter().any(|item| item.id.contains(":postcondition:")));
}

#[test]
fn false_same_named_field_on_other_outcome_is_refuted() {
    let response = verify(&union_source(0));
    assert_semantically_refuted(&response, ":postcondition:");
}

#[test]
fn false_success_outcome_is_not_hidden_by_union_projection() {
    let source = union_source(1).replace(
        "ResultT(Completed).value == Old(request.value)",
        "ResultT(Completed).value == Old(request.value) + 1",
    );
    assert_semantically_refuted(&verify(&source), ":postcondition:");
}

#[test]
fn guarded_union_postconditions_only_read_the_actual_outcome_fields() {
    let records = RECORDS.replace("class Idle:\n    value: int", "class Idle:\n    reason: str");
    let source = format!(
        r#"{records}from nagini_contracts.contracts import Ensures, Old, ResultT

@operation
def work(request: Request) -> Completed | Idle:
    Ensures(not isinstance(ResultT(Completed), Completed) or ResultT(Completed).value == Old(request.value))
    Ensures(not isinstance(ResultT(Idle), Idle) or ResultT(Idle).reason == "idle")
    if request.active:
        return Completed(request.value)
    return Idle("idle")
"#
    );
    assert_proved(&verify(&source), DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS);
    let false_source = source.replace("ResultT(Idle).reason == \"idle\"", "ResultT(Idle).reason == \"wrong\"");
    assert_semantically_refuted(&verify(&false_source), ":postcondition:");
}

#[test]
fn negative_cross_record_type_guard_is_semantic_not_frontend_nonoverlap() {
    let source = format!(
        r#"{RECORDS}@operation
def work(request: Request) -> Idle:
    result = Idle(request.value)
    assert not isinstance(result, Completed)
    return result
"#
    );
    assert_proved(&verify(&source), DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_ASSERTIONS);
    let false_source = source.replace("assert not isinstance", "assert isinstance");
    assert_semantically_refuted(&verify(&false_source), ":assert:");
}

#[test]
fn finally_overridden_outcome_is_the_postcondition_result() {
    let source = format!(
        r#"{RECORDS}from nagini_contracts.contracts import Ensures, ResultT

@operation
def work(request: Request) -> Completed | Idle:
    Ensures(isinstance(ResultT(Idle), Idle))
    Ensures(ResultT(Idle).value == 9)
    try:
        return Completed(3)
    finally:
        return Idle(9)
"#
    );
    assert_proved(&verify(&source), DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS);
    let false_source = source.replace(
        "Ensures(isinstance(ResultT(Idle), Idle))",
        "Ensures(isinstance(ResultT(Completed), Completed))",
    );
    assert_semantically_refuted(&verify(&false_source), ":postcondition:");
}

#[test]
fn postcondition_does_not_erase_missing_return_or_exception_paths() {
    for body in [
        "    if request.active:\n        return Completed(request.value)\n",
        "    converted = float(request.value)\n    return Completed(request.value)\n",
    ] {
        let source = format!(
            "{RECORDS}from nagini_contracts.contracts import Ensures\n\n@operation\ndef work(request: Request) -> Completed:\n    Ensures(True)\n{body}"
        );
        let error = verify_operation_module(&source, "worker.py", &["work".to_owned()]).unwrap_err();
        assert_eq!(error.code, "frontend.python.dagcert.operation-not-total", "{error:#?}");
        let response = verify(&source);
        assert!(
            response.files.iter().all(|file| file.fragment.as_deref() != Some(DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS)),
            "A weaker proof must never be advertised as jointly closed and postcondition-proved: {response:#?}"
        );
    }
}

#[test]
fn application_requires_cannot_vacuously_discharge_closed_postconditions() {
    let source = format!(
        "{RECORDS}from nagini_contracts.contracts import Ensures, Requires\n\n@operation\ndef work(request: Request) -> Completed:\n    Requires(False)\n    Ensures(False)\n    return Completed(request.value)\n"
    );
    let error = verify_operation_module(&source, "worker.py", &["work".to_owned()]).unwrap_err();
    assert_eq!(error.code, "frontend.python.dagcert.semantic-contract-import-unsupported");
    let response = verify(&source);
    assert!(response.files.iter().all(|file| file.fragment.as_deref() != Some(DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS)), "{response:#?}");
}

#[test]
fn canonical_contract_names_cannot_be_rebound_or_aliased() {
    let sources = [
        format!("{RECORDS}from nagini_contracts.contracts import Ensures as Guarantee\n\n@operation\ndef work(request: Request) -> Completed:\n    Guarantee(False)\n    return Completed(request.value)\n"),
        format!("{RECORDS}from nagini_contracts.contracts import Ensures\n\n@operation\ndef work(request: Request) -> Completed:\n    Ensures(False)\n    Ensures = request.active\n    return Completed(request.value)\n"),
        format!("{RECORDS}from nagini_contracts.contracts import Ensures\n\n@operation\ndef work(Ensures: Request) -> Completed:\n    return Completed(Ensures.value)\n"),
        format!("{RECORDS}from nagini_contracts.contracts import Ensures\n\n@operation\ndef work(request: Request) -> Completed:\n    Ensures(ResultT(Completed).value == request.value)\n    return Completed(request.value)\n"),
    ];
    for source in sources {
        assert!(
            verify_operation_module(&source, "worker.py", &["work".to_owned()]).is_err(),
            "noncanonical contract binding was admitted:\n{source}"
        );
    }
}

#[test]
fn nested_or_late_postcondition_is_not_erased_as_an_executable_statement() {
    for body in [
        "    if request.active:\n        Ensures(False)\n    return Completed(request.value)\n",
        "    value = request.value\n    Ensures(False)\n    return Completed(value)\n",
    ] {
        let source = format!("{RECORDS}from nagini_contracts.contracts import Ensures\n\n@operation\ndef work(request: Request) -> Completed:\n{body}");
        assert!(verify_operation_module(&source, "worker.py", &["work".to_owned()]).is_err());
    }
}

#[test]
fn inherited_or_overlapping_outcomes_are_not_assumed_disjoint() {
    let source = format!(
        r#"{RECORDS}@dataclass(frozen=True)
class Both(Completed, Idle):
    value: int

@operation
def work(request: Request) -> Completed | Idle:
    result = Both(request.value)
    assert not isinstance(result, Idle)
    return result
"#
    );
    // The closed record fragment currently refuses inheritance instead of treating nominal
    // non-overlap as a theorem. Supporting inheritance later must preserve this false guard.
    let error = verify_operation_module(&source, "worker.py", &["work".to_owned()]).unwrap_err();
    assert_eq!(error.code, "frontend.python.dagcert.record-shape-unsupported");
    let response = verify(&source);
    assert!(!matches!(response.status, ProofStatus::Proved), "{response:#?}");
}
