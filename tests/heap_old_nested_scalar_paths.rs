use std::fs;

use maledictus::fragments::DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS;
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofResponse, ProofStatus, SourceFile};
use maledictus::python_heap_contracts::verify_heap_module;

const RECORDS: &str = r#"from dataclasses import dataclass
from nagini_contracts.contracts import Ensures, Old, ResultT

@dataclass(frozen=True)
class Turn:
    id: int

@dataclass(frozen=True)
class Narration:
    turn: Turn

@dataclass(frozen=True)
class Request:
    narration: Narration

@dataclass(frozen=True)
class Published:
    turn_id: int

@dataclass(frozen=True)
class Failed:
    error: int
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

fn operation(body: &str, predicate: &str) -> String {
    format!(
        "from dagcert.runtime import operation\n{RECORDS}\n@operation\ndef work(request: Request) -> Published | Failed:\n    Ensures(not isinstance(ResultT(Published), Published) or ({predicate}))\n{body}\n"
    )
}

fn proved(response: &ProofResponse) {
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some(DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS),
        "{response:#?}"
    );
}

fn refuted(response: &ProofResponse) {
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|item| item.id.contains(":postcondition:") && !item.satisfied()),
        "{response:#?}"
    );
}

#[test]
fn nested_integer_snapshot_proves_and_off_by_one_is_semantically_refuted() {
    let body = "    return Published(request.narration.turn.id)";
    proved(&verify(&operation(
        body,
        "ResultT(Published).turn_id == Old(request.narration.turn.id)",
    )));
    refuted(&verify(&operation(
        body,
        "ResultT(Published).turn_id == Old(request.narration.turn.id) + 1",
    )));
}

#[test]
fn nested_boolean_snapshot_preserves_the_boolean_sort() {
    let source = operation(
        "    return Published(request.narration.turn.id)",
        "ResultT(Published).turn_id == Old(request.narration.turn.id)",
    )
    .replace("id: int", "id: bool");
    proved(&verify(&source));
    refuted(&verify(&source.replace(" == Old", " != Old")));
}

#[test]
fn rebinding_the_input_does_not_change_the_entry_snapshot_root() {
    let body = "    before = request.narration.turn.id\n    request = Request(Narration(Turn(before + 1)))\n    return Published(before)";
    // Closed operation locals are single-assignment. Do not broaden that
    // admission rule just to test the shared heap snapshot implementation.
    let closed = verify(&operation(
        body,
        "ResultT(Published).turn_id == Old(request.narration.turn.id)",
    ));
    assert!(matches!(closed.status, ProofStatus::Refused), "{closed:#?}");
    assert!(
        closed.diagnostics.iter().any(|diagnostic| diagnostic.code
            == "frontend.python.dagcert.local-binding-shadowed-or-mutated"),
        "{closed:#?}"
    );

    // Ordinary heap code may rebind a local. Isolate that entry-binding behavior
    // with a direct scalar field and explicit ownership: nested frozen reads
    // themselves are exercised above through the actual closed-operation path.
    let source = format!(
        "{RECORDS}\nfrom nagini_contracts.contracts import Requires, Acc\n\ndef work(request: Turn) -> Published:\n    Requires(Acc(request.id))\n    Ensures(ResultT(Published).turn_id == Old(request.id))\n    before = request.id\n    request = Turn(before + 1)\n    return Published(before)\n"
    );
    let result = verify_heap_module(&source, "rebound_input.py", &["work".to_owned()]).unwrap();
    assert!(result.passed, "{result:#?}");
    let incorrect = source.replace("Published(before)", "Published(before + 1)");
    let result = verify_heap_module(&incorrect, "rebound_wrong.py", &["work".to_owned()]).unwrap();
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains(":postcondition:") && !item.satisfied()),
        "{result:#?}"
    );
}

#[test]
fn every_nested_old_hop_still_requires_entry_read_permission() {
    for (precondition, missing) in [
        ("", vec!["narration", "turn", "id"]),
        ("    Requires(Acc(request.narration))\n", vec!["turn", "id"]),
    ] {
        let source = format!(
            "{RECORDS}\nfrom nagini_contracts.contracts import Requires, Acc\n\ndef work(request: Request) -> Published:\n{precondition}    Ensures(Old(request.narration.turn.id) == Old(request.narration.turn.id))\n    return Published(0)\n"
        );
        let result =
            verify_heap_module(&source, "old_permissions.py", &["work".to_owned()]).unwrap();
        assert!(!result.passed, "{result:#?}");
        for field in missing {
            assert!(
                result.obligations.iter().any(|item| item
                    .id
                    .contains(&format!(":old-field-permission:{field}:"))
                    && !item.satisfied()),
                "missing permission for {field}: {result:#?}"
            );
        }
    }
}

#[test]
fn nested_old_does_not_assume_optional_or_mutable_record_paths() {
    let source = format!(
        "{RECORDS}\ndef work(request: Request) -> Published:\n    Ensures(Old(request.narration.turn.id) == 0)\n    return Published(0)\n"
    );
    for invalid in [
        source.replace("turn: Turn", "turn: Turn | None"),
        source.replace(
            "@dataclass(frozen=True)\nclass Narration",
            "@dataclass(frozen=False)\nclass Narration",
        ),
        source.replace("turn.id)", "turn)"),
    ] {
        let failure = verify_heap_module(&invalid, "invalid_snapshot.py", &["work".to_owned()])
            .expect_err(
                "nested snapshots must not erase optional, mutable, or reference distinctions",
            );
        assert_eq!(
            failure.code, "frontend.python.heap.old-expression-unsupported",
            "{failure:#?}"
        );
    }
}

#[test]
fn body_local_alias_is_not_invented_as_an_entry_state_local() {
    let source = format!(
        "{RECORDS}\ndef work(request: Request) -> Published:\n    Ensures(Old(local.narration.turn.id) == 0)\n    local = request\n    return Published(0)\n"
    );
    let failure = verify_heap_module(&source, "late_local.py", &["work".to_owned()])
        .expect_err("a local first assigned in the body has no entry binding");
    assert_eq!(
        failure.code, "frontend.python.heap.old-expression-unsupported",
        "{failure:#?}"
    );
}
