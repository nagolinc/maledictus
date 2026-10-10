use std::fs;

use maledictus::dagcert_operations::verify_operation_module;
use maledictus::fragments::DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS;
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofResponse, ProofStatus, SourceFile};
use maledictus::python_heap_contracts::verify_heap_module;

fn verify_operation(source: &str) -> ProofResponse {
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

fn truth_source(annotation: &str, truth: &str, equality: &str) -> String {
    format!(
        r#"from __future__ import annotations
from dataclasses import dataclass
from dagcert.runtime import operation
from nagini_contracts.contracts import Ensures, Old, ResultT

@dataclass(frozen=True)
class Request:
    value: {annotation}

@dataclass(frozen=True)
class Completed:
    active: bool

@operation
def work(request: Request) -> Completed:
    Ensures(ResultT(Completed).active {equality} ({truth}))
    if request.value:
        return Completed(True)
    return Completed(False)
"#
    )
}

fn length_truth_source(annotation: &str, equality: &str) -> String {
    // The operation compares truthiness with the length of the same immutable
    // input. Record that scalar projection in the result: whole-value Old(bytes)
    // and Old(tuple) are a separate, unsupported snapshot feature.
    truth_source(annotation, "ResultT(Completed).size > 0", equality)
        .replace("    active: bool", "    active: bool\n    size: int")
        .replace("Completed(True)", "Completed(True, len(request.value))")
        .replace("Completed(False)", "Completed(False, len(request.value))")
}

#[test]
fn builtin_lengths_stay_inside_the_closed_operation_frontend() {
    for annotation in ["str", "bytes", "tuple[int, ...]"] {
        let source = length_truth_source(annotation, "==");
        let result = verify_operation_module(&source, "length.py", &["work".to_owned()])
            .unwrap_or_else(|error| panic!("{annotation}: {error:#?}"));
        assert_eq!(result.operations, ["work"]);
    }
}

#[test]
fn local_variadic_tuple_fields_preserve_immutable_element_sorts() {
    for annotation in [
        "tuple[int, ...]",
        "tuple[bytes, ...]",
        "tuple[tuple[str, ...], ...]",
    ] {
        let source = format!(
            "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Request:\n    value: {annotation}\n"
        );
        let result = verify_heap_module(&source, "immutable_tuple.py", &[])
            .unwrap_or_else(|error| panic!("{annotation}: {error:#?}"));
        assert!(result.passed, "{annotation}: {result:#?}");
    }
    for annotation in [
        "tuple[object, ...]",
        "tuple[list[int], ...]",
        "tuple[Request, ...]",
    ] {
        let source = format!(
            "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Request:\n    value: {annotation}\n"
        );
        assert!(
            verify_heap_module(&source, "identity_tuple.py", &[]).is_err(),
            "{annotation}: tuple values must not erase mutable or nominal element identity"
        );
    }
}

#[test]
fn builtin_length_does_not_hide_invalid_arguments_or_shadowed_bindings() {
    let source = length_truth_source("bytes", "==");
    for expression in [
        "len()",
        "len(request.value, request.value)",
        "len(value=request.value)",
    ] {
        let invalid = source.replace("len(request.value)", expression);
        let failure = verify_operation_module(&invalid, "length_shape.py", &["work".to_owned()])
            .expect_err("builtin len has one positional argument");
        assert_eq!(
            failure.code,
            "frontend.python.dagcert.len-call-shape-unsupported"
        );
    }
    let invalid = source.replace("len(request.value)", "len(request)");
    let failure = verify_operation_module(&invalid, "object_length.py", &["work".to_owned()])
        .expect_err("a nominal object's __len__ is not assumed total");
    assert_eq!(
        failure.code,
        "frontend.python.dagcert.len-argument-unsupported"
    );
    for invalid in [
        source.replace("request", "len"),
        source.replace(
            "    if request.value:",
            "    len = 0\n    if request.value:",
        ),
    ] {
        assert!(
            verify_operation_module(&invalid, "local_length.py", &["work".to_owned()]).is_err()
        );
    }
    let shadowed_module = format!(
        "{source}\n@operation\ndef len(request: Request) -> Completed:\n    return Completed(False, 0)\n"
    );
    let failure =
        verify_operation_module(&shadowed_module, "shadowed_length.py", &["work".to_owned()])
            .expect_err("a source operation named len is not the builtin");
    assert_eq!(
        failure.code,
        "frontend.python.dagcert.builtin-binding-shadowed"
    );
}

#[test]
fn constructor_argument_length_still_requires_permission_to_read_its_input() {
    let source = r#"from dataclasses import dataclass

@dataclass(frozen=True)
class Request:
    value: bytes

@dataclass(frozen=True)
class Completed:
    size: int

def work(request: Request) -> Completed:
    return Completed(len(request.value))
"#;
    let result = verify_heap_module(source, "unowned_length.py", &["work".to_owned()]).unwrap();
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains("permission:value:") && !item.satisfied()),
        "Pure len must not erase the field permission needed to evaluate its argument: {result:#?}"
    );
}

#[test]
fn builtin_field_truthiness_is_proved_with_actual_zero_and_length_semantics() {
    for (annotation, source) in [
        ("bool", truth_source("bool", "Old(request.value)", "==")),
        ("int", truth_source("int", "Old(request.value) != 0", "==")),
        (
            "str",
            truth_source("str", "len(Old(request.value)) > 0", "=="),
        ),
        ("bytes", length_truth_source("bytes", "==")),
        (
            "tuple[int, ...]",
            length_truth_source("tuple[int, ...]", "=="),
        ),
    ] {
        let response = verify_operation(&source);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{annotation}: {response:#?}"
        );
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some(DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS),
            "{annotation}: {response:#?}"
        );
        assert!(
            response.obligations.iter().all(|item| item.satisfied()),
            "{response:#?}"
        );
    }
}

#[test]
fn the_opposite_truthiness_postcondition_is_semantically_refuted() {
    for (annotation, source) in [
        ("int", truth_source("int", "Old(request.value) != 0", "!=")),
        (
            "str",
            truth_source("str", "len(Old(request.value)) > 0", "!="),
        ),
        ("bytes", length_truth_source("bytes", "!=")),
        (
            "tuple[int, ...]",
            length_truth_source("tuple[int, ...]", "!="),
        ),
    ] {
        let response = verify_operation(&source);
        assert!(
            matches!(response.status, ProofStatus::Refuted),
            "{annotation}: {response:#?}"
        );
        assert!(
            response
                .obligations
                .iter()
                .any(|item| item.id.contains(":postcondition:") && !item.satisfied()),
            "{annotation}: {response:#?}"
        );
    }
}

#[test]
fn operation_truthiness_does_not_assume_object_truth_hooks_are_total() {
    let source = truth_source("int", "Old(request.value) != 0", "==")
        .replace("if request.value:", "if request:");
    let failure = verify_operation_module(&source, "object_condition.py", &["work".to_owned()])
        .expect_err("a nominal record is not a builtin truthiness type");
    assert_eq!(
        failure.code,
        "frontend.python.dagcert.condition-type-mismatch"
    );
}

#[test]
fn none_is_a_false_builtin_condition_without_external_effects() {
    let source = truth_source("int", "False", "==").replace("if request.value:", "if None:");
    let response = verify_operation(&source);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some(DAGCERT_TYPED_OPERATIONS_WITH_SEMANTIC_POSTCONDITIONS)
    );
}

#[test]
fn canonical_future_annotations_does_not_hide_heap_postconditions() {
    let source = r#"from __future__ import annotations
from dataclasses import dataclass
from nagini_contracts.contracts import Ensures, ResultT

@dataclass(frozen=True)
class Completed:
    value: int

def work() -> Completed:
    Ensures(ResultT(Completed).value == 7)
    return Completed(7)
"#;
    let result = verify_heap_module(source, "future_annotations.py", &[]).unwrap();
    assert!(result.passed, "{result:#?}");
    let false_source = source.replace("value == 7", "value == 8");
    let result = verify_heap_module(&false_source, "future_annotations_false.py", &[]).unwrap();
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains(":postcondition:") && !item.satisfied())
    );
}

#[test]
fn unrelated_future_features_are_not_silently_accepted_as_annotations() {
    for import in [
        "from __future__ import annotations as ignored",
        "from __future__ import unrecognized_feature",
    ] {
        let source = format!("{import}\nclass Record:\n    value: int\n");
        let failure = verify_heap_module(&source, "future_not_annotations.py", &[])
            .expect_err("only the canonical postponed-annotation feature is modeled");
        assert_eq!(
            failure.code, "frontend.python.heap.future-import-unsupported",
            "{failure:#?}"
        );
    }
}
