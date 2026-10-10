use maledictus::python_heap_contracts::verify_heap_module;

const PRELUDE: &str = r#"from __future__ import annotations
from typing import TYPE_CHECKING
from dataclasses import dataclass
from nagini_contracts.contracts import Ensures, ResultT
"#;

const BODY: &str = r#"
@dataclass(frozen=True)
class Completed:
    value: int

def work() -> Completed:
    Ensures(ResultT(Completed).value == 7)
    return Completed(7)
"#;

#[test]
fn canonical_type_only_import_is_not_executed_or_required_as_runtime_provider() {
    let source = format!(
        "{PRELUDE}\nif TYPE_CHECKING:\n    from unavailable_at_runtime import TypeOnly\n{BODY}"
    );
    let result = verify_heap_module(&source, "type_only.py", &["work".to_owned()]).unwrap();
    assert!(result.passed, "{result:#?}");
    let false_source = source.replace("value == 7", "value == 8");
    let result =
        verify_heap_module(&false_source, "type_only_false.py", &["work".to_owned()]).unwrap();
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains(":postcondition:") && !item.satisfied())
    );
}

#[test]
fn runtime_else_branch_is_not_erased_with_the_type_only_branch() {
    let source = format!(
        "{PRELUDE}\nif TYPE_CHECKING:\n    from unavailable_at_runtime import TypeOnly\nelse:\n    assert False\n{BODY}"
    );
    let result = verify_heap_module(&source, "runtime_else.py", &["work".to_owned()]).unwrap();
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains("module:assert:") && !item.satisfied())
    );
}

#[test]
fn type_checking_rebinding_cannot_turn_runtime_effects_into_metadata() {
    for rebinding in [
        "TYPE_CHECKING = True",
        "from another_provider import TYPE_CHECKING",
        "from another_provider import *",
        "def change() -> None:\n    global TYPE_CHECKING\n    TYPE_CHECKING = True",
    ] {
        let source = format!(
            "{PRELUDE}\n{rebinding}\nif TYPE_CHECKING:\n    from unavailable_at_runtime import TypeOnly\n{BODY}"
        );
        let error = verify_heap_module(&source, "rebound.py", &["work".to_owned()]).unwrap_err();
        assert_eq!(
            error.code, "frontend.python.heap.type-checking-binding-reassigned",
            "{error:#?}"
        );
    }
}

#[test]
fn unknown_guards_and_arbitrary_guarded_statements_are_not_silently_erased() {
    let missing = format!("if TYPE_CHECKING:\n    import another_provider\n{PRELUDE}{BODY}");
    let error = verify_heap_module(&missing, "missing_guard.py", &["work".to_owned()]).unwrap_err();
    assert_eq!(
        error.code,
        "frontend.python.heap.type-checking-binding-unresolved"
    );
    for statement in ["perform_effect()", "raise ValueError()", "value = 1"] {
        let source = format!("{PRELUDE}\nif TYPE_CHECKING:\n    {statement}\n{BODY}");
        let error =
            verify_heap_module(&source, "guarded_effect.py", &["work".to_owned()]).unwrap_err();
        assert_eq!(
            error.code, "frontend.python.heap.type-checking-body-unsupported",
            "{error:#?}"
        );
    }
}

#[test]
fn type_only_import_does_not_create_runtime_binding_or_erase_unresolved_annotation() {
    let source = format!(
        "{PRELUDE}\nif TYPE_CHECKING:\n    from unavailable_at_runtime import TypeOnly\n{BODY}"
    );
    for invalid in [
        source.replace("return Completed(7)", "return TypeOnly(7)"),
        source.replace("def work()", "def work(value: TypeOnly)"),
    ] {
        match verify_heap_module(&invalid, "type_only_use.py", &["work".to_owned()]) {
            Ok(result) => assert!(!result.passed, "{result:#?}"),
            Err(error) => assert!(!error.message.is_empty()),
        }
    }
}

#[test]
fn recursive_json_alias_has_its_own_source_located_refusal() {
    let source = "from typing import TypedDict\n\nJSONValue = bool | int | float | str | None | list[\"JSONValue\"] | dict[str, \"JSONValue\"]\n";
    let error = verify_heap_module(source, "configuration.py", &[]).unwrap_err();
    assert_eq!(
        error.code,
        "frontend.python.heap.recursive-type-alias-unsupported"
    );
    assert!(error.message.contains("configuration.py:3:1"), "{error:#?}");
    assert!(error.message.contains("JSONValue"), "{error:#?}");
}

#[test]
fn alias_lookalike_runtime_calls_are_not_discarded_as_type_declarations() {
    let source = format!("{PRELUDE}\nJSONValue = make_value() | list[\"JSONValue\"]\n{BODY}");
    match verify_heap_module(&source, "runtime_alias.py", &["work".to_owned()]) {
        Ok(result) => assert!(
            !result.passed,
            "An executed unknown call must not disappear: {result:#?}"
        ),
        Err(error) => assert_ne!(
            error.code,
            "frontend.python.heap.recursive-type-alias-unsupported"
        ),
    }
}
