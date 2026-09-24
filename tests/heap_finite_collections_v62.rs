use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_heap_contracts::verify_heap_module;

#[test]
fn exact_upstream_finite_collection_fixtures_match() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (fixture, expected_diagnostics) in [
        ("tests/functional/verification/test_dicts.py", 5),
        ("tests/functional/verification/test_set.py", 4),
        ("tests/functional/verification/test_boxing.py", 8),
    ] {
        let result = check_pinned_heap_fixture(
            &repository.join(".upstream/nagini"),
            &repository.join("conformance/nagini-v1.3.1.json"),
            fixture,
        )
        .unwrap_or_else(|error| panic!("exact upstream fixture {fixture} was refused: {error}"));

        assert!(result.passed, "{result:#?}");
        assert_eq!(result.expected, result.actual);
        assert_eq!(result.actual.len(), expected_diagnostics);
    }
}

#[test]
fn finite_collection_operations_preserve_exact_values() {
    let source = r#"from typing import Dict, Set

class Key:
    pass

class Value:
    pass

def run() -> None:
    key = Key()
    value = Value()
    mapping = {key: value}
    empty = {}  # type: Dict[Key, Value]
    assert key in mapping
    assert mapping[key] == value
    assert empty.get(key) == None
    empty[key] = value
    assert empty[key] == value
    values = {key}
    cleared: Set[Key] = set()
    assert key in values
    cleared.add(key)
    assert key in cleared
    cleared.clear()
    assert key not in cleared
"#;
    let verification = verify_heap_module(source, "finite_collections.py", &[])
        .unwrap_or_else(|failure| panic!("finite collection source refused: {failure:#?}"));
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn finite_collection_boundaries_fail_closed() {
    for (source, path, expected_code) in [
        (
            r#"class Key:
    def __hash__(self) -> int:
        return 1

def run() -> None:
    key = Key()
    values = {key}
"#,
            "custom_hash.py",
            "frontend.python.heap.collection-key-hooks-unsupported",
        ),
        (
            r#"class Key:
    def __eq__(self, other: 'Key') -> bool:
        return True

def run() -> None:
    key = Key()
    values = {key}
"#,
            "custom_eq.py",
            "frontend.python.heap.collection-key-hooks-unsupported",
        ),
        (
            r#"from typing import Set

def run(set: int) -> None:
    values: Set[int] = set()
"#,
            "shadowed_set.py",
            "frontend.python.heap.collection-builtin-shadowed",
        ),
        (
            r#"from typing import Set

def run() -> None:
    values: Set[int] = set()
    alias = values
    values.add(1)
"#,
            "aliased_set.py",
            "frontend.python.heap.set-mutation-alias-unsupported",
        ),
        (
            r#"from typing import Dict

def run() -> None:
    values = {1: 2}
    alias = values
    values[2] = 3
"#,
            "aliased_dict.py",
            "frontend.python.heap.dict-mutation-alias-unsupported",
        ),
        (
            r#"class Key:
    pass

def run() -> None:
    values = {Key()}
"#,
            "set_constructor_element.py",
            "frontend.python.heap.collection-key-evaluation-unsupported",
        ),
        (
            r#"from typing import Set

def run() -> None:
    values: Set[int] = set()
    values.pop()
"#,
            "unmodeled_set_method.py",
            "frontend.python.heap.set-method-unsupported",
        ),
    ] {
        let failure = verify_heap_module(source, path, &[])
            .expect_err("unsupported finite collection semantics must refuse");
        assert_eq!(failure.code, expected_code, "{path}: {failure:#?}");
    }
}

#[test]
fn missing_dictionary_subscript_is_a_keyerror_obligation() {
    let verification = verify_heap_module(
        "def run() -> None:\n    values = {1: 2}\n    assert values[3] == 2\n",
        "missing_dict_key.py",
        &[],
    )
    .expect("a real KeyError path is a failed proof obligation, not a structural refusal");
    assert!(!verification.passed, "{verification:#?}");
    assert!(verification.obligations.iter().any(|item| {
        item.id.contains("application-precondition:KeyError") && !item.satisfied()
    }));
}
