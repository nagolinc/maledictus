use maledictus::python_contracts::verify_contract_module;
use maledictus::python_heap_contracts::verify_heap_module;

#[test]
fn scalar_annotations_retain_nested_mutable_collection_sorts() {
    let source = r#"from nagini_contracts.contracts import *
from typing import List

def run() -> None:
    lists = []  # type: List[List[int]]
    assert len(lists) == 0
"#;

    let verification = verify_contract_module(source, "nested_collection_annotations.py", &[])
        .unwrap_or_else(|failure| panic!("nested annotations were refused: {failure:#?}"));
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn heap_literals_retain_nested_list_and_dictionary_values() {
    let source = r#"def run() -> None:
    inner = [1, 2]
    lists = [inner, [3, 4]]
    assert len(lists) == 2
    assert len(lists[0]) == 2
    first = {1: 10, 2: 20}
    dictionaries = {6: first, 7: {3: 30}}
    assert len(dictionaries) == 2
"#;

    let verification = verify_heap_module(source, "nested_collection_literals.py", &[])
        .unwrap_or_else(|failure| panic!("nested literals were refused: {failure:#?}"));
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn mutable_collections_remain_invalid_hash_keys_and_set_elements() {
    for (source, path) in [
        (
            "def run() -> None:\n    key = [1]\n    values = {key: 2}\n",
            "mutable_list_key.py",
        ),
        (
            "def run() -> None:\n    member = {1}\n    values = {member}\n",
            "mutable_set_member.py",
        ),
    ] {
        let failure = verify_heap_module(source, path, &[])
            .expect_err("mutable collection hashing must remain fail-closed");
        assert_eq!(
            failure.code, "frontend.python.heap.collection-key-unsupported",
            "{path}: {failure:#?}"
        );
    }
}

#[test]
fn nested_sequence_equality_is_precise_without_inventing_set_or_dict_equality() {
    let lists = verify_heap_module(
        "def run() -> None:\n    left = [[1], [2]]\n    right = [[1], [2]]\n    assert left == right\n",
        "nested_list_equality.py",
        &[],
    )
    .unwrap_or_else(|failure| panic!("nested list equality was refused: {failure:#?}"));
    assert!(lists.passed, "{lists:#?}");

    for (source, path, expected_message) in [
        (
            "def run() -> None:\n    left_value = {1}\n    right_value = {1}\n    left = [left_value]\n    right = [right_value]\n    assert left == right\n",
            "nested_set_equality.py",
            "list equality over nested Set(Int)",
        ),
        (
            "def run() -> None:\n    left_value = {1: 2}\n    right_value = {1: 2}\n    left = [left_value]\n    right = [right_value]\n    assert left == right\n",
            "nested_dict_equality.py",
            "list equality over nested FiniteDict(Int, Int)",
        ),
    ] {
        let failure = verify_heap_module(source, path, &[])
            .expect_err("unsupported nested mutable equality must fail closed");
        assert_eq!(failure.code, "solver.translation-failed", "{failure:#?}");
        assert!(
            failure.message.contains(expected_message),
            "{path}: {failure:#?}"
        );
    }
}
