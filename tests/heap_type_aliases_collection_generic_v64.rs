use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_heap_contracts::verify_heap_module;

#[test]
fn exact_upstream_alias_and_collection_generic_fixtures_match() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (fixture, expected_diagnostics) in [
        ("tests/functional/verification/test_type_aliases.py", 2),
        ("tests/functional/verification/issues/00285.py", 0),
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
fn ordered_class_and_annotation_aliases_are_used_at_typed_boundaries() {
    let source = r#"from nagini_contracts.contracts import *
from typing import List

class Item:
    pass

Alias = Item
Items = List[Alias]

def inspect(values: Items) -> None:
    Requires(list_pred(values) and len(values) > 0)
    value = values[0]
    assert isinstance(value, Alias)

def build() -> None:
    value = Alias()
    assert isinstance(value, Item)
"#;
    let verification = verify_heap_module(source, "ordered_aliases.py", &[])
        .unwrap_or_else(|failure| panic!("ordered aliases were refused: {failure:#?}"));
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn aliases_are_immutable_ordered_and_cannot_escape_as_runtime_values() {
    for (source, expected_code) in [
        (
            "class Item:\n    pass\nAlias = Item\nAlias = Item\n",
            "frontend.python.heap.type-alias-reassigned",
        ),
        (
            "class Item:\n    pass\ndef make() -> Alias:\n    return Item()\nAlias = Item\n",
            "frontend.python.heap.type-alias-runtime-use-unsupported",
        ),
        (
            "class Item:\n    pass\nAlias = Item\ndef expose() -> object:\n    return Alias\n",
            "frontend.python.heap.type-alias-runtime-use-unsupported",
        ),
    ] {
        let failure = verify_heap_module(source, "invalid_alias.py", &[]).unwrap_err();
        assert_eq!(failure.code, expected_code, "{failure:#?}");
    }
}

#[test]
fn alias_boundary_refuses_dynamic_nested_union_and_shadowed_list_forms() {
    for source in [
        "class Item:\n    pass\ndef choose():\n    return Item\nAlias = choose()\n",
        "from typing import List\nclass Item:\n    pass\nAlias = List[List[Item]]\n",
        "from typing import List, Union\nclass Item:\n    pass\nAlias = Union[Item, int]\n",
        "from typing import List\nclass Item:\n    pass\nList = tuple\nAlias = List[Item]\n",
    ] {
        assert!(
            verify_heap_module(source, "unsupported_alias.py", &[]).is_err(),
            "unsupported alias form was accepted: {source}"
        );
    }
}

#[test]
fn collection_constructor_identity_requires_the_proven_direct_alias_assignment() {
    let source = r#"from nagini_contracts.contracts import *
from typing import Generic, List, TypeVar

T = TypeVar('T')

class Box(Generic[T]):
    def __init__(self, expected: T, actual: T):
        Ensures(Acc(self.value) and self.value is expected)
        self.value = actual

def build() -> Box[List[int]]:
    return Box[List[int]]([1], [2])
"#;
    let failure = verify_heap_module(source, "generic_alias_mismatch.py", &[]).unwrap_err();
    assert_eq!(
        failure.code, "frontend.python.heap.nonreference-identity-unsupported",
        "{failure:#?}"
    );
}

#[test]
fn nominal_list_elements_prove_static_supertype_isinstance_without_exact_runtime_class() {
    let source = r#"from nagini_contracts.contracts import *
from typing import List

class Base:
    pass

class Child(Base):
    pass

Items = List[Base]

def inspect(values: Items) -> None:
    Requires(list_pred(values) and len(values) > 0)
    value = values[0]
    assert isinstance(value, Base)
"#;
    let result = verify_heap_module(source, "unsealed_list_elements.py", &[]).unwrap();
    assert!(result.passed, "{:#?}", result.obligations);
    assert!(result.obligations.iter().any(|obligation| {
        obligation.id.starts_with("inspect:assert:") && obligation.satisfied()
    }));
}
