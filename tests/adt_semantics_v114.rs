use std::path::PathBuf;

use maledictus::conformance::{
    check_heap_source, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};

const PREFIX: &str = "from nagini_contracts.adt import ADT\nfrom nagini_contracts.contracts import *\nfrom typing import NamedTuple, cast\n\nclass Tree(ADT):\n    pass\nclass Leaf(Tree, NamedTuple('Leaf', [('value', int)])):\n    pass\nclass Node(Tree, NamedTuple('Node', [('left', Tree), ('right', Tree)])):\n    pass\n";

#[test]
fn immutable_products_preserve_nested_fields_runtime_tags_and_order() {
    let source = format!(
        "{PREFIX}\ndef run() -> None:\n    left = Leaf(4)\n    right = Leaf(9)\n    tree = Node(left, right)\n    assert cast(Leaf, tree.left).value == 4\n    assert cast(Leaf, tree.right).value == 9\n    assert isinstance(tree.left, Tree)\n    assert type(tree.right) is Leaf\n    #:: ExpectedOutput(assert.failed:assertion.false)\n    assert False\n"
    );
    let result = check_heap_source(&source, "adt_nested.py").unwrap();
    assert_eq!(result.expected, result.actual, "{result:#?}");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn structural_equality_requires_every_declared_field() {
    let source = "from nagini_contracts.adt import ADT\nfrom nagini_contracts.contracts import *\nfrom typing import NamedTuple\nclass Root(ADT):\n    pass\nclass Pair(Root, NamedTuple('Pair', [('left', int), ('right', int)])):\n    pass\n@Pure\ndef complete(a: Pair, b: Pair) -> bool:\n    Requires(a.left == b.left)\n    Requires(a.right == b.right)\n    Ensures(a == b)\n    return True\n@Pure\ndef incomplete(a: Pair, b: Pair) -> bool:\n    Requires(a.left == b.left)\n    #:: ExpectedOutput(postcondition.violated:assertion.false)\n    Ensures(a == b)\n    return True\n";
    let result = check_heap_source(source, "adt_equality.py").unwrap();
    assert_eq!(result.expected, result.actual, "{result:#?}");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn exact_pinned_adt_verification_fixtures_match_through_public_classifiers() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/verification/test_adt_2.py",
        "tests/functional/verification/test_adt_3.py",
        "tests/functional/verification/test_adt_4.py",
    ] {
        let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture);
        assert!(
            scalar.is_err(),
            "scalar must not claim heap ADT semantics: {scalar:#?}"
        );
        if fixture.ends_with("test_adt_3.py") {
            let error = scalar.unwrap_err();
            assert!(
                error.starts_with("frontend.python.contracts.module-statement-unsupported:"),
                "the valid method assignment type comment must not fail location preflight: {error}"
            );
        }

        let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("public heap classifier refused {fixture}: {error}"));
        assert!(heap.passed, "{fixture}: {heap:#?}");
        assert_eq!(heap.expected, heap.actual, "{fixture}: {heap:#?}");

        let reference = check_pinned_reference_fixture(&suite, &pin, fixture);
        assert!(
            reference.is_err(),
            "reference backend must not claim heap ADT semantics: {reference:#?}"
        );
    }
}
