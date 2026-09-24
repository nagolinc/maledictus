use std::path::PathBuf;

use maledictus::conformance::{check_heap_source, check_pinned_heap_fixture};
use maledictus::python_heap_contracts::verify_heap_module;

fn pinned() -> (PathBuf, PathBuf) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    (
        root.join(".upstream/nagini"),
        root.join("conformance/nagini-v1.3.1.json"),
    )
}

#[test]
fn exact_persistent_collection_fixtures_match_through_the_public_classifier() {
    let (suite, pin) = pinned();
    for fixture in [
        "tests/functional/verification/test_pseq.py",
        "tests/functional/verification/test_pset.py",
        "tests/functional/verification/test_pmultiset.py",
    ] {
        let result = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("public heap classifier refused {fixture}: {error}"));
        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(result.expected, result.actual, "{fixture}: {result:#?}");
    }
}

#[test]
fn source_general_algebra_preserves_multiplicity_and_identity() {
    let source = r#"from nagini_contracts.contracts import *

class Item:
    pass

def verify() -> None:
    item = Item()
    sequence = PSeq(item)
    assert sequence[0] is item
    bag = PMultiset(1, 1, 2) - PMultiset(1)
    assert bag.num(1) == 1
    assert PMultiset(1, 2, 1) == PMultiset(2, 1, 1)
    values = PSet(1, 1) + PSet(2)
    assert len(values) == 2
    assert PSet(1, 2) == PSet(2, 1)
    mapping = {1: 2, 1: 3}
    assert len(mapping) == 1
    keys = ToSeq(mapping)
    assert len(keys) == 1
    assert 1 in keys
"#;
    let result = check_heap_source(source, "source_general.py")
        .expect("supported persistent algebra should verify");
    assert!(result.passed, "{result:#?}");
    assert!(result.semantic_verified, "{result:#?}");
}

#[test]
fn a_to_seq_only_module_routes_through_the_general_heap_frontend() {
    let source = r#"from nagini_contracts.contracts import *

def verify() -> None:
    values = ToSeq([1, 2, 3])
    assert len(values) == 3
    assert values[1] == 2
"#;
    let verification = verify_heap_module(source, "to_seq_only.py", &[])
        .expect("ToSeq over an ordinary list belongs to the general heap verifier");
    assert_eq!(
        verification.schema,
        "maledictus-python-heap-contract-verification/v1"
    );
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn unsupported_dynamic_behavior_fails_closed_through_the_public_classifier() {
    let shadowed = r#"from nagini_contracts.contracts import *

def PSeq() -> int:
    return 1

def verify() -> None:
    value = PSeq()
    assert value == 1
"#;
    let error = check_heap_source(shadowed, "shadowed.py")
        .expect_err("a shadowed persistent constructor must not inherit builtin semantics");
    assert!(
        error.starts_with("frontend.python.persistent.canonical-name-shadowed:"),
        "{error}"
    );

    let nested = r#"from nagini_contracts.contracts import *

def verify() -> None:
    values = PSeq(PSeq(1))
    assert len(values) == 1
"#;
    let error = check_heap_source(nested, "nested.py")
        .expect_err("nested persistent values are outside the proved flat algebra");
    assert!(
        error.starts_with("frontend.python.persistent.nested-element-unsupported:"),
        "{error}"
    );

    let unordered_projection = r#"from nagini_contracts.contracts import *

def verify() -> None:
    projected = ToSeq({1, 2})
    expected = PSeq(1, 2)
    assert projected == expected
"#;
    let error = check_heap_source(unordered_projection, "unordered_projection.py")
        .expect_err("a set projection must not acquire a fabricated element order");
    assert!(
        error.starts_with("frontend.python.persistent.equality-operands-unsupported:"),
        "{error}"
    );

    let mixed_dictionary_keys = r#"from nagini_contracts.contracts import *

def verify() -> None:
    mapping = {1: 2, True: 3}
    marker = PSeq(0)
    assert len(mapping) == len(marker)
"#;
    let error = check_heap_source(mixed_dictionary_keys, "mixed_dictionary_keys.py")
        .expect_err("mixed dictionary key kinds are outside the proved hash/equality algebra");
    assert!(
        error.starts_with("frontend.python.persistent.heterogeneous-elements:"),
        "{error}"
    );
}
