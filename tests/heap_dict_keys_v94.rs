use std::path::PathBuf;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_heap_contracts::verify_heap_module;

fn verify(source: &str) -> maledictus::python_heap_contracts::HeapContractVerification {
    verify_heap_module(source, "heap_dict_keys_v94.py", &[])
        .unwrap_or_else(|failure| panic!("dictionary keys source was refused: {failure:#?}"))
}

#[test]
fn finite_dictionary_keys_preserve_exact_membership_length_and_duplicate_key_behavior() {
    let source = r#"def run() -> None:
    values = {1: 'old', 2: 'two', 1: 'new'}
    keys = values.keys()
    assert len(keys) == 2
    assert 1 in keys
    assert 2 in keys
    assert 3 not in keys
"#;

    let verification = verify(source);
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn keys_after_a_finite_dictionary_store_observe_the_updated_dictionary() {
    let source = r#"def run() -> None:
    values = {1: 'one'}
    values[2] = 'two'
    keys = values.keys()
    assert len(keys) == 2
    assert 2 in keys
"#;

    let verification = verify(source);
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn malformed_calls_and_mutation_with_a_live_keys_view_fail_closed() {
    for (source, expected_code) in [
        (
            "def run() -> None:\n    values = {1: 2}\n    keys = values.keys(1)\n",
            "frontend.python.heap.dict-keys-arguments-unsupported",
        ),
        (
            "def run() -> None:\n    values = {1: 2}\n    keys = values.keys()\n    values[2] = 3\n",
            "frontend.python.heap.dict-mutation-live-keys-view-unsupported",
        ),
        (
            "def run() -> None:\n    values = [1, 2]\n    keys = values.keys()\n",
            "frontend.python.heap.expression-unsupported",
        ),
    ] {
        let failure = verify_heap_module(source, "heap_dict_keys_v94_bad.py", &[])
            .expect_err("unsupported dictionary keys semantics must fail closed");
        assert_eq!(failure.code, expected_code, "{failure:#?}");
    }
}

#[test]
fn exact_pinned_dictionary_keys_fixture_matches_all_backends() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/functional/verification/issues/00049.py";

    let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("scalar dictionary keys fixture was refused: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(scalar.expected, scalar.actual);
    assert!(scalar.actual.is_empty());

    let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("heap dictionary keys fixture was refused: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual);
    assert!(heap.actual.is_empty());

    let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
        .expect_err("the nominal-reference backend has no source classes to analyze");
    assert!(
        reference.contains("frontend.python.references.empty-module"),
        "{reference}"
    );
}
