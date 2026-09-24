use std::path::PathBuf;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};

#[test]
fn exact_io_builtins_fixture_uses_only_the_heap_transition_backend() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/io/verification/test_builtins.py";

    let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture);
    assert!(
        scalar.is_err(),
        "scalar must not claim linear heap IO semantics: {scalar:#?}"
    );

    let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("heap IO classifier refused exact fixture: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert!(heap.semantic_verified, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual, "{heap:#?}");

    let reference = check_pinned_reference_fixture(&suite, &pin, fixture);
    assert!(
        reference.is_err(),
        "reference backend must not claim linear heap IO semantics: {reference:#?}"
    );
}
