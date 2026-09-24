use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};

const INVALID_UNFOLDING_FIXTURE: &str = "tests/functional/translation/test_unfolding_2.py";

#[test]
fn invalid_unfolding_position_matches_all_three_backends() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, INVALID_UNFOLDING_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar {INVALID_UNFOLDING_FIXTURE}: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(
        scalar.analysis_kind,
        ConformanceMatchKind::SourceWellformednessRejection,
        "{scalar:#?}"
    );
    assert!(
        !scalar.python_typecheck_diagnostics.is_empty(),
        "the source rejection must retain the same-line typechecker evidence"
    );
    assert!(
        scalar
            .python_typecheck_diagnostics
            .iter()
            .all(|diagnostic| diagnostic.line == Some(21)),
        "{scalar:#?}"
    );

    let heap = check_pinned_heap_fixture(&suite, &pin, INVALID_UNFOLDING_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {INVALID_UNFOLDING_FIXTURE}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual, "{heap:#?}");

    let reference = check_pinned_reference_fixture(&suite, &pin, INVALID_UNFOLDING_FIXTURE)
        .unwrap_or_else(|error| panic!("reference {INVALID_UNFOLDING_FIXTURE}: {error}"));
    assert!(reference.passed, "{reference:#?}");
    assert_eq!(reference.expected, reference.actual, "{reference:#?}");
}
