use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_predicate_family_wellformedness::{
    PARTIALLY_ABSTRACT_PREDICATE_FAMILY, validate_predicate_families,
};
use rustpython_parser::{Parse, ast};

const FIXTURE: &str = "tests/functional/translation/test_abstract_pred_5.py";

#[test]
fn pinned_partially_abstract_predicate_family_matches_every_public_classifier() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let source = std::fs::read_to_string(suite.join(FIXTURE)).unwrap();
    let parsed = ast::Suite::parse(&source, FIXTURE).unwrap();
    let failure = validate_predicate_families(&parsed, &source).unwrap_err();
    assert_eq!(failure.code, PARTIALLY_ABSTRACT_PREDICATE_FAMILY);
    assert_eq!((failure.line, failure.column), (17, 5));

    let scalar = check_pinned_scalar_fixture(&suite, &pin, FIXTURE).unwrap();
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(
        scalar.analysis_kind,
        ConformanceMatchKind::SourceWellformednessRejection
    );
    assert_eq!(scalar.expected, scalar.actual);
    assert_eq!(scalar.actual[0].code, PARTIALLY_ABSTRACT_PREDICATE_FAMILY);
    assert_eq!(scalar.actual[0].line, 17);

    let heap = check_pinned_heap_fixture(&suite, &pin, FIXTURE).unwrap();
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(
        heap.analysis_kind,
        ConformanceMatchKind::SourceWellformednessRejection
    );
    assert_eq!(heap.expected, heap.actual);

    let reference = check_pinned_reference_fixture(&suite, &pin, FIXTURE).unwrap();
    assert!(reference.passed, "{reference:#?}");
    assert_eq!(reference.expected, reference.actual);
}
