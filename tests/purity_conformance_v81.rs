use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_scalar_fixture,
};

fn pinned_suite() -> (&'static Path, &'static Path) {
    (
        Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/.upstream/nagini")),
        Path::new(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/conformance/nagini-v1.3.1.json"
        )),
    )
}

#[test]
fn pinned_purity_violations_match_at_the_production_call_site() {
    let (suite, pin) = pinned_suite();
    for fixture in [
        "tests/functional/translation/test_loop_1.py",
        "tests/functional/translation/test_purity_1.py",
        "tests/functional/translation/test_purity_2.py",
        "tests/sif-true/translation/test_while_purity.py",
    ] {
        let result = check_pinned_scalar_fixture(suite, pin, fixture).unwrap();
        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(
            result.analysis_kind,
            ConformanceMatchKind::SemanticVerification,
            "{fixture}"
        );
        assert_eq!(result.actual.len(), 1, "{fixture}");
        assert_eq!(
            result.actual[0].code, "invalid.program:purity.violated",
            "{fixture}"
        );
    }
}

#[test]
fn pinned_unfolding_purity_violation_matches_through_the_heap_frontend() {
    let (suite, pin) = pinned_suite();
    let fixture = "tests/functional/translation/test_unfolding_3.py";
    let result = check_pinned_heap_fixture(suite, pin, fixture).unwrap();
    assert!(result.passed, "{result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SemanticVerification
    );
    assert_eq!(result.actual.len(), 1);
    assert_eq!(result.actual[0].code, "invalid.program:purity.violated");
}
