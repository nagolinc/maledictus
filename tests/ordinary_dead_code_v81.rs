use std::path::Path;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_scalar_fixture};

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
fn pinned_exception_and_io_dead_code_fixtures_match() {
    let (suite, pin) = pinned_suite();
    for fixture in [
        "tests/functional/translation/test_exception_2.py",
        "tests/functional/translation/test_exception_3.py",
        "tests/functional/translation/test_exception_4.py",
        "tests/functional/translation/test_exception_5.py",
    ] {
        let result = check_pinned_scalar_fixture(suite, pin, fixture).unwrap();
        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(
            result.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection,
            "{fixture}"
        );
        assert_eq!(result.actual.len(), 1, "{fixture}");
        assert_eq!(result.actual[0].code, "type.error:dead.code", "{fixture}");
    }
}
