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
fn exact_production_mypy_rejection_is_identity_bound_but_not_a_semantic_proof() {
    let (suite, pin) = pinned_suite();
    let result =
        check_pinned_scalar_fixture(suite, pin, "tests/functional/translation/issues/00002.py")
            .unwrap();
    assert!(result.passed, "{result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::ProductionTypecheckRejection
    );
    let identity = result.python_typechecker.as_ref().unwrap();
    assert_eq!(identity.checker, "mypy");
    assert_eq!(identity.checker_version, "1.5.0");
    assert_eq!(identity.profile, "strict-issuance");
    assert_eq!(result.python_typecheck_diagnostics.len(), 1);
    assert_eq!(
        result.python_typecheck_diagnostics[0].path.as_deref(),
        Some("tests/functional/translation/issues/00002.py")
    );
    assert_eq!(result.python_typecheck_diagnostics[0].line, Some(9));
}

#[test]
fn legacy_nagini_missing_annotation_name_matches_without_losing_mypy_evidence() {
    let (suite, pin) = pinned_suite();
    for fixture in [
        "tests/functional/translation/issues/00001.py",
        "tests/functional/translation/issues/00012.py",
        "tests/io/translation/test_basic_io_10.py",
    ] {
        let result = check_pinned_scalar_fixture(suite, pin, fixture).unwrap();
        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(
            result.analysis_kind,
            ConformanceMatchKind::ProductionTypecheckRejection,
            "{fixture}"
        );
        assert!(result.python_typechecker.is_some(), "{fixture}");
        assert_eq!(result.expected, result.actual, "{fixture}");
        assert_eq!(result.python_typecheck_diagnostics.len(), 1, "{fixture}");
        assert_eq!(
            result.python_typecheck_diagnostics[0].code, "frontend.python.typecheck.no-untyped-def",
            "{fixture}"
        );
    }
}
