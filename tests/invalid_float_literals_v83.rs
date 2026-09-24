use std::fs;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};

const INVALID_FLOAT_VALUE: &str = "invalid.program:invalid.float.val";

fn analyze(source: &str) -> maledictus::FrontendAnalysis {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("program.py"), source).unwrap();
    maledictus::analyze_python_frontend(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "program.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

#[test]
fn rejects_certainly_invalid_builtin_float_literals_at_the_real_call() {
    for invalid in ["asdasd", "1.2 dollars", "3/4", "(1.0)"] {
        let source = format!(
            "from nagini_contracts.contracts import Assert\n\ndef run() -> None:\n    value = float({invalid:?})\n    Assert(value == value)\n"
        );
        let analysis = analyze(&source);
        let diagnostic = analysis
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code == INVALID_FLOAT_VALUE)
            .unwrap_or_else(|| {
                panic!("missing invalid-float diagnostic for {invalid:?}: {analysis:#?}")
            });
        assert_eq!(diagnostic.line, Some(4));
    }
}

#[test]
fn does_not_guess_about_valid_unknown_or_shadowed_float_spellings() {
    for source in [
        "def run() -> None:\n    value = float('1.25e-3')\n",
        "def run() -> None:\n    value = float('-Infinity')\n",
        "def run() -> None:\n    value = float('NaN')\n",
        "def run() -> None:\n    value = float('١٢٣')\n",
        "def run(float: object) -> None:\n    value = float('asdasd')\n",
        "float = lambda value: value\ndef run() -> None:\n    value = float('asdasd')\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != INVALID_FLOAT_VALUE),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn both_pinned_invalid_float_fixtures_match_all_frontends_exactly() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/float_ieee32/test_non_float.py",
        "tests/functional/translation/float_real/test_non_float.py",
    ] {
        let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("scalar {fixture}: {error}"));
        assert!(scalar.passed, "scalar {fixture}: {scalar:#?}");
        assert_eq!(
            scalar.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection
        );

        let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("heap {fixture}: {error}"));
        assert!(heap.passed, "heap {fixture}: {heap:#?}");

        let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(reference.passed, "reference {fixture}: {reference:#?}");
    }
}
