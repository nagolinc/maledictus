use std::fs;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};

fn request(directory: &tempfile::TempDir, source: &str) -> ProofRequest {
    fs::write(directory.path().join("program.py"), source).unwrap();
    ProofRequest {
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
    }
}

fn analyze(source: &str) -> maledictus::FrontendAnalysis {
    let directory = tempfile::tempdir().unwrap();
    maledictus::analyze_python_frontend(&request(&directory, source))
}

#[test]
fn exact_nested_declaration_and_pure_assignment_failures_match_every_backend() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_nested_1.py",
        "tests/functional/translation/test_nested_2.py",
        "tests/functional/translation/test_pure_multi_assign.py",
    ] {
        let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("scalar {fixture}: {error}"));
        assert!(scalar.passed, "scalar {fixture}: {scalar:#?}");
        assert_eq!(
            scalar.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection,
            "scalar {fixture}: {scalar:#?}"
        );
        assert!(scalar.python_typechecker.is_some(), "{scalar:#?}");
        let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("heap {fixture}: {error}"));
        assert!(heap.passed, "heap {fixture}: {heap:#?}");
        let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(reference.passed, "reference {fixture}: {reference:#?}");
    }
}

#[test]
fn top_level_declarations_and_single_target_pure_assignments_remain_valid() {
    for source in [
        "from nagini_contracts.contracts import *\nclass Box:\n    pass\ndef make() -> Box:\n    return Box()\n",
        "from nagini_contracts.contracts import *\n@Pure\ndef increment(value: int) -> int:\n    result = value + 1\n    return result\n",
        "from nagini_contracts.contracts import *\ndef unpack(value: int) -> int:\n    left, right = value, value + 1\n    return left\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis.diagnostics.iter().all(|diagnostic| !matches!(
                diagnostic.code.as_str(),
                "invalid.program:nested.class.declaration"
                    | "invalid.program:nested.function.declaration"
                    | "unsupported:Multi-target assignments are not supported in pure functions."
            )),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn a_shadowed_pure_decorator_spelling_does_not_restrict_assignment_shape() {
    let source = "from nagini_contracts.contracts import Pure\nPure = object\n@Pure\ndef unpack(value: int) -> int:\n    left, right = value, value + 1\n    return left\n";
    let analysis = analyze(source);
    assert!(
        analysis.diagnostics.iter().all(|diagnostic| diagnostic.code
            != "unsupported:Multi-target assignments are not supported in pure functions."),
        "{analysis:#?}"
    );
}
