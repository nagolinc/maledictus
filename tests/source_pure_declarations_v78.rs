use std::fs;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};

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

fn pure_diagnostics(analysis: &maledictus::FrontendAnalysis) -> Vec<&str> {
    analysis
        .diagnostics
        .iter()
        .filter_map(|diagnostic| {
            matches!(
                diagnostic.code.as_str(),
                "invalid.program:function.type.none"
                    | "invalid.program:function.throws.exception"
                    | "invalid.program:function.return.missing"
                    | "invalid.program:function.dead.code"
                    | "type.error:dead.code"
            )
            .then_some(diagnostic.code.as_str())
        })
        .collect()
}

#[test]
fn exact_pure_declaration_failures_match_every_backend() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/issues/00009.py",
        "tests/functional/translation/test_exception_1.py",
        "tests/functional/translation/test_missing_return_1.py",
        "tests/functional/translation/test_dead_code_1.py",
        "tests/functional/translation/test_dead_code_2.py",
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
fn ordinary_functions_and_total_reachable_pure_functions_remain_valid() {
    for source in [
        "from nagini_contracts.contracts import Pure\n@Pure\ndef identity(value: int) -> int:\n    return value\n",
        "from nagini_contracts.contracts import Pure\n@Pure\ndef choose(flag: bool) -> int:\n    if flag:\n        return 1\n    else:\n        return 2\n",
        "def ordinary() -> None:\n    return\n",
        "from nagini_contracts.contracts import Exsures\nclass Failure(Exception):\n    pass\ndef ordinary() -> int:\n    Exsures(Failure, True)\n    return 1\n",
    ] {
        let analysis = analyze(source);
        assert!(
            pure_diagnostics(&analysis).is_empty(),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn pure_raises_and_nested_dead_code_are_rejected_structurally() {
    let raised = analyze(
        "from nagini_contracts.contracts import Pure\n@Pure\ndef invalid() -> int:\n    raise RuntimeError()\n",
    );
    assert_eq!(
        pure_diagnostics(&raised),
        ["invalid.program:function.throws.exception"],
        "{raised:#?}"
    );

    let dead = analyze(
        "from nagini_contracts.contracts import Pure\n@Pure\ndef invalid(flag: bool) -> int:\n    if flag:\n        return 1\n        value = 2\n    return 3\n",
    );
    assert_eq!(
        pure_diagnostics(&dead),
        ["type.error:dead.code"],
        "{dead:#?}"
    );

    let unreachable_return = analyze(
        "from nagini_contracts.contracts import Pure\n@Pure\ndef invalid() -> int:\n    return 1\n    return 2\n",
    );
    assert_eq!(
        pure_diagnostics(&unreachable_return),
        ["invalid.program:function.dead.code"],
        "{unreachable_return:#?}"
    );
}

#[test]
fn rebound_pure_spelling_has_no_declaration_semantics() {
    let analysis = analyze(
        "from nagini_contracts.contracts import Pure\nPure = object\n@Pure\ndef ordinary() -> None:\n    return\n",
    );
    assert!(pure_diagnostics(&analysis).is_empty(), "{analysis:#?}");
}
