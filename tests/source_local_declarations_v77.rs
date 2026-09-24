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

fn declaration_diagnostics(analysis: &maledictus::FrontendAnalysis) -> Vec<&str> {
    analysis
        .diagnostics
        .iter()
        .filter_map(|diagnostic| {
            matches!(
                diagnostic.code.as_str(),
                "invalid.program:local.import" | "invalid.program:local.type.alias"
            )
            .then_some(diagnostic.code.as_str())
        })
        .collect()
}

#[test]
fn exact_local_type_alias_failures_match_every_backend() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_type_aliases_1.py",
        "tests/functional/translation/test_type_aliases_2.py",
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
fn local_imports_are_rejected_at_any_executable_depth() {
    for source in [
        "def direct() -> None:\n    import decimal\n",
        "def nested(flag: bool) -> None:\n    if flag:\n        from decimal import Decimal\n",
        "class Box:\n    import decimal\n",
    ] {
        let analysis = analyze(source);
        assert_eq!(
            declaration_diagnostics(&analysis),
            ["invalid.program:local.import"],
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn aliases_of_typing_constructors_are_binding_aware() {
    let function =
        analyze("from typing import List as L\ndef invalid() -> None:\n    Alias = L[int]\n");
    assert_eq!(
        declaration_diagnostics(&function),
        ["invalid.program:local.type.alias"],
        "{function:#?}"
    );

    let class =
        analyze("from typing import Optional as Maybe\nclass Box:\n    Alias = Maybe[int]\n");
    assert_eq!(
        declaration_diagnostics(&class),
        ["invalid.program:local.type.alias"],
        "{class:#?}"
    );
}

#[test]
fn module_aliases_runtime_subscripts_and_shadowed_names_remain_ordinary() {
    for source in [
        "from typing import List\nValues = List[int]\n",
        "from typing import List\ndef first(values: List[int]) -> int:\n    item = values[0]\n    return item\n",
        "from typing import List\ndef ordinary(value: int) -> int:\n    List = value\n    Alias = List[value]\n    return value\n",
        "from typing import List\nclass Box:\n    List = object\n    Alias = List[int]\n",
    ] {
        let analysis = analyze(source);
        assert!(
            declaration_diagnostics(&analysis).is_empty(),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn pinned_local_imports_report_the_source_rejection_before_same_line_typecheck_consequences() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_import_1.py",
        "tests/functional/translation/test_import_2.py",
    ] {
        let result = check_pinned_scalar_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("{fixture}: {error}"));
        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(
            result.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection,
            "{fixture}: {result:#?}"
        );
        assert!(
            result
                .python_typecheck_diagnostics
                .iter()
                .all(|diagnostic| {
                    diagnostic.code == "frontend.python.typecheck.misc"
                        && diagnostic.line == Some(6)
                }),
            "{fixture}: {result:#?}"
        );
    }
}
