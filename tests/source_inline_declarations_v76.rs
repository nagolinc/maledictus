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

fn inline_diagnostics(analysis: &maledictus::FrontendAnalysis) -> Vec<&str> {
    analysis
        .diagnostics
        .iter()
        .filter_map(|diagnostic| {
            matches!(
                diagnostic.code.as_str(),
                "invalid.program:decorators.incompatible"
                    | "invalid.program:overriding.inline.method"
                    | "invalid.program:contract.in.inline.method"
                    | "unsupported:Inlining constructors is currently not supported."
            )
            .then_some(diagnostic.code.as_str())
        })
        .collect()
}

#[test]
fn exact_inline_and_opaque_declaration_failures_match_every_backend() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_inline_1.py",
        "tests/functional/translation/test_inline_2.py",
        "tests/functional/translation/test_inline_3.py",
        "tests/functional/translation/test_inline_4.py",
        "tests/functional/translation/test_inline_5.py",
        "tests/functional/translation/test_inline_6.py",
        "tests/functional/translation/test_inline_constructor.py",
        "tests/functional/translation/test_opaque_1.py",
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
fn valid_inline_opaque_and_ordinary_overrides_are_not_rejected() {
    for source in [
        "from nagini_contracts.contracts import *\n@Inline\ndef inline(value: int) -> int:\n    return value + 1\n",
        "from nagini_contracts.contracts import *\n@Pure\n@Opaque\ndef hidden(value: int) -> int:\n    Ensures(Result() == value)\n    return value\n",
        "from nagini_contracts.contracts import *\nclass Left:\n    @Inline\n    def value(self) -> int:\n        return 1\nclass Right:\n    def value(self) -> int:\n        return 2\n",
        "from nagini_contracts.contracts import *\nclass Base:\n    def value(self) -> int:\n        return 1\nclass Child(Base):\n    def value(self) -> int:\n        return 2\n",
    ] {
        let analysis = analyze(source);
        assert!(inline_diagnostics(&analysis).is_empty(), "{analysis:#?}");
    }
}

#[test]
fn canonical_aliases_are_checked_but_rebound_spellings_have_no_contract_meaning() {
    let aliased = analyze(
        "from nagini_contracts.contracts import Inline as inline\nfrom nagini_contracts.contracts import Requires\n@inline\ndef invalid(value: int) -> int:\n    Requires(value > 0)\n    return value\n",
    );
    assert_eq!(
        inline_diagnostics(&aliased),
        ["invalid.program:contract.in.inline.method"],
        "{aliased:#?}"
    );

    let rebound = analyze(
        "from nagini_contracts.contracts import Inline, Requires\nInline = object\n@Inline\ndef ordinary(value: int) -> int:\n    Requires(value > 0)\n    return value\n",
    );
    assert!(inline_diagnostics(&rebound).is_empty(), "{rebound:#?}");
}

#[test]
fn inherited_inline_boundaries_are_checked_transitively() {
    let analysis = analyze(
        "from nagini_contracts.contracts import *\nclass Base:\n    @Inline\n    def value(self) -> int:\n        return 1\nclass Middle(Base):\n    pass\nclass Child(Middle):\n    def value(self) -> int:\n        return 2\n",
    );
    assert_eq!(
        inline_diagnostics(&analysis),
        ["invalid.program:overriding.inline.method"],
        "{analysis:#?}"
    );
}
