use std::fs;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};

const MALFORMED_ADT: &str = "invalid.program:malformed.adt";

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

fn malformed(source: &str) -> maledictus::protocol::Diagnostic {
    let analysis = analyze(source);
    let failures = analysis
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == MALFORMED_ADT)
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{source}\n{analysis:#?}");
    failures.into_iter().next().unwrap()
}

#[test]
fn aliases_and_module_qualified_factories_are_canonical() {
    for source in [
        "from nagini_contracts.adt import ADT as Algebraic\nfrom typing import NamedTuple as Product\nclass Tree(Algebraic):\n    pass\nclass Leaf(Tree, Product('Leaf', [])):\n    pass\n",
        "import nagini_contracts.adt as algebra\nimport typing as types\nclass Tree(algebra.ADT):\n    pass\nclass Leaf(Tree, types.NamedTuple('Leaf', [])):\n    pass\n",
        "import nagini_contracts.adt\nfrom typing import NamedTuple\nclass Tree(nagini_contracts.adt.ADT):\n    pass\nclass Leaf(Tree, NamedTuple('Leaf', [])):\n    pass\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != MALFORMED_ADT),
            "{source}\n{analysis:#?}"
        );
        assert!(
            !matches!(
                analysis.disposition,
                maledictus::FrontendDisposition::Supported
            ),
            "well-formed ADTs must reach explicit unsupported semantics, not be claimed proved:\n{analysis:#?}"
        );
    }
}

#[test]
fn lookalikes_and_shadowed_imports_do_not_create_adts() {
    for source in [
        "class ADT:\n    pass\nclass LooksLike(ADT):\n    def method(self) -> None:\n        pass\n",
        "from nagini_contracts.adt import ADT\nADT = object\nclass LooksLike(ADT):\n    def method(self) -> None:\n        pass\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != MALFORMED_ADT),
            "{source}\n{analysis:#?}"
        );
    }

    let shadowed_named_tuple = "from nagini_contracts.adt import ADT\nfrom typing import NamedTuple\nNamedTuple = object\nclass Tree(ADT):\n    pass\nclass Leaf(Tree, NamedTuple('Leaf', [])):\n    pass\n";
    let failure = malformed(shadowed_named_tuple);
    assert_eq!(failure.line, Some(6), "{failure:#?}");
}

#[test]
fn every_root_is_checked_after_late_constructors_have_been_seen() {
    let valid = "from nagini_contracts.adt import ADT\nfrom typing import NamedTuple\nclass First(ADT):\n    pass\nclass Second(ADT):\n    pass\nclass SecondLeaf(Second, NamedTuple('SecondLeaf', [])):\n    pass\nclass FirstLeaf(First, NamedTuple('FirstLeaf', [])):\n    pass\n";
    let analysis = analyze(valid);
    assert!(
        analysis
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != MALFORMED_ADT),
        "{analysis:#?}"
    );

    let missing_second = "from nagini_contracts.adt import ADT\nfrom typing import NamedTuple\nclass First(ADT):\n    pass\nclass Second(ADT):\n    pass\nclass FirstLeaf(First, NamedTuple('FirstLeaf', [])):\n    pass\n";
    let failure = malformed(missing_second);
    assert_eq!(failure.line, Some(5), "{failure:#?}");
}

#[test]
fn docstring_then_pass_is_empty_but_other_bodies_are_not() {
    let valid = "from nagini_contracts.adt import ADT\nfrom typing import NamedTuple\nclass Tree(ADT):\n    \"tree values\"\n    pass\nclass Leaf(Tree, NamedTuple('Leaf', [])):\n    \"leaf constructor\"\n    pass\n";
    let analysis = analyze(valid);
    assert!(
        analysis
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != MALFORMED_ADT),
        "{analysis:#?}"
    );

    let method_body = "from nagini_contracts.adt import ADT\nclass Tree(ADT):\n    def value(self) -> int:\n        return 1\n";
    assert_eq!(malformed(method_body).line, Some(2));
}

#[test]
fn constructor_subclasses_cannot_silently_become_defining_roots() {
    let source = "from nagini_contracts.adt import ADT\nfrom typing import NamedTuple\nclass Tree(ADT):\n    pass\nclass Leaf(Tree, NamedTuple('Leaf', [])):\n    pass\nclass Child(Leaf):\n    pass\n";
    let failure = malformed(source);
    assert_eq!(failure.line, Some(7), "{failure:#?}");
}

#[test]
fn complete_module_validation_is_not_limited_by_requested_symbols() {
    let directory = tempfile::tempdir().unwrap();
    let source = "from nagini_contracts.adt import ADT\ndef selected() -> int:\n    return 1\nclass Broken(ADT):\n    pass\n";
    let mut proof_request = request(&directory, source);
    proof_request.files[0].symbols = vec!["selected".to_owned()];
    let analysis = maledictus::analyze_python_frontend(&proof_request);
    assert!(
        analysis
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == MALFORMED_ADT && diagnostic.line == Some(4) }),
        "{analysis:#?}"
    );
}

#[test]
fn all_nine_upstream_malformed_adt_fixtures_match_exactly() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture_number in 1..=9 {
        let fixture = format!("tests/functional/translation/test_adt_{fixture_number}.py");
        let scalar = check_pinned_scalar_fixture(&suite, &pin, &fixture)
            .unwrap_or_else(|error| panic!("scalar {fixture}: {error}"));
        assert!(scalar.passed, "scalar {fixture}: {scalar:#?}");
        assert_eq!(
            scalar.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection,
            "scalar {fixture}: {scalar:#?}"
        );
        assert!(scalar.python_typechecker.is_some(), "{scalar:#?}");

        let heap = check_pinned_heap_fixture(&suite, &pin, &fixture)
            .unwrap_or_else(|error| panic!("heap {fixture}: {error}"));
        assert!(heap.passed, "heap {fixture}: {heap:#?}");

        let reference = check_pinned_reference_fixture(&suite, &pin, &fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(reference.passed, "reference {fixture}: {reference:#?}");
    }
}
