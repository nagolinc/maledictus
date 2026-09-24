use std::{fs, path::PathBuf};

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};
use maledictus::python_heap_contracts::verify_heap_module;
use maledictus::vc::ObligationExpectation;

fn verify(source: &str) -> maledictus::python_heap_contracts::HeapContractVerification {
    verify_heap_module(source, "heap_refute_v91.py", &[])
        .unwrap_or_else(|failure| panic!("source was refused: {failure:#?}"))
}

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
fn refute_requires_the_argument_to_be_false_on_each_reachable_path() {
    let source = r#"from nagini_contracts.contracts import *

def run(value: int, branch: bool) -> None:
    Requires(value > 0)
    Refute(value <= 0)
    Refute(value > 0)
    if branch:
        Refute(False)
    else:
        Refute(True)
"#;
    let verification = verify(source);
    let refutations: Vec<_> = verification
        .obligations
        .iter()
        .filter(|item| item.id.contains(":refute:"))
        .collect();

    assert_eq!(refutations.len(), 4, "{verification:#?}");
    assert!(
        refutations
            .iter()
            .all(|item| item.expectation == ObligationExpectation::Refute)
    );
    assert_eq!(
        refutations.iter().filter(|item| item.satisfied()).count(),
        2,
        "{verification:#?}"
    );
    assert!(!verification.passed);
}

#[test]
fn method_refutations_keep_heap_read_permissions_as_separate_proof_obligations() {
    let source = r#"from nagini_contracts.contracts import *

class Cell:
    value: int

    def nonnegative(self) -> None:
        Requires(Acc(self.value))
        Requires(self.value >= 0)
        Refute(self.value < 0)

    def missing_permission(self) -> None:
        Refute(self.value < 0)
"#;
    let verification = verify(source);

    assert!(
        verification
            .obligations
            .iter()
            .any(|item| { item.id.starts_with("Cell.nonnegative:refute:") && item.satisfied() })
    );
    assert!(verification.obligations.iter().any(|item| {
        item.id.contains("Cell.missing_permission:body-refute:") && !item.satisfied()
    }));
    assert!(!verification.passed);
}

#[test]
fn non_boolean_refutations_fail_closed() {
    let failure = verify_heap_module(
        "from nagini_contracts.contracts import *\ndef run() -> None:\n    Refute(1)\n",
        "heap_refute_v91_bad.py",
        &[],
    )
    .expect_err("Refute must not coerce an integer into a proposition");

    assert_eq!(failure.code, "frontend.python.heap.expected-bool");
}

#[test]
fn frontend_reports_refutation_failures_without_relabeling_them_as_assertions() {
    let analysis = analyze(
        "from nagini_contracts.contracts import *\nclass Marker:\n    pass\ndef run() -> None:\n    Refute(True)\n",
    );

    assert!(
        analysis
            .diagnostics
            .iter()
            .any(|item| item.code == "refute.failed:refutation.true"),
        "{analysis:#?}"
    );
    assert!(
        analysis
            .diagnostics
            .iter()
            .all(|item| item.code != "assert.failed:assertion.false")
    );
}

#[test]
fn exact_pinned_refute_fixture_matches_scalar_and_heap_diagnostics() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/functional/verification/test_refute.py";

    let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(scalar.expected, scalar.actual);
    assert_eq!(scalar.actual.len(), 3);

    let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("heap fixture was refused: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual);
    assert_eq!(heap.actual.len(), 3);

    let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
        .expect_err("the nominal-reference backend has no source classes to analyze");
    assert!(
        reference.contains("frontend.python.references.empty-module"),
        "{reference}"
    );
}
