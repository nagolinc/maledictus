use std::fs;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_scalar_fixture};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};

const RECURSIVE_STATIC_CALL: &str = "invalid.program:recursive.static.call";

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

fn recursive_failure(source: &str) -> maledictus::protocol::Diagnostic {
    let analysis = analyze(source);
    let failures = analysis
        .diagnostics
        .into_iter()
        .filter(|diagnostic| diagnostic.code == RECURSIVE_STATIC_CALL)
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "expected one recursive-call failure");
    failures.into_iter().next().unwrap()
}

#[test]
fn direct_and_indirect_class_qualified_cycles_are_rejected_at_the_entering_call() {
    let direct = "class A:\n    def repeat(self) -> int:\n        return A.repeat(self)\n";
    let failure = recursive_failure(direct);
    assert_eq!(failure.line, Some(3));

    let indirect = "class A:\n    def first(self) -> int:\n        return B.second(self)\nclass B:\n    def second(self) -> int:\n        return A.first(self)\n";
    let failure = recursive_failure(indirect);
    assert_eq!(failure.line, Some(3));
}

#[test]
fn acyclic_class_qualified_calls_remain_valid() {
    let source = "class A:\n    def first(self) -> int:\n        return A.second(self)\n    def second(self) -> int:\n        return 1\n";
    let analysis = analyze(source);
    assert!(
        analysis
            .diagnostics
            .iter()
            .all(|failure| failure.code != RECURSIVE_STATIC_CALL),
        "{analysis:#?}"
    );
}

#[test]
fn lexical_or_module_rebinding_does_not_invent_a_static_call_edge() {
    let lexical_shadow = "class A:\n    def first(self, A: object) -> int:\n        return A.second(self)\n    def second(self) -> int:\n        return A.first(self)\n";
    let result = analyze(lexical_shadow);
    assert!(
        result
            .diagnostics
            .iter()
            .all(|failure| failure.code != RECURSIVE_STATIC_CALL),
        "{result:#?}"
    );

    let module_rebound = "class A:\n    def first(self) -> int:\n        return A.second(self)\n    def second(self) -> int:\n        return A.first(self)\nA = object\n";
    let result = analyze(module_rebound);
    assert!(
        result
            .diagnostics
            .iter()
            .all(|failure| failure.code != RECURSIVE_STATIC_CALL),
        "{result:#?}"
    );
}

#[test]
fn pinned_recursive_static_call_matches_as_a_located_source_rejection() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let result = check_pinned_scalar_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/translation/test_static_call_1.py",
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SourceWellformednessRejection
    );
    assert_eq!(result.actual.len(), 1);
    assert_eq!(result.actual[0].code, RECURSIVE_STATIC_CALL);
    assert_eq!(result.actual[0].line, 10);
}
