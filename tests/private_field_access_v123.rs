use std::fs;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_scalar_fixture};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};

const PRIVATE_FIELD_ACCESS: &str = "invalid.program:private.field.access";

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

fn assert_private_failure(source: &str, line: u32) {
    let analysis = analyze(source);
    let failures = analysis
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == PRIVATE_FIELD_ACCESS)
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{analysis:#?}");
    assert_eq!(failures[0].line, Some(line), "{analysis:#?}");
}

#[test]
fn exact_constructor_and_annotated_receivers_expose_private_accesses() {
    assert_private_failure(
        "class Secret:\n    def initialize(self) -> None:\n        self.__value = 1\ndef leak() -> int:\n    value = Secret()\n    return value.__value\n",
        6,
    );
    assert_private_failure(
        "class Secret:\n    def initialize(self) -> None:\n        self.__value = 1\ndef leak(value: Secret) -> int:\n    return value.__value\n",
        5,
    );
    assert_private_failure(
        "class Secret:\n    def initialize(self) -> None:\n        self.__value = 1\ndef leak() -> int:\n    return Secret().__value\n",
        5,
    );
}

#[test]
fn declaring_class_access_and_distinct_subclass_private_storage_are_allowed() {
    let source = "class Base:\n    def initialize(self) -> None:\n        self.__value = 1\n    def read(self) -> int:\n        return self.__value\nclass Child(Base):\n    def initialize_child(self) -> None:\n        self.__value = 2\n    def read_child(self) -> int:\n        return self.__value\n";
    let analysis = analyze(source);
    assert!(
        analysis
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != PRIVATE_FIELD_ACCESS),
        "{analysis:#?}"
    );
}

#[test]
fn subclass_access_to_a_base_private_field_is_rejected() {
    assert_private_failure(
        "class Base:\n    def initialize(self) -> None:\n        self.__value = 1\nclass Child(Base):\n    def leak(self) -> int:\n        return self.__value\n",
        6,
    );
}

#[test]
fn ambiguous_reassigned_receivers_and_dunder_protocol_names_are_not_guessed() {
    let source = "class Secret:\n    def initialize(self) -> None:\n        self.__value = 1\n    def __len__(self) -> int:\n        return 1\ndef ambiguous(flag: bool) -> int:\n    value = Secret()\n    value = object()\n    return value.__value\n";
    let analysis = analyze(source);
    assert!(
        analysis
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != PRIVATE_FIELD_ACCESS),
        "{analysis:#?}"
    );

    let shadowed_constructor = "class Secret:\n    def initialize(self) -> None:\n        self.__value = 1\ndef ambiguous(Secret: object) -> int:\n    return Secret().__value\n";
    let analysis = analyze(shadowed_constructor);
    assert!(
        analysis
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != PRIVATE_FIELD_ACCESS),
        "{analysis:#?}"
    );
}

#[test]
fn pinned_private_field_fixture_matches_as_a_located_source_rejection() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let result = check_pinned_scalar_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/translation/test_fields.py",
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SourceWellformednessRejection
    );
    assert_eq!(result.actual.len(), 1);
    assert_eq!(result.actual[0].code, PRIVATE_FIELD_ACCESS);
    assert_eq!(result.actual[0].line, 70);
}
