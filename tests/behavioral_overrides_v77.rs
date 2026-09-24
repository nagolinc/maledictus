use std::fs;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};

const INVALID_OVERRIDE: &str = "invalid.program:invalid.override";

fn request(directory: &tempfile::TempDir, source: &str) -> ProofRequest {
    fs::write(directory.path().join("override.py"), source).unwrap();
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "override.py".to_owned(),
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
fn eight_exact_behavioral_override_fixtures_are_source_wellformedness_matches() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_behavioural_subtyping_5.py",
        "tests/functional/translation/test_behavioural_subtyping_6.py",
        "tests/functional/translation/test_behavioural_subtyping_7.py",
        "tests/functional/translation/test_behavioural_subtyping_8.py",
        "tests/functional/translation/test_behavioural_subtyping_9.py",
        "tests/functional/translation/test_behavioural_subtyping_10.py",
        "tests/functional/translation/test_behavioural_subtyping_11.py",
        "tests/functional/translation/test_behavioural_subtyping_14.py",
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
            result.python_typechecker.is_some(),
            "{fixture}: {result:#?}"
        );
    }
}

#[test]
fn ordinary_compatible_overrides_and_exception_narrowing_are_not_rejected() {
    for source in [
        "class Base:\n    def value(self, item: int) -> int:\n        return item\nclass Derived(Base):\n    def value(self, item: int) -> int:\n        return item + 1\n",
        "from nagini_contracts.contracts import *\nclass Failure(Exception):\n    pass\nclass NarrowFailure(Failure):\n    pass\nclass Base:\n    def value(self) -> int:\n        Exsures(Failure, True)\n        return 1\nclass Derived(Base):\n    def value(self) -> int:\n        Exsures(NarrowFailure, True)\n        return 2\n",
        "from nagini_contracts.contracts import *\nclass Standalone:\n    @Pure\n    def value(self) -> int:\n        return 1\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != INVALID_OVERRIDE),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn ordinary_constructor_signature_changes_preserve_the_existing_exact_fixture() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let result = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/verification/test_constructor.py",
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SemanticVerification,
        "{result:#?}"
    );
}

#[test]
fn zero_argument_factory_obligation_tracks_effective_class_method_dispatch() {
    let inherited_zero_argument_factory = analyze(
        "class Base:\n    @classmethod\n    def construct(cls) -> object:\n        return cls()\nclass Derived(Base):\n    def __init__(self, item: int) -> None:\n        self.item = item\n",
    );
    assert!(
        inherited_zero_argument_factory
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == INVALID_OVERRIDE),
        "{inherited_zero_argument_factory:#?}"
    );

    for source in [
        "class Base:\n    @classmethod\n    def construct(cls) -> object:\n        return cls()\nclass Derived(Base):\n    def __init__(self, item: int = 1) -> None:\n        self.item = item\n",
        "class Base:\n    @classmethod\n    def construct(cls) -> object:\n        return cls()\nclass Derived(Base):\n    def __init__(self, item: int) -> None:\n        self.item = item\n    @classmethod\n    def construct(cls) -> object:\n        return cls(1)\n",
        "classmethod = lambda function: function\nclass Base:\n    @classmethod\n    def construct(cls) -> object:\n        return cls()\nclass Derived(Base):\n    def __init__(self, item: int) -> None:\n        self.item = item\n",
        "class Base:\n    @classmethod\n    def construct(cls, item: int) -> object:\n        return cls()\nclass Derived(Base):\n    def __init__(self, item: int) -> None:\n        self.item = item\n",
        "class Base:\n    @classmethod\n    def construct(cls) -> object:\n        return cls()\nclass Derived(Base):\n    def __init__(self, item: int) -> None:\n        self.item = item\n    construct = 1\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != INVALID_OVERRIDE),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn override_rules_reject_only_proven_kind_keyword_and_exception_incompatibilities() {
    for source in [
        "from nagini_contracts.contracts import *\nclass Base:\n    def value(self, item: int) -> int:\n        return item\nclass Derived(Base):\n    @Pure\n    def value(self, item: int) -> int:\n        return item\n",
        "class Base:\n    def value(self, item: int) -> int:\n        return item\nclass Derived(Base):\n    def value(self, renamed: int) -> int:\n        return renamed\n",
        "class Base:\n    def value(self, item: int) -> int:\n        return item\nclass Derived(Base):\n    def value(self, item: int = 1) -> int:\n        return item\n",
        "from nagini_contracts.contracts import *\nclass First(Exception):\n    pass\nclass Second(Exception):\n    pass\nclass Base:\n    def value(self) -> int:\n        Exsures(First, True)\n        return 1\nclass Derived(Base):\n    def value(self) -> int:\n        Exsures(Second, True)\n        return 2\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == INVALID_OVERRIDE),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn default_values_and_constructor_defaults_remain_compatible() {
    for source in [
        "class Base:\n    def value(self, item: int = 1) -> int:\n        return item\nclass Derived(Base):\n    def value(self, item: int = 1) -> int:\n        return item\n",
        "class Base:\n    def value(self, item: int = 1) -> int:\n        return item\nclass Derived(Base):\n    def value(self, item: int = 2) -> int:\n        return item\n",
        "class Base:\n    def __init__(self) -> None:\n        pass\nclass Derived(Base):\n    def __init__(self, item: int = 1) -> None:\n        self.item = item\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != INVALID_OVERRIDE),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn differing_default_values_preserve_the_existing_behavioral_semantic_fixture() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let result = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/verification/test_behavioural_subtyping.py",
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SemanticVerification,
        "{result:#?}"
    );
}

#[test]
fn unproved_property_cases_remain_outside_this_rule() {
    let fixture = "tests/functional/translation/test_behavioural_subtyping_15.py";
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let source = fs::read_to_string(repository.join(".upstream/nagini").join(fixture)).unwrap();
    let analysis = analyze(&source);
    assert!(
        analysis
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != INVALID_OVERRIDE),
        "{fixture}: {analysis:#?}"
    );
}

#[test]
fn public_issuance_runs_strict_typecheck_before_override_rejection() {
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(
        &directory,
        "class Base:\n    def value(self, item: int) -> int:\n        return item\nclass Derived(Base):\n    def value(self, renamed: int) -> int:\n        return renamed\n",
    ));
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(
        response
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == INVALID_OVERRIDE),
        "{response:#?}"
    );
}
