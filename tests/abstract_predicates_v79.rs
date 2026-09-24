use std::fs;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};

const ABSTRACT_FOLD: &str = "invalid.program:abstract.predicate.fold";
const INVALID_CALL: &str = "invalid.program:invalid.contract.call";

fn request(directory: &tempfile::TempDir, source: &str) -> ProofRequest {
    fs::write(directory.path().join("abstract_predicate.py"), source).unwrap();
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "abstract_predicate.py".to_owned(),
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

fn codes(analysis: &maledictus::FrontendAnalysis) -> Vec<&str> {
    analysis
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code.as_str())
        .collect()
}

#[test]
fn four_exact_abstract_predicate_fixtures_match_every_backend() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_abstract_pred_1.py",
        "tests/functional/translation/test_abstract_pred_2.py",
        "tests/functional/translation/test_abstract_pred_3.py",
        "tests/functional/translation/test_abstract_pred_4.py",
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
fn concrete_and_abstract_global_predicates_remain_distinct() {
    let concrete = analyze(
        "from nagini_contracts.contracts import *\n@Predicate\ndef ready(value: int) -> bool:\n    return value > 0\ndef use(value: int) -> None:\n    Fold(ready(value))\n",
    );
    assert!(!codes(&concrete).contains(&ABSTRACT_FOLD), "{concrete:#?}");

    for primitive in ["Fold", "Unfold"] {
        let source = format!(
            "from nagini_contracts.contracts import *\n@Predicate\n@ContractOnly\ndef ready(value: int) -> bool:\n    return True\ndef use(value: int) -> None:\n    {primitive}(ready(value))\n"
        );
        let abstract_predicate = analyze(&source);
        assert_eq!(
            codes(&abstract_predicate),
            [ABSTRACT_FOLD],
            "{source}\n{abstract_predicate:#?}"
        );
    }
    let unfolding = analyze(
        "from nagini_contracts.contracts import *\n@Predicate\n@ContractOnly\ndef ready(value: int) -> bool:\n    return True\ndef use(value: int) -> int:\n    return Unfolding(ready(value), 1)\n",
    );
    assert_eq!(codes(&unfolding), [ABSTRACT_FOLD], "{unfolding:#?}");
}

#[test]
fn receiver_provenance_controls_abstract_method_resolution() {
    let inherited = analyze(
        "from nagini_contracts.contracts import *\nclass Base:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\nclass Child(Base):\n    pass\ndef use(value: Child) -> None:\n    Fold(value.ready())\n",
    );
    assert_eq!(codes(&inherited), [ABSTRACT_FOLD], "{inherited:#?}");

    let concrete_override = analyze(
        "from nagini_contracts.contracts import *\nclass Base:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\nclass Child(Base):\n    @Predicate\n    def ready(self) -> bool:\n        return True\ndef use(value: Child) -> None:\n    Fold(value.ready())\n",
    );
    assert!(
        !codes(&concrete_override).contains(&ABSTRACT_FOLD),
        "{concrete_override:#?}"
    );

    for source in [
        "from nagini_contracts.contracts import *\nclass Item:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\ndef use(value: object) -> None:\n    Fold(value.ready())\n",
        "from nagini_contracts.contracts import *\nclass Item:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\ndef use(value: Item, other: Item) -> None:\n    value = other\n    Fold(value.ready())\n",
        "from nagini_contracts.contracts import *\nclass Item:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\ndef make() -> Item:\n    return Item()\ndef use() -> None:\n    Fold(make().ready())\n",
    ] {
        let unknown = analyze(source);
        assert_eq!(codes(&unknown), [INVALID_CALL], "{source}\n{unknown:#?}");
    }
}

#[test]
fn canonical_aliases_work_but_rebound_decorators_and_predicates_are_not_trusted() {
    let aliases = analyze(
        "from nagini_contracts.contracts import Predicate as P, ContractOnly as C, Fold\n@P\n@C\ndef ready(value: int) -> bool:\n    return True\ndef use(value: int) -> None:\n    Fold(ready(value))\n",
    );
    assert_eq!(codes(&aliases), [ABSTRACT_FOLD], "{aliases:#?}");

    for source in [
        "from nagini_contracts.contracts import *\nContractOnly = lambda value: value\n@Predicate\n@ContractOnly\ndef ready(value: int) -> bool:\n    return True\ndef use(value: int) -> None:\n    Fold(ready(value))\n",
        "from nagini_contracts.contracts import *\n@Predicate\n@ContractOnly\ndef ready(value: int) -> bool:\n    return True\nready = lambda value: True\ndef use(value: int) -> None:\n    Fold(ready(value))\n",
    ] {
        let rebound = analyze(source);
        assert!(
            !codes(&rebound).contains(&ABSTRACT_FOLD) && !rebound.diagnostics.is_empty(),
            "{source}\n{rebound:#?}"
        );
    }
}

#[test]
fn permission_wrappers_preserve_abstract_predicate_identity() {
    for wrapper in ["Acc", "Rd"] {
        let source = format!(
            "from nagini_contracts.contracts import *\n@Predicate\n@ContractOnly\ndef ready(value: int) -> bool:\n    return True\ndef use(value: int) -> None:\n    Fold({wrapper}(ready(value)))\n"
        );
        let analysis = analyze(&source);
        assert_eq!(codes(&analysis), [ABSTRACT_FOLD], "{source}\n{analysis:#?}");
    }
}

#[test]
fn public_issuance_runs_strict_typecheck_before_abstract_fold_rejection() {
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(
        &directory,
        "from nagini_contracts.contracts import *\n@Predicate\n@ContractOnly\ndef ready(value: int) -> bool:\n    return True\ndef use(value: int) -> None:\n    Fold(ready(value))\n",
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
            .any(|diagnostic| diagnostic.code == ABSTRACT_FOLD),
        "{response:#?}"
    );
}

#[test]
fn verified_dynamic_class_factory_preserves_exact_receiver_provenance() {
    let analysis = analyze(
        "from nagini_contracts.contracts import *\nclass Base:\n    @Predicate\n    def ready(self) -> bool:\n        return True\n    @classmethod\n    def make(cls) -> 'Base':\n        value = cls()\n        return value\nclass Child(Base):\n    pass\ndef use() -> None:\n    value = Child.make()\n    Fold(value.ready())\n",
    );
    assert!(!codes(&analysis).contains(&INVALID_CALL), "{analysis:#?}");
}

#[test]
fn prior_valid_abstract_predicate_neighbors_are_not_overflagged() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for fixture in [
        "tests/functional/verification/test_classmethod.py",
        "tests/functional/verification/test_predicate_abstract.py",
        "tests/functional/verification/test_union_contracts.py",
    ] {
        let source = fs::read_to_string(repository.join(".upstream/nagini").join(fixture)).unwrap();
        let analysis = analyze(&source);
        assert!(
            !codes(&analysis).contains(&ABSTRACT_FOLD) && !codes(&analysis).contains(&INVALID_CALL),
            "{fixture}: {analysis:#?}"
        );
    }
}

#[test]
fn abstract_stub_exemption_does_not_escape_the_predicate_body() {
    let stub = analyze(
        "from nagini_contracts.contracts import *\n@Predicate\n@ContractOnly\ndef ready(value: int) -> bool:\n    return True\n@Pure\n@ContractOnly\ndef specification(value: int) -> int:\n    return Unfolding(ready(value), 1)\n",
    );
    assert!(!codes(&stub).contains(&ABSTRACT_FOLD), "{stub:#?}");

    let executable = analyze(
        "from nagini_contracts.contracts import *\n@Predicate\n@ContractOnly\ndef ready(value: int) -> bool:\n    return True\n@Pure\ndef executable(value: int) -> int:\n    return Unfolding(ready(value), 1)\n",
    );
    assert_eq!(codes(&executable), [ABSTRACT_FOLD], "{executable:#?}");
}

#[test]
fn union_receiver_resolution_requires_unanimous_exact_predicate_kinds() {
    let unanimous = analyze(
        "from typing import Union\nfrom nagini_contracts.contracts import *\nclass Left:\n    @Predicate\n    def ready(self) -> bool:\n        return True\nclass Right:\n    @Predicate\n    def ready(self) -> bool:\n        return True\ndef use(value: Union[Left, Right]) -> None:\n    Fold(value.ready())\n",
    );
    assert!(!codes(&unanimous).contains(&INVALID_CALL), "{unanimous:#?}");

    for right_method in [
        "    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\n",
        "    def other(self) -> bool:\n        return True\n",
    ] {
        let source = format!(
            "from typing import Union\nfrom nagini_contracts.contracts import *\nclass Left:\n    @Predicate\n    def ready(self) -> bool:\n        return True\nclass Right:\n{right_method}def use(value: Union[Left, Right]) -> None:\n    Fold(value.ready())\n"
        );
        let analysis = analyze(&source);
        assert_eq!(codes(&analysis), [INVALID_CALL], "{source}\n{analysis:#?}");
    }
}

#[test]
fn only_dynamic_class_factories_create_exact_result_provenance() {
    for factory in [
        "    @classmethod\n    def make(cls) -> 'Base':\n        return Base()\n",
        "    @staticmethod\n    def make() -> 'Base':\n        return Base()\n",
    ] {
        let source = format!(
            "from nagini_contracts.contracts import *\nclass Base:\n    @Predicate\n    def ready(self) -> bool:\n        return True\n{factory}class Child(Base):\n    pass\ndef use() -> None:\n    value = Child.make()\n    Fold(value.ready())\n"
        );
        let analysis = analyze(&source);
        assert_eq!(codes(&analysis), [INVALID_CALL], "{source}\n{analysis:#?}");
    }
}
