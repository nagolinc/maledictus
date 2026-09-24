use std::fs;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_scalar_fixture};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};

const INVALID_CONTRACT_CALL: &str = "invalid.program:invalid.contract.call";

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
fn exact_invalid_predicate_contract_calls_match_all_five_pinned_fixtures() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_fold.py",
        "tests/functional/translation/test_unfold.py",
        "tests/functional/translation/test_unfolding_1.py",
        "tests/functional/translation/test_pure_unfold_1.py",
        "tests/functional/translation/test_pure_unfold_2.py",
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
fn declared_predicate_calls_and_canonical_import_aliases_are_valid_operands() {
    for source in [
        "from nagini_contracts.contracts import Fold as F, Predicate as P, Unfold as U, Unfolding as UG\n@P\ndef state(value: int) -> bool:\n    return value >= 0\ndef client(value: int) -> int:\n    F(state(value))\n    U(state(value))\n    return UG(state(value), value)\n",
        "from nagini_contracts.contracts import *\nclass Cell:\n    @Predicate\n    def state(self) -> bool:\n        return True\n    def use(self) -> None:\n        Fold(self.state())\n        Unfold(self.state())\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != INVALID_CONTRACT_CALL),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn permission_wrappers_and_deferred_final_global_predicates_do_not_overflag() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for fixture in [
        "tests/functional/verification/test_pure_unfold.py",
        "tests/functional/verification/test_wildcard_permissions.py",
        "tests/arp/verification/test_chalice_rdringbuffer.py",
        "tests/functional/verification/test_predicate.py",
    ] {
        let source = fs::read_to_string(repository.join(".upstream/nagini").join(fixture))
            .unwrap_or_else(|error| panic!("{fixture}: {error}"));
        let analysis = analyze(&source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != INVALID_CONTRACT_CALL),
            "{fixture}: {analysis:#?}"
        );
    }
}

#[test]
fn nonpredicate_dynamic_and_rebound_operands_fail_closed() {
    for source in [
        "from nagini_contracts.contracts import *\ndef ordinary() -> bool:\n    return True\ndef client() -> None:\n    Fold(ordinary())\n",
        "from nagini_contracts.contracts import *\n@Pure\ndef pure() -> bool:\n    return True\ndef client() -> None:\n    Unfold(pure())\n",
        "from nagini_contracts.contracts import *\ndef client(factory: object) -> int:\n    return Unfolding(factory()(), 1)\n",
        "from nagini_contracts.contracts import *\n@Predicate\ndef state() -> bool:\n    return True\ndef client(state: object) -> None:\n    Fold(state())\n",
        "from nagini_contracts.contracts import *\n@Predicate\ndef state() -> bool:\n    return True\nalias = state\ndef client() -> None:\n    Fold(alias())\n",
        "from nagini_contracts.contracts import *\ndef ordinary() -> bool:\n    return True\ndef client() -> None:\n    Unfold(Acc(ordinary()))\n",
        "from nagini_contracts.contracts import *\n@Pure\ndef pure() -> bool:\n    return True\ndef client() -> None:\n    Unfold(Rd(pure()))\n",
        "from nagini_contracts.contracts import *\ndef client() -> None:\n    Fold(Acc(True))\n",
        "from nagini_contracts.contracts import *\ndef client() -> None:\n    Unfold(Acc(lambda: True))\n",
        "from nagini_contracts.contracts import *\ndef client() -> None:\n    Unfold(Acc())\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == INVALID_CONTRACT_CALL),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn deferred_predicates_apply_only_to_runtime_function_lookup() {
    let valid = analyze(
        "from nagini_contracts.contracts import *\ndef client() -> None:\n    Fold(state())\n@Predicate\ndef state() -> bool:\n    return True\n",
    );
    assert!(
        valid
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != INVALID_CONTRACT_CALL),
        "{valid:#?}"
    );

    for source in [
        "from nagini_contracts.contracts import *\nFold(state())\n@Predicate\ndef state() -> bool:\n    return True\n",
        "from nagini_contracts.contracts import *\ndef client() -> None:\n    Fold(state())\n@Predicate\ndef state() -> bool:\n    return True\nstate = print\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == INVALID_CONTRACT_CALL),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn definitely_shadowed_contract_primitive_is_not_given_contract_meaning() {
    let source = "from nagini_contracts.contracts import Fold\nFold = print\nFold(True)\n";
    let result = analyze(source);
    assert!(
        result
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != INVALID_CONTRACT_CALL),
        "{result:#?}"
    );
}

#[test]
fn public_issuance_runs_strict_typecheck_before_located_contract_call_rejection() {
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(
        &directory,
        "from nagini_contracts.contracts import Fold\ndef client() -> None:\n    Fold(True)\n",
    ));
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(
        response.diagnostics.iter().any(
            |diagnostic| diagnostic.code == INVALID_CONTRACT_CALL && diagnostic.line == Some(3)
        ),
        "{response:#?}"
    );
}

#[test]
fn pure_return_completeness_traverses_match_case_bodies() {
    let analysis = analyze(
        "from nagini_contracts.contracts import *\n@Pure\ndef choose(value: bool) -> bool:\n    match value:\n        case True:\n            return True\n        case False:\n            return False\n",
    );
    assert!(
        analysis
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "invalid.program:function.return.missing"),
        "{analysis:#?}"
    );
}

#[test]
fn pure_and_io_operation_aliases_are_incompatible_before_completeness() {
    let invalid = analyze(
        "from nagini_contracts.contracts import Pure as P\nfrom nagini_contracts.io_contracts import IOOperation as IO\n@P\n@IO\ndef operation() -> bool:\n    pass\n",
    );
    assert!(
        invalid
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "invalid.program:decorators.incompatible"),
        "{invalid:#?}"
    );

    let rebound = analyze(
        "from nagini_contracts.contracts import Pure\nfrom nagini_contracts.io_contracts import IOOperation\nIOOperation = object\n@Pure\n@IOOperation\ndef operation() -> bool:\n    return True\n",
    );
    assert!(
        rebound
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "invalid.program:decorators.incompatible"),
        "{rebound:#?}"
    );
}
