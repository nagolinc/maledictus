use std::fs;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_scalar_fixture};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};

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
fn all_pinned_invalid_contract_positions_are_located_exactly() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(".upstream/nagini");
    for (fixture, line) in [
        ("tests/sif-true/translation/test_lowexit.py", 11),
        ("tests/sif-true/translation/test_lowevent.py", 11),
        ("tests/functional/translation/issues/00025.py", 12),
        ("tests/functional/translation/issues/00018.py", 11),
        ("tests/functional/translation/issues/00014.py", 8),
        ("tests/functional/translation/issues/00060.py", 18),
        ("tests/functional/translation/test_acc_5.py", 11),
        ("tests/functional/translation/issues/00111.py", 18),
        ("tests/functional/translation/issues/00142_1.py", 28),
        ("tests/functional/translation/issues/00142_2.py", 25),
        ("tests/functional/translation/issues/00185.py", 8),
        ("tests/functional/translation/test_acc_4.py", 10),
        ("tests/functional/translation/issues/00238.py", 22),
        ("tests/functional/translation/test_contract_1.py", 9),
        ("tests/functional/translation/test_contract_2.py", 12),
        ("tests/functional/translation/test_contract_3.py", 9),
        (
            "tests/obligations/translation/test_pure_mustterminate.py",
            14,
        ),
        ("tests/functional/translation/test_decreases_impure.py", 8),
        ("tests/functional/translation/test_impure_1.py", 15),
        ("tests/functional/translation/test_impure_2.py", 15),
        ("tests/functional/translation/test_impure_3.py", 19),
        ("tests/functional/translation/test_impure_4.py", 19),
        ("tests/functional/translation/test_impure_5.py", 19),
        ("tests/functional/translation/test_unfolding_2.py", 21),
    ] {
        let source = fs::read_to_string(repository.join(fixture)).unwrap();
        let analysis = analyze(&source);
        let diagnostics = analysis
            .diagnostics
            .iter()
            .filter(|item| item.code == "invalid.program:invalid.contract.position")
            .collect::<Vec<_>>();
        assert_eq!(diagnostics.len(), 1, "{fixture}: {analysis:#?}");
        assert_eq!(diagnostics[0].line, Some(line), "{fixture}: {analysis:#?}");
    }
}

#[test]
fn all_pinned_positions_match_the_explicit_wellformedness_rejection_category() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/sif-true/translation/test_lowexit.py",
        "tests/sif-true/translation/test_lowevent.py",
        "tests/functional/translation/issues/00025.py",
        "tests/functional/translation/issues/00018.py",
        "tests/functional/translation/issues/00014.py",
        "tests/functional/translation/issues/00060.py",
        "tests/functional/translation/test_acc_5.py",
        "tests/functional/translation/issues/00111.py",
        "tests/functional/translation/issues/00185.py",
        "tests/functional/translation/test_acc_4.py",
        "tests/functional/translation/issues/00238.py",
        "tests/functional/translation/test_contract_1.py",
        "tests/functional/translation/test_contract_2.py",
        "tests/functional/translation/test_contract_3.py",
        "tests/functional/translation/test_decreases_impure.py",
        "tests/functional/translation/test_impure_1.py",
        "tests/functional/translation/test_impure_2.py",
        "tests/functional/translation/test_impure_3.py",
        "tests/functional/translation/test_impure_4.py",
        "tests/functional/translation/test_impure_5.py",
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
fn valid_fractional_permissions_and_sif_loop_invariants_are_not_overflagged() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(".upstream/nagini");
    for fixture in [
        "tests/arp/translation/test_acc_func.py",
        "tests/sif-true/verification/test_while_3.py",
        "tests/functional/verification/test_global_mutable_2.py",
        "tests/io/verification/test_io_exists.py",
    ] {
        let source = fs::read_to_string(repository.join(fixture)).unwrap();
        let analysis = analyze(&source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|item| item.code != "invalid.program:invalid.contract.position"),
            "{fixture}: {analysis:#?}"
        );
    }
}

#[test]
fn comment_free_adversarial_positions_refuse_by_ast_context() {
    for source in [
        "from nagini_contracts.contracts import Requires\nRequires(True)\n",
        "from nagini_contracts.contracts import *\ndef f() -> None:\n    Ensures(True)\n    Requires(True)\n",
        "from nagini_contracts.contracts import *\ndef f() -> None:\n    while True:\n        x = 1\n        Invariant(x == 1)\n",
        "from nagini_contracts.contracts import Assert\ndef f() -> None:\n    Assert(Assert(True))\n",
        "from nagini_contracts.contracts import Assert\nAssert(Assert(True))\n",
        "from nagini_contracts.contracts import *\nclass A:\n    @Predicate\n    def p(self) -> bool:\n        return True\ndef f(a: A) -> None:\n    if a.p():\n        pass\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .any(|item| item.code == "invalid.program:invalid.contract.position"),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn definitely_shadowed_contract_names_are_not_misclassified_as_nagini_primitives() {
    for source in [
        "from nagini_contracts.contracts import Requires\nRequires = print\nRequires(True)\n",
        "from nagini_contracts.contracts import Requires\ndef f(Requires: object) -> None:\n    Requires(True)\n",
        "from nagini_contracts.contracts import Requires\ndef f() -> None:\n    Requires = print\n    Requires(True)\n",
        "def f() -> None:\n    Requires(True)\nfrom nagini_contracts.contracts import Requires\n",
        "from nagini_contracts.io_contracts import IOExists15\ndef f(IOExists15: object) -> None:\n    IOExists15(lambda value: value)\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|item| item.code != "invalid.program:invalid.contract.position"),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn valid_neighbor_contract_positions_do_not_trigger_the_preflight() {
    for source in [
        "from nagini_contracts.contracts import *\ndef f(x: int) -> int:\n    Requires(x >= 0)\n    Ensures(Result() >= 0)\n    return x\n",
        "from nagini_contracts.contracts import *\ndef f() -> None:\n    while True:\n        Invariant(True)\n        break\n",
        "from nagini_contracts.contracts import *\nclass A:\n    def __init__(self) -> None:\n        self.x = 1\n    @Predicate\n    def p(self) -> bool:\n        return Acc(self.x)\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|item| item.code != "invalid.program:invalid.contract.position"),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn production_issuance_runs_strict_mypy_before_located_position_rejection() {
    let source = "from nagini_contracts.contracts import Requires\nRequires(True)\n";
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(&directory, source));
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(
        response.diagnostics.iter().any(|item| {
            item.code == "invalid.program:invalid.contract.position" && item.line == Some(2)
        }),
        "{response:#?}"
    );
}
