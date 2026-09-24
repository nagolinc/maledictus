use std::fs;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
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
fn exact_pinned_result_and_predicate_declaration_failures_match() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_result.py",
        "tests/functional/translation/test_result_2.py",
        "tests/functional/translation/test_result_3.py",
        "tests/functional/translation/test_result_4.py",
        "tests/functional/translation/test_result_5.py",
        "tests/functional/translation/test_predicate_1.py",
        "tests/functional/translation/test_predicate_2.py",
        "tests/functional/translation/test_predicate_3.py",
        "tests/functional/translation/test_predicate_4.py",
        "tests/functional/translation/issues/00011.py",
        "tests/functional/translation/issues/00013.py",
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
        let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("heap {fixture}: {error}"));
        assert!(heap.passed, "heap {fixture}: {heap:#?}");
        let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(reference.passed, "reference {fixture}: {reference:#?}");
    }
}

#[test]
fn valid_result_forms_and_single_expression_predicates_are_not_rejected() {
    for source in [
        "from nagini_contracts.contracts import *\ndef value() -> int:\n    Ensures(Result() == 1)\n    return 1\n",
        "from nagini_contracts.contracts import *\ndef value() -> int:\n    Ensures(int, lambda result: result == 1)\n    return 1\n",
        "from nagini_contracts.contracts import *\ndef value() -> int:\n    Ensures(ResultT(int) == 1)\n    return 1\n",
        "from nagini_contracts.contracts import *\n@Pure\ndef positive(value: int) -> bool:\n    return value > 0\n@Predicate\ndef valid(value: int) -> bool:\n    return positive(value)\n",
        "from nagini_contracts.contracts import *\n@Predicate\ndef recursive(value: int) -> bool:\n    return Implies(value > 0, recursive(value - 1))\n",
        "from nagini_contracts.contracts import *\nclass Box:\n    @Pure\n    def positive(self, value: int) -> bool:\n        return value > 0\n    @Predicate\n    def valid(self, value: int) -> bool:\n        return self.positive(value)\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis.diagnostics.iter().all(|diagnostic| !matches!(
                diagnostic.code.as_str(),
                "invalid.program:invalid.result"
                    | "invalid.program:invalid.result.type"
                    | "invalid.program:incorrect.declared.type"
                    | "invalid.program:invalid.predicate"
            )),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn shadowed_contract_spellings_do_not_gain_kernel_meaning() {
    for source in [
        "from nagini_contracts.contracts import Result\ndef empty(Result: object) -> None:\n    Result()\n",
        "from nagini_contracts.contracts import ResultT\ndef empty(ResultT: object) -> None:\n    ResultT(int)\n",
        "from nagini_contracts.contracts import Predicate\nPredicate = object\n@Predicate\ndef value() -> int:\n    return 1\n",
        "from nagini_contracts.contracts import *\ndef helper(value: int) -> int:\n    return value\n@Predicate\ndef valid(helper: object) -> bool:\n    return helper()\n",
        "from nagini_contracts.contracts import *\ndef helper(value: int) -> int:\n    return value\nhelper = object\n@Predicate\ndef valid() -> bool:\n    return helper()\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis.diagnostics.iter().all(|diagnostic| !matches!(
                diagnostic.code.as_str(),
                "invalid.program:invalid.result"
                    | "invalid.program:invalid.result.type"
                    | "invalid.program:incorrect.declared.type"
                    | "invalid.program:invalid.predicate"
            )),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn public_issuance_runs_strict_types_then_refuses_malformed_contract_declarations() {
    for (source, code) in [
        (
            "from nagini_contracts.contracts import *\ndef empty() -> None:\n    Ensures(Result() is None)\n",
            "invalid.program:invalid.result",
        ),
        (
            "from nagini_contracts.contracts import *\n@Predicate\ndef wrong() -> int:\n    return 1\n",
            "invalid.program:invalid.predicate",
        ),
    ] {
        let directory = tempfile::tempdir().unwrap();
        let response = maledictus::verify(&request(&directory, source));
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{response:#?}"
        );
        assert!(response.python_typechecker.is_some(), "{response:#?}");
        assert!(
            response
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == code),
            "{response:#?}"
        );
    }
}

#[test]
fn strict_type_error_precedes_result_wellformedness_failure() {
    let source = "from nagini_contracts.contracts import *\ndef empty() -> None:\n    Ensures(Result() is None)\n    value: int = 'wrong'\n";
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(&directory, source));
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(
        response
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code.starts_with("frontend.python.typecheck.")),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "invalid.program:invalid.result"),
        "{response:#?}"
    );
}
