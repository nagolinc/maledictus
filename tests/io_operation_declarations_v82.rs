use std::fs;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};

const RETURN_TYPE: &str = "invalid.program:invalid.io_operation.return_type_not_bool";
const VARARG: &str = "invalid.program:invalid.io_operation.vararg";
const KWARG: &str = "invalid.program:invalid.io_operation.kwarg";
const DEFAULT_ARGUMENT: &str = "invalid.program:invalid.io_operation.default_argument";
const INVALID_PRESET: &str = "invalid.program:invalid.io_operation.invalid_preset";
const INVALID_POSTSET: &str = "invalid.program:invalid.io_operation.invalid_postset";

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

fn declaration_failure(source: &str) -> maledictus::protocol::Diagnostic {
    let analysis = analyze(source);
    let failures = analysis
        .diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic
                .code
                .starts_with("invalid.program:invalid.io_operation.")
        })
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{source}\n{analysis:#?}");
    failures.into_iter().next().unwrap()
}

#[test]
fn io_operation_signature_is_a_source_bound_relation_not_a_decorator_spelling() {
    let valid = "from nagini_contracts.contracts import Result as R\nfrom nagini_contracts.io_contracts import IOOperation as IO, Place as P\n@IO\ndef relation(start: P, value: int = R(), end: P = R()) -> bool:\n    return True\n";
    let analysis = analyze(valid);
    assert!(
        analysis.diagnostics.iter().all(|diagnostic| !diagnostic
            .code
            .starts_with("invalid.program:invalid.io_operation.")),
        "{analysis:#?}"
    );

    for lookalike in [
        "def IOOperation(function):\n    return function\n@IOOperation\ndef relation(value: int = 1) -> int:\n    return value\n",
        "from nagini_contracts.io_contracts import IOOperation\nIOOperation = lambda function: function\n@IOOperation\ndef relation(value: int = 1) -> int:\n    return value\n",
    ] {
        let analysis = analyze(lookalike);
        assert!(
            analysis.diagnostics.iter().all(|diagnostic| !diagnostic
                .code
                .starts_with("invalid.program:invalid.io_operation.")),
            "{lookalike}\n{analysis:#?}"
        );
    }
}

#[test]
fn every_signature_component_is_checked_before_the_relation_body() {
    for (source, expected) in [
        (
            "from nagini_contracts.contracts import Result\nfrom nagini_contracts.io_contracts import IOOperation, Place\n@IOOperation\ndef relation(start: Place) -> int:\n    return True\n",
            RETURN_TYPE,
        ),
        (
            "from nagini_contracts.io_contracts import IOOperation\n@IOOperation\ndef relation(*values: object) -> bool:\n    return True\n",
            VARARG,
        ),
        (
            "from nagini_contracts.io_contracts import IOOperation\n@IOOperation\ndef relation(**values: object) -> bool:\n    return True\n",
            KWARG,
        ),
        (
            "from nagini_contracts.io_contracts import IOOperation, Place\n@IOOperation\ndef relation(start: Place, value: int = 1) -> bool:\n    return True\n",
            DEFAULT_ARGUMENT,
        ),
        (
            "from nagini_contracts.contracts import Result\nfrom nagini_contracts.io_contracts import IOOperation, Place\n@IOOperation\ndef relation(value: int = Result()) -> bool:\n    return True\n",
            INVALID_PRESET,
        ),
        (
            "from nagini_contracts.contracts import Result\nfrom nagini_contracts.io_contracts import IOOperation, Place\n@IOOperation\ndef relation(first: Place, second: Place, value: int = Result()) -> bool:\n    return True\n",
            INVALID_PRESET,
        ),
        (
            "from nagini_contracts.contracts import Result\nfrom nagini_contracts.io_contracts import IOOperation, Place\n@IOOperation\ndef relation(start: Place, first: Place = Result(), second: Place = Result()) -> bool:\n    return True\n",
            INVALID_POSTSET,
        ),
        (
            "from nagini_contracts.contracts import Result\nfrom nagini_contracts.io_contracts import IOOperation, Place\n@IOOperation\ndef relation(start: Place, end: Place = Result(), value: int = Result()) -> bool:\n    return True\n",
            INVALID_POSTSET,
        ),
    ] {
        assert_eq!(declaration_failure(source).code, expected, "{source}");
    }
}

#[test]
fn aliases_are_accepted_but_shadowed_place_result_and_bool_are_not() {
    let shadowed_place = "from nagini_contracts.contracts import Result\nfrom nagini_contracts.io_contracts import IOOperation, Place\nPlace = object\n@IOOperation\ndef relation(start: Place, value: int = Result()) -> bool:\n    return True\n";
    assert_eq!(declaration_failure(shadowed_place).code, INVALID_PRESET);

    let shadowed_result = "from nagini_contracts.contracts import Result\nfrom nagini_contracts.io_contracts import IOOperation, Place\nResult = lambda: 1\n@IOOperation\ndef relation(start: Place, value: int = Result()) -> bool:\n    return True\n";
    assert_eq!(declaration_failure(shadowed_result).code, DEFAULT_ARGUMENT);

    let shadowed_bool = "from nagini_contracts.io_contracts import IOOperation, Place\nbool = int\n@IOOperation\ndef relation(start: Place) -> bool:\n    return True\n";
    assert_eq!(declaration_failure(shadowed_bool).code, RETURN_TYPE);

    let result_with_argument = "from nagini_contracts.contracts import Result\nfrom nagini_contracts.io_contracts import IOOperation, Place\n@IOOperation\ndef relation(start: Place, value: int = Result(1)) -> bool:\n    return True\n";
    assert_eq!(
        declaration_failure(result_with_argument).code,
        DEFAULT_ARGUMENT
    );
}

#[test]
fn all_nine_pinned_basic_signature_fixtures_match_exactly() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture_number in 1..=9 {
        let fixture = format!("tests/io/translation/test_basic_io_{fixture_number}.py");
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
