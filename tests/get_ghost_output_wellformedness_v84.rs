use std::{fs, path::Path};

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};
use maledictus::python_io_wellformedness::{
    ARGUMENT_NOT_IO_OPERATION, INVALID_RESULT_IDENTIFIER, MULTIPLE_TARGETS,
    RESULT_IDENTIFIER_NOT_STRING, TARGET_NOT_VARIABLE, TARGET_TYPE_UNKNOWN, TYPE_MISMATCH,
    validate_io_wellformedness,
};

fn operation_prefix() -> &'static str {
    concat!(
        "from nagini_contracts.contracts import Result as R\n",
        "from nagini_contracts.io_contracts import ",
        "GetGhostOutput as Ghost, IOOperation as IO, Place as P\n",
        "@IO\n",
        "def relation(start: P, value: int = R(), end: P = R()) -> bool:\n",
        "    return True\n\n",
    )
}

fn failure(body: &str) -> maledictus::python_io_wellformedness::IoWellformednessFailure {
    let source = format!("{}{}", operation_prefix(), body);
    validate_io_wellformedness(&source, "program.py")
        .expect_err("source unexpectedly passed GetGhostOutput validation")
}

#[test]
fn canonical_aliases_and_nested_assignments_are_valid() {
    let source = format!(
        "{}def use(start: P, flag: bool) -> None:\n    if flag:\n        end = Ghost(relation(start), 'end')  # type: P\n",
        operation_prefix()
    );
    validate_io_wellformedness(&source, "program.py").unwrap();
}

#[test]
fn class_methods_cannot_bypass_ghost_output_validation() {
    let failure = failure(
        "class Consumer:\n    def use(self, start: P) -> None:\n        end = Ghost(relation(start), 'value')  # type: P\n",
    );
    assert_eq!(failure.code, TYPE_MISMATCH);
}

#[test]
fn malformed_operation_declarations_precede_uses_of_their_outputs() {
    let source = "from nagini_contracts.contracts import Result\nfrom nagini_contracts.io_contracts import GetGhostOutput, IOOperation, Place\n@IOOperation\ndef broken(start: Place, value: int = Result()) -> int:\n    return 1\ndef use(start: Place) -> None:\n    end = GetGhostOutput(True, 'missing')  # type: Place\n";
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("program.py"), source).unwrap();
    let analysis = maledictus::analyze_python_frontend(&ProofRequest {
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
    });
    assert!(
        analysis.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "invalid.program:invalid.io_operation.return_type_not_bool"
        }),
        "{analysis:#?}"
    );
    assert!(
        analysis
            .diagnostics
            .iter()
            .all(|diagnostic| !diagnostic.code.contains("invalid.get_ghost_output")),
        "{analysis:#?}"
    );
}

#[test]
fn lookalikes_and_local_shadows_do_not_acquire_ghost_semantics() {
    for source in [
        "def GetGhostOutput(operation: bool, name: str) -> int:\n    return 1\ndef use() -> None:\n    value = GetGhostOutput(True, 'value')  # type: int\n",
        "from nagini_contracts.io_contracts import GetGhostOutput\ndef use(GetGhostOutput: object) -> None:\n    value = GetGhostOutput(True, 'value')  # type: int\n",
        "from nagini_contracts.io_contracts import GetGhostOutput\nGetGhostOutput = lambda operation, name: 1\ndef use() -> None:\n    value = GetGhostOutput(True, 'value')  # type: int\n",
    ] {
        validate_io_wellformedness(source, "program.py").unwrap();
    }
}

#[test]
fn assignment_shape_and_literal_identifier_are_closed() {
    assert_eq!(
        failure("def use(start: P) -> None:\n    first = second = Ghost(relation(start), 'end')  # type: P\n").code,
        MULTIPLE_TARGETS
    );
    assert_eq!(
        failure("def use(start: P) -> None:\n    first, second = Ghost(relation(start), 'end')  # type: P\n").code,
        TARGET_NOT_VARIABLE
    );
    assert_eq!(
        failure("def use(start: P, name: str) -> None:\n    end = Ghost(relation(start), name)  # type: P\n").code,
        RESULT_IDENTIFIER_NOT_STRING
    );
}

#[test]
fn operation_and_output_must_come_from_the_source_catalog() {
    assert_eq!(
        failure("def use(start: P) -> None:\n    end = Ghost(relation(start) and True, 'end')  # type: P\n").code,
        ARGUMENT_NOT_IO_OPERATION
    );
    assert_eq!(
        failure("def ordinary(start: P) -> bool:\n    return True\ndef use(start: P) -> None:\n    end = Ghost(ordinary(start), 'end')  # type: P\n").code,
        ARGUMENT_NOT_IO_OPERATION
    );
    assert_eq!(
        failure(
            "def use(start: P) -> None:\n    end = Ghost(relation(start), 'missing')  # type: P\n"
        )
        .code,
        INVALID_RESULT_IDENTIFIER
    );
}

#[test]
fn target_type_is_checked_and_missing_type_evidence_fails_closed() {
    assert_eq!(
        failure(
            "def use(start: P) -> None:\n    end = Ghost(relation(start), 'value')  # type: P\n"
        )
        .code,
        TYPE_MISMATCH
    );
    assert_eq!(
        failure("def use(start: P) -> None:\n    end = Ghost(relation(start), 'end')\n").code,
        TARGET_TYPE_UNKNOWN
    );
}

#[test]
fn all_seven_pinned_get_ghost_output_fixtures_match_exactly() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/io/translation/get_ghost_output/test_argument_not_io_operation_1.py",
        "tests/io/translation/get_ghost_output/test_argument_not_io_operation_2.py",
        "tests/io/translation/get_ghost_output/test_invalid_result_identifier_1.py",
        "tests/io/translation/get_ghost_output/test_multiple_targets_1.py",
        "tests/io/translation/get_ghost_output/test_result_identifier_not_str_1.py",
        "tests/io/translation/get_ghost_output/test_target_not_var_1.py",
        "tests/io/translation/get_ghost_output/test_type_mismatch_1.py",
    ] {
        let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("scalar {fixture}: {error}"));
        assert!(scalar.passed, "scalar {fixture}: {scalar:#?}");
        assert_eq!(
            scalar.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection,
            "scalar {fixture}: {scalar:#?}"
        );

        let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("heap {fixture}: {error}"));
        assert!(heap.passed, "heap {fixture}: {heap:#?}");

        let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(reference.passed, "reference {fixture}: {reference:#?}");
    }
}
