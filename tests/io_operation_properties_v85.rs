use std::{fs, path::Path};

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};
use maledictus::python_io_wellformedness::{
    DUPLICATE_PROPERTY, MISPLACED_PROPERTY, PROPERTY_DEPENDS_ON_NON_INPUT,
    validate_io_wellformedness,
};

fn operation_prefix() -> &'static str {
    concat!(
        "from nagini_contracts.contracts import Result as R\n",
        "from nagini_contracts.io_contracts import ",
        "IOOperation as IO, Place as P, Terminates as T, TerminationMeasure as M\n",
    )
}

fn failure(source: &str) -> maledictus::python_io_wellformedness::IoWellformednessFailure {
    validate_io_wellformedness(source, "program.py")
        .expect_err("source unexpectedly passed IO-property validation")
}

#[test]
fn direct_properties_may_depend_on_real_value_inputs() {
    let source = format!(
        "{}@IO\ndef relation(start: P, amount: int, value: int = R(), end: P = R()) -> bool:\n    T(amount > 0)\n    M(amount)\n    return True\n",
        operation_prefix()
    );
    validate_io_wellformedness(&source, "program.py").unwrap();
}

#[test]
fn properties_are_rejected_outside_direct_io_operation_statements() {
    let sources = [
        format!("{}T(True)\n", operation_prefix()),
        format!(
            "{}def ordinary(value: bool) -> None:\n    T(value)\n",
            operation_prefix()
        ),
        format!(
            "{}class Consumer:\n    def method(self, value: bool) -> None:\n        T(value)\n",
            operation_prefix()
        ),
        format!(
            "{}@IO\ndef relation(start: P, amount: int, end: P = R()) -> bool:\n    if amount > 0:\n        T(True)\n    return True\n",
            operation_prefix()
        ),
        format!(
            "{}@IO\ndef relation(start: P, amount: int, end: P = R()) -> bool:\n    T(M(amount))\n    return True\n",
            operation_prefix()
        ),
    ];
    for source in sources {
        assert_eq!(failure(&source).code, MISPLACED_PROPERTY, "{source}");
    }
}

#[test]
fn place_tokens_and_outputs_are_not_operation_inputs() {
    for expression in ["start == end", "value > 0"] {
        let source = format!(
            "{}@IO\ndef relation(start: P, amount: int, value: int = R(), end: P = R()) -> bool:\n    T({expression})\n    return True\n",
            operation_prefix()
        );
        assert_eq!(
            failure(&source).code,
            PROPERTY_DEPENDS_ON_NON_INPUT,
            "{source}"
        );
    }
}

#[test]
fn duplicate_kind_precedes_the_second_property_argument() {
    let source = format!(
        "{}@IO\ndef relation(start: P, amount: int, value: int = R()) -> bool:\n    T(amount > 0)\n    T(value > 0)\n    return True\n",
        operation_prefix()
    );
    assert_eq!(failure(&source).code, DUPLICATE_PROPERTY);
}

#[test]
fn lookalikes_and_python_shadows_do_not_acquire_property_semantics() {
    for source in [
        "def Terminates(value: bool) -> None:\n    pass\ndef ordinary(value: bool) -> None:\n    Terminates(value)\n".to_owned(),
        "from nagini_contracts.io_contracts import Terminates\nTerminates = lambda value: None\ndef ordinary(value: bool) -> None:\n    Terminates(value)\n".to_owned(),
        "from nagini_contracts.io_contracts import Terminates\ndef ordinary(Terminates: object, value: bool) -> None:\n    Terminates(value)\n".to_owned(),
    ] {
        validate_io_wellformedness(&source, "program.py").unwrap();
    }
}

#[test]
fn malformed_declaration_precedes_a_misplaced_property() {
    let source = concat!(
        "from nagini_contracts.io_contracts import IOOperation, Place, Terminates\n",
        "@IOOperation\n",
        "def broken(start: Place) -> int:\n",
        "    if True:\n",
        "        Terminates(True)\n",
        "    return 1\n",
    );
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
            .all(|diagnostic| diagnostic.code != MISPLACED_PROPERTY),
        "{analysis:#?}"
    );
}

#[test]
fn all_eight_pinned_io_property_fixtures_match_exactly() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/io/translation/test_basic_io_11.py",
        "tests/io/translation/test_basic_io_12.py",
        "tests/io/translation/test_basic_io_13.py",
        "tests/io/translation/test_basic_io_15.py",
        "tests/io/translation/test_basic_io_16.py",
        "tests/io/translation/test_basic_io_19.py",
        "tests/io/translation/test_duplicate_property_1.py",
        "tests/io/translation/test_duplicate_property_2.py",
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
