use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_io_wellformedness::{
    EXISTENTIAL_DEFINITION_TYPE_MISMATCH, EXISTENTIAL_USE_UNDEFINED,
    OPERATION_RESULT_NOT_EXISTENTIAL, OPERATION_RESULT_NOT_VARIABLE,
    OPERATION_UNDEFINED_EXISTENTIAL, validate_io_wellformedness,
};

fn failure(source: &str) -> maledictus::python_io_wellformedness::IoWellformednessFailure {
    validate_io_wellformedness(source, "program.py")
        .expect_err("invalid IO existential definition flow unexpectedly passed")
}

#[test]
fn direct_result_and_operation_output_definitions_are_source_typed() {
    for source in [
        concat!(
            "from nagini_contracts.contracts import ContractOnly, Ensures, Result\n",
            "from nagini_contracts.io_contracts import IOExists1\n",
            "@ContractOnly\n",
            "def run() -> int:\n",
            "    IOExists1(int)(lambda value: (\n",
            "        Ensures(value == Result() and value == 1),\n",
            "    ))\n",
        ),
        concat!(
            "from nagini_contracts.contracts import Result\n",
            "from nagini_contracts.io_contracts import *\n",
            "@IOOperation\n",
            "def leaf(start: Place, value: int = Result()) -> bool:\n",
            "    Terminates(True)\n",
            "@IOOperation\n",
            "def compose(start: Place) -> bool:\n",
            "    Terminates(True)\n",
            "    return IOExists1(int)(lambda value: leaf(start, value))\n",
        ),
    ] {
        validate_io_wellformedness(source, "program.py")
            .unwrap_or_else(|diagnostic| panic!("{diagnostic:#?}"));
    }
}

#[test]
fn reversed_conditional_and_prior_uses_do_not_define_an_existential() {
    for source in [
        concat!(
            "from nagini_contracts.contracts import Ensures, Result\n",
            "from nagini_contracts.io_contracts import *\n",
            "def run() -> Place:\n",
            "    IOExists1(Place)(lambda value: (\n",
            "        Ensures(Result() == value),\n",
            "    ))\n",
        ),
        concat!(
            "from nagini_contracts.contracts import Ensures, Implies, Result\n",
            "from nagini_contracts.io_contracts import *\n",
            "def run(flag: bool) -> Place:\n",
            "    IOExists1(Place)(lambda value: (\n",
            "        Ensures(Implies(flag, value == Result())),\n",
            "    ))\n",
        ),
        concat!(
            "from nagini_contracts.contracts import Ensures, Result\n",
            "from nagini_contracts.io_contracts import *\n",
            "def run() -> Place:\n",
            "    IOExists1(Place)(lambda value: (\n",
            "        Ensures(token(value) and value == Result()),\n",
            "    ))\n",
        ),
    ] {
        let diagnostic = failure(source);
        assert_eq!(diagnostic.code, EXISTENTIAL_USE_UNDEFINED, "{source}");
        assert!(diagnostic.line > 0);
        assert!(diagnostic.column > 0);
    }
}

#[test]
fn aliases_preserve_exact_result_types_and_lexical_shadowing_remains_ordinary_python() {
    let mismatch = concat!(
        "from nagini_contracts.contracts import ContractOnly, Ensures, Result as R\n",
        "from nagini_contracts.io_contracts import IOExists1 as Exists\n",
        "@ContractOnly\n",
        "def run() -> int:\n",
        "    Exists(bool)(lambda value: (\n",
        "        Ensures(value == R()),\n",
        "    ))\n",
    );
    assert_eq!(failure(mismatch).code, EXISTENTIAL_DEFINITION_TYPE_MISMATCH);

    let shadowed = concat!(
        "from nagini_contracts.io_contracts import *\n",
        "def run(IOExists1: object) -> None:\n",
        "    IOExists1(int)(lambda value: value)\n",
    );
    validate_io_wellformedness(shadowed, "program.py")
        .unwrap_or_else(|diagnostic| panic!("{diagnostic:#?}"));
}

#[test]
fn operation_result_positions_distinguish_all_three_invalid_shapes() {
    let prefix = concat!(
        "from nagini_contracts.contracts import Result\n",
        "from nagini_contracts.io_contracts import *\n",
        "@IOOperation\n",
        "def leaf(start: Place, value: int = Result()) -> bool:\n",
        "    Terminates(True)\n",
    );
    let literal = format!(
        "{prefix}@IOOperation\ndef compose(start: Place) -> bool:\n    Terminates(True)\n    return leaf(start, 2)\n"
    );
    assert_eq!(failure(&literal).code, OPERATION_RESULT_NOT_VARIABLE);

    let ordinary = format!(
        "{prefix}@IOOperation\ndef compose(start: Place, value: int) -> bool:\n    Terminates(True)\n    return leaf(start, value)\n"
    );
    assert_eq!(failure(&ordinary).code, OPERATION_RESULT_NOT_EXISTENTIAL);

    let undefined = format!(
        "{prefix}@IOOperation\ndef compose(start: Place, flag: bool) -> bool:\n    Terminates(True)\n    return IOExists1(int)(lambda value: Implies(flag, value == 2))\n"
    );
    assert_eq!(failure(&undefined).code, OPERATION_UNDEFINED_EXISTENTIAL);
}

#[test]
fn enclosing_operation_outputs_are_typed_result_endpoints_for_nested_relations() {
    let prefix = concat!(
        "from nagini_contracts.contracts import Result\n",
        "from nagini_contracts.io_contracts import *\n",
        "@IOOperation\n",
        "def leaf(start: Place, value: int = Result()) -> bool:\n",
        "    Terminates(True)\n",
    );
    let passthrough = format!(
        "{prefix}@IOOperation\ndef compose(start: Place, value: int = Result()) -> bool:\n    Terminates(True)\n    return leaf(start, value)\n"
    );
    validate_io_wellformedness(&passthrough, "program.py")
        .unwrap_or_else(|diagnostic| panic!("{diagnostic:#?}"));

    let mismatched = format!(
        "{prefix}@IOOperation\ndef compose(start: Place, value: bool = Result()) -> bool:\n    Terminates(True)\n    return leaf(start, value)\n"
    );
    assert_eq!(
        failure(&mismatched).code,
        EXISTENTIAL_DEFINITION_TYPE_MISMATCH
    );
}

#[test]
fn imported_relations_defer_unknown_result_positions_but_shadowed_names_do_not() {
    let imported = concat!(
        "from provider import leaf\n",
        "from nagini_contracts.io_contracts import *\n",
        "@IOOperation\n",
        "def compose(start: Place) -> bool:\n",
        "    Terminates(True)\n",
        "    return IOExists1(int)(lambda value: leaf(start, value))\n",
    );
    validate_io_wellformedness(imported, "program.py")
        .unwrap_or_else(|diagnostic| panic!("{diagnostic:#?}"));

    let shadowed = concat!(
        "from provider import leaf\n",
        "from nagini_contracts.io_contracts import *\n",
        "leaf = object\n",
        "@IOOperation\n",
        "def compose(start: Place) -> bool:\n",
        "    Terminates(True)\n",
        "    return IOExists1(int)(lambda value: leaf(start, value))\n",
    );
    assert_eq!(failure(shadowed).code, OPERATION_UNDEFINED_EXISTENTIAL);
}

#[test]
fn conditional_operation_results_are_defined_only_on_their_branch() {
    let prefix = concat!(
        "from nagini_contracts.contracts import Result\n",
        "from nagini_contracts.io_contracts import *\n",
        "@IOOperation\n",
        "def leaf(start: Place, value: int = Result()) -> bool:\n",
        "    Terminates(True)\n",
    );
    let branch_local = format!(
        "{prefix}@IOOperation\ndef compose(start: Place, flag: bool) -> bool:\n    Terminates(True)\n    return IOExists1(int)(lambda value: (leaf(start, value) and value == 1) if flag else True)\n"
    );
    validate_io_wellformedness(&branch_local, "program.py")
        .unwrap_or_else(|diagnostic| panic!("{diagnostic:#?}"));

    let escaped = format!(
        "{prefix}@IOOperation\ndef compose(start: Place, flag: bool) -> bool:\n    Terminates(True)\n    return IOExists1(int)(lambda value: ((leaf(start, value) if flag else True) and value == 1))\n"
    );
    assert_eq!(failure(&escaped).code, OPERATION_UNDEFINED_EXISTENTIAL);
}

#[test]
fn all_fifteen_pinned_io_existential_definition_fixtures_match_every_frontend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/io/translation/test_basic_io_21.py",
        "tests/io/translation/test_defining_variable_types_1.py",
        "tests/io/translation/test_defining_variable_types_2.py",
        "tests/io/translation/test_defining_variable_types_3.py",
        "tests/io/translation/test_defining_variable_types_4.py",
        "tests/io/translation/test_defining_variable_types_7.py",
        "tests/io/translation/test_defining_variables_1.py",
        "tests/io/translation/test_defining_variables_2.py",
        "tests/io/translation/test_defining_variables_3.py",
        "tests/io/translation/test_defining_variables_4.py",
        "tests/io/translation/test_defining_variables_5.py",
        "tests/io/translation/test_defining_variables_6.py",
        "tests/io/translation/test_defining_variables_7.py",
        "tests/io/translation/test_defining_variables_8.py",
        "tests/io/translation/test_defining_variables_9.py",
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
        assert_eq!(
            heap.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection,
            "heap {fixture}: {heap:#?}"
        );

        let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(reference.passed, "reference {fixture}: {reference:#?}");
        assert_eq!(reference.expected, reference.actual, "{reference:#?}");
    }
}
