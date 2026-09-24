use std::{fs, path::Path};

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_io_wellformedness::{MISPLACED_IO_EXISTS, validate_io_wellformedness};
use maledictus::{
    FrontendDisposition,
    protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile},
};

fn failure(source: &str) -> maledictus::python_io_wellformedness::IoWellformednessFailure {
    validate_io_wellformedness(source, "program.py")
        .expect_err("nested IOExists declaration unexpectedly passed well-formedness validation")
}

#[test]
fn nested_io_exists_is_rejected_for_star_and_aliased_imports() {
    let star_import = concat!(
        "from nagini_contracts.io_contracts import *\n",
        "def run() -> None:\n",
        "    IOExists1(Place)(lambda outer: (\n",
        "        IOExists1(int)(lambda inner: inner == 1)\n",
        "    ))\n",
    );
    let diagnostic = failure(star_import);
    assert_eq!(diagnostic.code, MISPLACED_IO_EXISTS);
    assert_eq!(diagnostic.line, 4);
    assert!(diagnostic.column > 0);

    let aliased_import = concat!(
        "from nagini_contracts.io_contracts import IOExists2 as Exists, Place\n",
        "def run() -> None:\n",
        "    Exists(Place, int)(lambda outer, value: (\n",
        "        Exists(int, int)(lambda left, right: left == right)\n",
        "    ))\n",
    );
    let diagnostic = failure(aliased_import);
    assert_eq!(diagnostic.code, MISPLACED_IO_EXISTS);
    assert_eq!(diagnostic.line, 4);
}

#[test]
fn sibling_declarations_and_nested_ordinary_calls_remain_well_formed() {
    for source in [
        concat!(
            "from nagini_contracts.io_contracts import *\n",
            "def run() -> None:\n",
            "    IOExists1(Place)(lambda first: first == first)\n",
            "    IOExists1(Place)(lambda second: second == second)\n",
        ),
        concat!(
            "from nagini_contracts.io_contracts import *\n",
            "def identity(value: int) -> int:\n",
            "    return value\n",
            "def run() -> None:\n",
            "    IOExists1(int)(lambda value: identity(value) == value)\n",
        ),
        concat!(
            "from nagini_contracts.io_contracts import *\n",
            "def run() -> None:\n",
            "    while True:\n",
            "        IOExists1(int)(lambda value: value == value)\n",
            "        break\n",
        ),
    ] {
        validate_io_wellformedness(source, "program.py")
            .unwrap_or_else(|diagnostic| panic!("{source}\n{diagnostic:#?}"));
    }
}

#[test]
fn io_operation_may_return_one_direct_io_exists_declaration() {
    for source in [
        concat!(
            "from nagini_contracts.contracts import Result\n",
            "from nagini_contracts.io_contracts import IOExists1, IOOperation, Place\n",
            "@IOOperation\n",
            "def operation(start: Place, end: Place = Result()) -> bool:\n",
            "    return IOExists1(Place)(lambda middle: middle == end)\n",
        ),
        concat!(
            "from nagini_contracts.contracts import Result\n",
            "from nagini_contracts.io_contracts import *\n",
            "@IOOperation\n",
            "def operation(start: Place, end: Place = Result()) -> bool:\n",
            "    Terminates(True)\n",
            "    return IOExists1(Place)(lambda middle: middle == end)\n",
        ),
    ] {
        validate_io_wellformedness(source, "program.py")
            .unwrap_or_else(|diagnostic| panic!("{source}\n{diagnostic:#?}"));
    }
}

#[test]
fn io_operation_return_does_not_waive_nested_or_indirect_io_exists() {
    for source in [
        concat!(
            "from nagini_contracts.contracts import Result\n",
            "from nagini_contracts.io_contracts import *\n",
            "@IOOperation\n",
            "def operation(start: Place, end: Place = Result()) -> bool:\n",
            "    return IOExists1(Place)(lambda outer: (\n",
            "        IOExists1(int)(lambda inner: inner == 1)\n",
            "    ))\n",
        ),
        concat!(
            "from nagini_contracts.contracts import Result\n",
            "from nagini_contracts.io_contracts import *\n",
            "def identity(value: bool) -> bool:\n",
            "    return value\n",
            "@IOOperation\n",
            "def operation(start: Place, end: Place = Result()) -> bool:\n",
            "    return identity(IOExists1(Place)(lambda middle: middle == end))\n",
        ),
        concat!(
            "from nagini_contracts.contracts import Result\n",
            "from nagini_contracts.io_contracts import *\n",
            "@IOOperation\n",
            "def operation(start: Place, flag: bool, end: Place = Result()) -> bool:\n",
            "    if flag:\n",
            "        return IOExists1(Place)(lambda middle: middle == end)\n",
            "    return True\n",
        ),
    ] {
        let diagnostic = failure(source);
        assert_eq!(diagnostic.code, MISPLACED_IO_EXISTS, "{source}");
    }
}

#[test]
fn io_exists_is_rejected_outside_a_direct_function_or_loop_body_statement() {
    for source in [
        concat!(
            "from nagini_contracts.io_contracts import *\n",
            "def run() -> object:\n",
            "    return IOExists1(int)(lambda value: value == value)\n",
        ),
        concat!(
            "from nagini_contracts.io_contracts import *\n",
            "def run(flag: bool) -> None:\n",
            "    if flag:\n",
            "        IOExists1(int)(lambda value: value == value)\n",
        ),
    ] {
        let diagnostic = failure(source);
        assert_eq!(diagnostic.code, MISPLACED_IO_EXISTS, "{source}");
    }
}

#[test]
fn lexical_shadowing_cannot_be_mistaken_for_the_contract_primitive() {
    let parameter_shadow = concat!(
        "from nagini_contracts.io_contracts import *\n",
        "def run(IOExists1: object) -> None:\n",
        "    IOExists1(object)(lambda outer: (\n",
        "        IOExists1(object)(lambda inner: inner)\n",
        "    ))\n",
    );
    validate_io_wellformedness(parameter_shadow, "program.py")
        .unwrap_or_else(|diagnostic| panic!("{parameter_shadow}\n{diagnostic:#?}"));

    let local_shadow = concat!(
        "from nagini_contracts.io_contracts import *\n",
        "def run(factory: object) -> None:\n",
        "    IOExists1 = factory\n",
        "    IOExists1(object)(lambda outer: IOExists1(object)(lambda inner: inner))\n",
    );
    validate_io_wellformedness(local_shadow, "program.py")
        .unwrap_or_else(|diagnostic| panic!("{local_shadow}\n{diagnostic:#?}"));

    let nonexistent_export = concat!(
        "from nagini_contracts.io_contracts import *\n",
        "def run() -> None:\n",
        "    IOExists16(object)(lambda outer: (\n",
        "        IOExists16(object)(lambda inner: inner)\n",
        "    ))\n",
    );
    validate_io_wellformedness(nonexistent_export, "program.py")
        .unwrap_or_else(|diagnostic| panic!("{nonexistent_export}\n{diagnostic:#?}"));
}

#[test]
fn production_frontend_reports_the_source_bound_io_failure() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("program.py"),
        concat!(
            "from nagini_contracts.io_contracts import *\n",
            "def run() -> None:\n",
            "    IOExists1(Place)(lambda outer: (\n",
            "        IOExists1(int)(lambda inner: inner == 1)\n",
            "    ))\n",
        ),
    )
    .unwrap();
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

    assert_eq!(analysis.disposition, FrontendDisposition::Unsupported);
    let diagnostic = analysis
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code == MISPLACED_IO_EXISTS)
        .unwrap_or_else(|| panic!("missing nested IOExists diagnostic: {analysis:#?}"));
    assert_eq!(diagnostic.line, Some(4));
}

#[test]
fn both_exact_nested_io_exists_fixtures_match_every_frontend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/io/translation/test_io_exists_1.py",
        "tests/io/translation/test_io_exists_2.py",
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

#[test]
fn exact_io_builtins_fixture_reaches_the_heap_io_backend_without_a_false_io_rejection() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/io/verification/test_builtins.py";

    for (lane, expected_boundary, checked) in [
        (
            "scalar",
            "frontend.python.contracts.module-statement-unsupported",
            check_pinned_scalar_fixture(&suite, &pin, fixture).map(|result| {
                (
                    result.passed,
                    result.expected == result.actual,
                    format!("{result:#?}"),
                )
            }),
        ),
        (
            "reference",
            "frontend.python.references.io-semantics-unsupported",
            check_pinned_reference_fixture(&suite, &pin, fixture).map(|result| {
                (
                    result.passed,
                    result.expected == result.actual,
                    format!("{result:#?}"),
                )
            }),
        ),
    ] {
        match checked {
            Ok((passed, exact, detail)) => {
                assert!(passed, "{lane}: {detail}");
                assert!(exact, "{lane}: {detail}");
            }
            Err(error) => {
                assert!(!error.contains(MISPLACED_IO_EXISTS), "{lane}: {error}");
                assert!(error.contains(expected_boundary), "{lane}: {error}");
            }
        }
    }

    let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("heap IO backend refused {fixture}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert!(heap.semantic_verified, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual, "{heap:#?}");
}
