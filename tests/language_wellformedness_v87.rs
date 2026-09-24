use std::{fs, path::Path};

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_language_wellformedness::{
    CONTINUE_IN_FINALLY, MAPPING_PATTERN_UNSUPPORTED, MULTI_ITEM_WITH_UNSUPPORTED,
    MULTIPLE_DICT_GENERATORS, MULTIPLE_LIST_GENERATORS, MULTIPLE_SET_GENERATORS,
    PARAMETERIZED_CLASS_PATTERN_UNSUPPORTED, POSITIONAL_CLASS_PATTERN_UNSUPPORTED,
    SLICE_ASSIGNMENT_UNSUPPORTED, validate_language_wellformedness,
};
use maledictus::{
    FrontendDisposition,
    protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile},
};

fn failure(
    source: &str,
) -> maledictus::python_language_wellformedness::LanguageWellformednessFailure {
    validate_language_wellformedness(source, "program.py")
        .expect_err("prohibited Python source unexpectedly passed well-formedness validation")
}

#[test]
fn each_restriction_is_derived_from_its_ast_shape_and_located() {
    let cases = [
        (
            "def run() -> None:\n    while True:\n        try:\n            pass\n        finally:\n            continue\n",
            CONTINUE_IN_FINALLY,
            6,
        ),
        (
            "def run(xs: list[int]) -> list[int]:\n    return [x + y for x in xs for y in xs]\n",
            MULTIPLE_LIST_GENERATORS,
            2,
        ),
        (
            "def run(xs: list[int]) -> dict[int, int]:\n    return {x: y for x in xs for y in xs}\n",
            MULTIPLE_DICT_GENERATORS,
            2,
        ),
        (
            "def run(xs: list[int]) -> set[int]:\n    return {x + y for x in xs for y in xs}\n",
            MULTIPLE_SET_GENERATORS,
            2,
        ),
        (
            "def run(value: object) -> int:\n    match value:\n        case {'key': item}:\n            return item\n        case _:\n            return 0\n",
            MAPPING_PATTERN_UNSUPPORTED,
            3,
        ),
        (
            "class Point:\n    __match_args__ = ('x',)\ndef run(value: Point) -> int:\n    match value:\n        case Point(item):\n            return item\n        case _:\n            return 0\n",
            POSITIONAL_CLASS_PATTERN_UNSUPPORTED,
            5,
        ),
        (
            "class Point:\n    pass\ndef run(value: Point) -> int:\n    match value:\n        case Point(x=item):\n            return item\n        case _:\n            return 0\n",
            PARAMETERIZED_CLASS_PATTERN_UNSUPPORTED,
            5,
        ),
        (
            "def run(values: list[int]) -> None:\n    values[1:3] = [2, 3]\n",
            SLICE_ASSIGNMENT_UNSUPPORTED,
            2,
        ),
        (
            "def run(first: object, second: object) -> None:\n    with first, second:\n        pass\n",
            MULTI_ITEM_WITH_UNSUPPORTED,
            2,
        ),
    ];

    for (source, code, line) in cases {
        let diagnostic = failure(source);
        assert_eq!(diagnostic.code, code, "{source}");
        assert_eq!(diagnostic.line, line, "{source}");
        assert!(diagnostic.column > 0, "{source}");
    }
}

#[test]
fn valid_neighboring_constructs_are_not_reclassified() {
    let sources = [
        // The continue is in the try body, not in the finally body.
        "def run() -> None:\n    while True:\n        try:\n            continue\n        finally:\n            pass\n",
        // A nested function has its own control-flow context.
        "def run() -> None:\n    try:\n        pass\n    finally:\n        def nested() -> None:\n            while True:\n                continue\n",
        // Multiple filters still belong to one generator.
        "def run(xs: list[int]) -> list[int]:\n    return [x for x in xs if x > 0 if x < 4]\n",
        "class Point:\n    pass\ndef run(value: Point) -> int:\n    match value:\n        case Point():\n            return 1\n        case _:\n            return 0\n",
        "def run(values: list[int]) -> list[int]:\n    values[0] = 1\n    head = values[1:3]\n    return head\n",
        "def run(values: list[int]) -> list[int]:\n    return values[::-1]\n",
        "def run(first: object, second: object) -> None:\n    with first:\n        with second:\n            pass\n",
    ];

    for source in sources {
        validate_language_wellformedness(source, "program.py")
            .unwrap_or_else(|diagnostic| panic!("{source}\n{diagnostic:#?}"));
    }
}

#[test]
fn stepped_slice_assignment_is_still_an_unsupported_mutation() {
    let source = "def run(values: list[int]) -> None:\n    values[::2] = [1]\n";
    let diagnostic = failure(source);
    assert_eq!(diagnostic.code, SLICE_ASSIGNMENT_UNSUPPORTED);
}

#[test]
fn first_prohibited_construct_in_source_order_wins() {
    let source = concat!(
        "def run(values: list[int], first: object, second: object) -> list[int]:\n",
        "    values[1:3] = [1]\n",
        "    with first, second:\n",
        "        pass\n",
        "    return stepped\n",
    );
    let diagnostic = failure(source);
    assert_eq!(diagnostic.code, SLICE_ASSIGNMENT_UNSUPPORTED);
    assert_eq!(diagnostic.line, 2);
}

#[test]
fn production_frontend_runs_the_source_general_preflight() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("program.py"),
        "def run(xs: list[int]) -> set[int]:\n    return {x + y for x in xs for y in xs}\n",
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
        .find(|diagnostic| diagnostic.code == MULTIPLE_SET_GENERATORS)
        .unwrap_or_else(|| panic!("missing source-language diagnostic: {analysis:#?}"));
    assert_eq!(diagnostic.line, Some(2));
}

#[test]
fn all_ten_actual_language_restriction_fixtures_match_every_frontend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_continue.py",
        "tests/functional/translation/test_listcomp_multiple_generators.py",
        "tests/functional/translation/test_listcomp_multi_generator.py",
        "tests/functional/translation/test_dictcomp_multiple_generators.py",
        "tests/functional/translation/test_setcomp_multiple_generators.py",
        "tests/functional/translation/test_match_mapping.py",
        "tests/functional/translation/test_match_positional.py",
        "tests/functional/translation/test_match_pure_class_keyword_capture.py",
        "tests/functional/translation/test_slice_assign.py",
        "tests/functional/translation/test_with_multi.py",
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

#[test]
fn symbolic_stepped_slice_is_a_heap_semantic_supersession() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/functional/translation/test_slice_step.py";

    assert!(
        check_pinned_scalar_fixture(&suite, &pin, fixture).is_err(),
        "the scalar backend must not reproduce Nagini's unsupported result as a proof"
    );
    let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
        .expect("the heap backend models symbolic stepped slicing");
    assert!(
        !heap.passed,
        "upstream refusal is not an exact match: {heap:#?}"
    );
    assert!(heap.semantic_verified, "{heap:#?}");
    assert_eq!(
        heap.analysis_kind,
        ConformanceMatchKind::SupersededUpstreamUnsupported,
        "{heap:#?}"
    );
    assert!(
        check_pinned_reference_fixture(&suite, &pin, fixture).is_err(),
        "the nominal-reference backend has no sequence semantics"
    );
}
