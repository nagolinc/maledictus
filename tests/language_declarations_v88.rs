use std::{fs, path::Path};

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::{
    analyze_python_frontend,
    protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile},
};

const FLOAT_CONVERSION_UNSUPPORTED: &str =
    "unsupported:float() is currently only supported with arguments NaN and inf.";
const MULTIPLE_INHERITANCE_UNSUPPORTED: &str = "unsupported:multiple inheritance";
const METACLASS_UNSUPPORTED: &str = "unsupported:Unsupported metaclass";
const LARGE_TUPLE_UNSUPPORTED: &str = "unsupported:Tuples longer than 9 elements are currently unsupported. Please file an issue to resolve this.";
const ILLEGAL_MAGIC_METHOD: &str = "invalid.program:illegal.magic.method";
const WILDCARD_VARIABLE_READ: &str = "invalid.program:wildcard.variable.read";

fn analyze(source: &str) -> maledictus::FrontendAnalysis {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("program.py"), source).unwrap();
    analyze_python_frontend(&ProofRequest {
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

#[test]
fn declaration_and_expression_restrictions_are_structural_and_located() {
    let cases = [
        (
            "class A:\n    pass\nclass B:\n    pass\nclass C(A, B):\n    pass\n",
            MULTIPLE_INHERITANCE_UNSUPPORTED,
            5,
        ),
        (
            "class Meta:\n    pass\nclass C(metaclass=Meta):\n    pass\n",
            METACLASS_UNSUPPORTED,
            3,
        ),
        (
            "def run() -> None:\n    value = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)\n",
            LARGE_TUPLE_UNSUPPORTED,
            2,
        ),
        (
            "class C:\n    def __getattr__(self, name: str) -> object:\n        return None\n",
            ILLEGAL_MAGIC_METHOD,
            2,
        ),
        (
            "def run() -> int:\n    _ = 1\n    return _\n",
            WILDCARD_VARIABLE_READ,
            3,
        ),
        (
            "def run(value: int) -> float:\n    return float(value)\n",
            FLOAT_CONVERSION_UNSUPPORTED,
            2,
        ),
    ];

    for (source, code, line) in cases {
        let analysis = analyze(source);
        let diagnostic = analysis
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code == code)
            .unwrap_or_else(|| panic!("{source}\n{analysis:#?}"));
        assert_eq!(diagnostic.line, Some(line), "{source}");
        assert!(
            diagnostic.column.is_some_and(|column| column > 0),
            "{source}"
        );
    }
}

#[test]
fn neighboring_supported_shapes_and_shadowed_float_are_not_reclassified() {
    let sources = [
        "from typing import Generic, Sized, TypeVar\nT = TypeVar('T')\nclass Base:\n    pass\nclass C(Generic[T], Base, Sized):\n    pass\n",
        "from abc import ABCMeta\nclass C(metaclass=ABCMeta):\n    pass\n",
        "def run() -> tuple[int, int, int, int, int, int, int, int, int]:\n    return (0, 1, 2, 3, 4, 5, 6, 7, 8)\n",
        "class C:\n    def __init__(self) -> None:\n        pass\n    def __eq__(self, other: object) -> bool:\n        return False\n",
        "def run() -> int:\n    _ = 1\n    return 0\n",
        "def run(float: object) -> object:\n    return float(1)\n",
        "def float(value: int) -> int:\n    return value\ndef run() -> int:\n    return float(1)\n",
        "def run() -> float:\n    return float('1.25e-3')\n",
    ];

    for source in sources {
        let analysis = analyze(source);
        assert!(
            analysis.diagnostics.iter().all(|diagnostic| !matches!(
                diagnostic.code.as_str(),
                FLOAT_CONVERSION_UNSUPPORTED
                    | ILLEGAL_MAGIC_METHOD
                    | LARGE_TUPLE_UNSUPPORTED
                    | METACLASS_UNSUPPORTED
                    | MULTIPLE_INHERITANCE_UNSUPPORTED
                    | WILDCARD_VARIABLE_READ
            )),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn shadowed_typing_and_abc_names_do_not_bypass_class_validation() {
    let shadowed_generic = analyze(
        "from typing import Generic\nclass Base:\n    pass\nclass Generic:\n    pass\nclass C(Generic[int], Base):\n    pass\n",
    );
    assert!(
        shadowed_generic
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == MULTIPLE_INHERITANCE_UNSUPPORTED),
        "{shadowed_generic:#?}"
    );

    let shadowed_meta = analyze(
        "from abc import ABCMeta\nclass ABCMeta:\n    pass\nclass C(metaclass=ABCMeta):\n    pass\n",
    );
    assert!(
        shadowed_meta
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == METACLASS_UNSUPPORTED),
        "{shadowed_meta:#?}"
    );
}

#[test]
fn restrictions_are_found_inside_nested_runtime_expressions() {
    let tuple = analyze(
        "def run(flag: bool) -> object:\n    return (0, (1, 2, 3, 4, 5, 6, 7, 8, 9, 10)) if flag else None\n",
    );
    let diagnostic = tuple
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code == LARGE_TUPLE_UNSUPPORTED)
        .unwrap_or_else(|| panic!("{tuple:#?}"));
    assert_eq!(diagnostic.line, Some(2));

    let wildcard = analyze("def run() -> int:\n    return 1 + _\n");
    let diagnostic = wildcard
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code == WILDCARD_VARIABLE_READ)
        .unwrap_or_else(|| panic!("{wildcard:#?}"));
    assert_eq!(diagnostic.line, Some(2));
}

#[test]
fn all_six_pinned_restriction_fixtures_match_every_frontend_exactly() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_multiple_inheritance.py",
        "tests/functional/translation/test_metaclass.py",
        "tests/functional/translation/test_large_tuple.py",
        "tests/functional/translation/test_magic_method_1.py",
        "tests/functional/translation/test_underscore_1.py",
        "tests/functional/translation/test_float_conversion.py",
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
    }
}
