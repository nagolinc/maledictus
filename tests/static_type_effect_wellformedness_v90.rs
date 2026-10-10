use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_language_wellformedness::{
    GENERIC_CONSTRUCTOR_WITHOUT_TYPE, IMPURE_LIST_COMPREHENSION_BODY, PARTIAL_TYPE,
    validate_language_wellformedness,
};

fn failure(
    source: &str,
) -> maledictus::python_language_wellformedness::LanguageWellformednessFailure {
    validate_language_wellformedness(source, "program.py")
        .expect_err("ill-formed source unexpectedly passed validation")
}

fn assert_valid(source: &str) {
    validate_language_wellformedness(source, "program.py")
        .unwrap_or_else(|error| panic!("{source}\n{error:#?}"));
}

#[test]
fn unresolved_empty_container_types_are_structural_and_context_sensitive() {
    for (source, line) in [
        ("def run() -> None:\n    values = []\n", 2),
        ("def run() -> None:\n    left, right = {}, 1\n", 2),
    ] {
        let error = failure(source);
        assert_eq!(error.code, PARTIAL_TYPE, "{source}");
        assert_eq!(error.line, line, "{source}");
    }

    for source in [
        "def run() -> None:\n    values: list[int] = []\n",
        "from typing import List\ndef run() -> None:\n    values = []  # type: List[int]\n",
        "def run() -> None:\n    values = [1]\n",
        "def set() -> object:\n    return object()\ndef run() -> None:\n    values = set()\n",
        "def run(target: object) -> None:\n    target.values = []\n",
        "def consume(values: list[int]) -> None:\n    pass\ndef run() -> None:\n    consume([])\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn empty_container_resets_retain_local_annotations_without_leaking_scopes() {
    for source in [
        "def run() -> None:\n    values: list[int] = [1]\n    values = []\n",
        "def run(values: list[int]) -> None:\n    values = []\n",
        "def run() -> None:\n    values: list[int]\n    counts: dict[str, int]\n    values, counts = [], {}\n",
        "async def run(values: list[int]) -> None:\n    values = []\n",
        "def run(flag: bool) -> None:\n    if flag:\n        values: list[int] = [1]\n    values = []\n",
    ] {
        assert_valid(source);
    }
    for source in [
        "values: list[int] = [1]\ndef run() -> None:\n    values = []\n",
        "def first() -> None:\n    values: list[int] = [1]\ndef second() -> None:\n    values = []\n",
        "def outer() -> None:\n    values: list[int] = [1]\n    def inner() -> None:\n        values = []\n",
        "def outer() -> None:\n    def inner() -> None:\n        values: list[int] = [1]\n    values = []\n",
        "class Box:\n    values: list[int] = [1]\n    def run(self) -> None:\n        values = []\n",
        "def run() -> None:\n    values: list[int] = [1]\n    values, missing = [], {}\n",
        "def run() -> None:\n    class Box:\n        values: list[int] = [1]\n    values = []\n",
    ] {
        assert_eq!(failure(source).code, PARTIAL_TYPE, "{source}");
    }
}

#[test]
fn annotated_resets_still_reach_heap_assertion_and_index_obligations() {
    use maledictus::python_heap_contracts::verify_heap_module;
    use maledictus::vc::ObligationStatus;
    let source = "from typing import List\ndef run() -> int:\n    values: List[int] = [1]\n    values = []\n    assert len(values) == 0\n    return 0\n";
    let valid = verify_heap_module(source, "reset.py", &[]).unwrap();
    assert!(valid.passed, "{valid:#?}");
    for bad in [
        source.replace("len(values) == 0", "len(values) == 1"),
        source.replace("return 0", "return values[0]"),
    ] {
        let result = verify_heap_module(&bad, "reset.py", &[]).unwrap();
        assert!(!result.passed, "{result:#?}");
        assert!(
            result
                .obligations
                .iter()
                .any(|o| o.status == ObligationStatus::Refuted),
            "{result:#?}"
        );
    }
    let alias = "from typing import List\ndef run() -> int:\n    values: List[int] = [1]\n    original = values\n    values = []\n    assert len(values) == 0\n    assert len(original) == 1\n    return 0\n";
    let result = verify_heap_module(alias, "alias.py", &[]).unwrap();
    assert!(result.passed, "{result:#?}");
    let result = verify_heap_module(
        &alias.replace("len(original) == 1", "len(original) == 0"),
        "alias.py",
        &[],
    )
    .unwrap();
    assert!(
        !result.passed,
        "reset must not clear the alias: {result:#?}"
    );
}

#[test]
fn dictionary_resets_remain_an_explicitly_unsupported_semantic_context() {
    use maledictus::python_heap_contracts::verify_heap_module;
    let source = "from typing import Dict\ndef run() -> int:\n    values: Dict[str, int] = {'a': 1}\n    values = {}\n    assert len(values) == 0\n    return 0\n";
    let error = verify_heap_module(source, "dictionary.py", &[]).unwrap_err();
    assert_eq!(error.code, "frontend.python.heap.empty-dict-needs-context");
    let missing = source.replace("return 0", "return values['a']");
    let error = verify_heap_module(&missing, "dictionary.py", &[]).unwrap_err();
    assert_eq!(error.code, "frontend.python.heap.empty-dict-needs-context");
}

#[test]
fn generic_construction_uses_resolved_typing_bindings_and_function_scope() {
    let direct = failure(
        "from typing import Generic, TypeVar\nT = TypeVar('T')\nclass Box(Generic[T]):\n    pass\ndef run() -> None:\n    Box(1)\n",
    );
    assert_eq!(direct.code, GENERIC_CONSTRUCTOR_WITHOUT_TYPE);
    assert_eq!(direct.line, 6);

    let aliased = failure(
        "import typing as ty\nT = ty.TypeVar('T')\nclass Box(ty.Generic[T]):\n    pass\ndef run() -> None:\n    Box(1)\n",
    );
    assert_eq!(aliased.code, GENERIC_CONSTRUCTOR_WITHOUT_TYPE);

    for source in [
        "from typing import Generic, TypeVar\nT = TypeVar('T')\nclass Box(Generic[T]):\n    pass\ndef run() -> None:\n    Box[int](1)\n",
        "from typing import Generic, TypeVar\nT = TypeVar('T')\nclass Box(Generic[T]):\n    pass\ndef run() -> None:\n    value = Box(1)  # type: Box[int]\n",
        "from typing import Generic, TypeVar\nT = TypeVar('T')\nclass Box(Generic[T]):\n    pass\ndef run() -> None:\n    value = Box(1)\n",
        "from typing import Generic, TypeVar\nT = TypeVar('T')\nclass Generic:\n    pass\nclass Box(Generic[T]):\n    pass\ndef run() -> None:\n    Box(1)\n",
        "from typing import Generic, TypeVar\nT = TypeVar('T')\nclass Box(Generic[T]):\n    pass\ndef run(Box: object) -> None:\n    Box(1)\n",
        "from typing import Generic, TypeVar\nT = TypeVar('T')\nclass Box(Generic[T]):\n    pass\nBox = object\ndef run() -> None:\n    Box()\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn list_comprehension_effect_check_resolves_purity_and_shadowing() {
    let direct = failure(
        "def transform(value: int) -> int:\n    return value\ndef run(values: list[int]) -> list[int]:\n    return [transform(value) for value in values]\n",
    );
    assert_eq!(direct.code, IMPURE_LIST_COMPREHENSION_BODY);
    assert_eq!(direct.line, 4);

    let shadowed_decorator = failure(
        "from nagini_contracts.contracts import Pure\ndef Pure(value: int) -> int:\n    return value\n@Pure\ndef transform(value: int) -> int:\n    return value\ndef run(values: list[int]) -> list[int]:\n    return [transform(value) for value in values]\n",
    );
    assert_eq!(shadowed_decorator.code, IMPURE_LIST_COMPREHENSION_BODY);

    for source in [
        "from nagini_contracts.contracts import Pure as VerifiedPure\n@VerifiedPure\ndef transform(value: int) -> int:\n    return value\ndef run(values: list[int]) -> list[int]:\n    return [transform(value) for value in values]\n",
        "def transform(value: int) -> int:\n    return value\ndef run(values: list[int], transform: object) -> list[object]:\n    return [transform(value) for value in values]\n",
        "def run(values: list[int]) -> list[int]:\n    return [abs(value) for value in values]\n",
        "def transform(value: int) -> int:\n    return value\ndef run(values: list[int]) -> list[object]:\n    return [(lambda: transform(value)) for value in values]\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn all_three_pinned_rules_match_scalar_heap_and_reference_frontends_exactly() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_partial_type.py",
        "tests/functional/translation/test_generic_class_1.py",
        "tests/functional/translation/test_list_comprehension_1.py",
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
