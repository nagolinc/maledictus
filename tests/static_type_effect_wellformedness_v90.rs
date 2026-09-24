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
