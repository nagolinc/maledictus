use std::path::PathBuf;

use maledictus::conformance::{
    check_heap_source, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};

#[test]
fn finite_union_narrowing_preserves_each_reachable_runtime_arm() {
    let source = "from typing import Union\nfrom nagini_contracts.contracts import *\nclass Left:\n    pass\nclass Right:\n    pass\ndef inspect(value: Union[Left, Right]) -> None:\n    if isinstance(value, Left):\n        assert isinstance(value, Left)\n    else:\n        assert isinstance(value, Right)\n";
    let result = check_heap_source(source, "union_narrowing.py").unwrap();
    assert!(result.passed, "{result:#?}");
    assert!(result.semantic_verified, "{result:#?}");
}

#[test]
fn false_cast_and_index_preconditions_are_refuted_at_the_real_operation() {
    let source = "from typing import Tuple, cast\nfrom nagini_contracts.contracts import *\nclass Left:\n    pass\nclass Right:\n    pass\ndef inspect_cast(value: Left) -> None:\n    #:: ExpectedOutput(application.precondition:assertion.false)\n    wrong = cast(Right, value)\ndef inspect_index(pair: Tuple[int, int]) -> None:\n    #:: ExpectedOutput(application.precondition:assertion.false)\n    item = pair[3]\n";
    let result = check_heap_source(source, "type_preconditions.py").unwrap();
    assert!(result.passed, "{result:#?}");
    assert!(!result.semantic_verified, "{result:#?}");
    assert_eq!(result.expected, result.actual, "{result:#?}");
}

#[test]
fn dynamic_cast_targets_fail_closed_instead_of_becoming_trusted_assertions() {
    let source = "from typing import cast\nclass Item:\n    pass\ndef inspect(value: object, target: object) -> object:\n    return cast(target, value)\n";
    let error = check_heap_source(source, "dynamic_cast.py").unwrap_err();
    assert!(
        error.starts_with("frontend.python.type-algebra.cast-target-unsupported:"),
        "{error}"
    );
}

#[test]
fn recognized_type_algebra_with_unsupported_declarations_fails_closed() {
    let source = "from typing import Union\nclass Left:\n    pass\nclass Right:\n    pass\nclass Both(Left, Right):\n    pass\ndef inspect(value: Union[Left, Right]) -> None:\n    pass\n";
    let error = check_heap_source(source, "unsupported_type_catalog.py").unwrap_err();
    assert!(
        error.starts_with("frontend.python.type-algebra.catalog-unsupported:"),
        "{error}"
    );
}

#[test]
fn recognized_type_algebra_with_unsupported_function_logic_fails_closed() {
    let source = "from typing import Union\nclass Left:\n    pass\nclass Right:\n    pass\ndef inspect(value: Union[Left, Right]) -> None:\n    try:\n        assert isinstance(value, Left)\n    except AssertionError:\n        pass\n";
    let error = check_heap_source(source, "unsupported_type_function.py").unwrap_err();
    assert!(
        error.starts_with("frontend.python.type-algebra.function-unsupported:"),
        "{error}"
    );
}

#[test]
fn five_pinned_type_algebra_fixtures_match_exactly_through_the_public_classifier() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/verification/issues/00118.py",
        "tests/functional/verification/test_cast.py",
        "tests/functional/verification/test_conversion.py",
        "tests/functional/verification/test_tuples.py",
        "tests/functional/verification/test_union_types.py",
    ] {
        let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("public heap classifier refused {fixture}: {error}"));
        assert!(heap.passed, "{fixture}: {heap:#?}");
        assert_eq!(heap.expected, heap.actual, "{fixture}: {heap:#?}");

        assert!(
            check_pinned_scalar_fixture(&suite, &pin, fixture).is_err(),
            "scalar backend must not claim heap type algebra for {fixture}"
        );
        assert!(
            check_pinned_reference_fixture(&suite, &pin, fixture).is_err(),
            "reference backend must not claim finite type algebra for {fixture}"
        );
    }
}
