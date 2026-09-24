use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_language_wellformedness::{
    INVALID_PREVIOUS, validate_language_wellformedness,
};

#[test]
fn canonical_previous_rejects_a_non_iteration_target_in_every_backend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/functional/translation/test_iterators_1.py";
    let source = std::fs::read_to_string(suite.join(fixture)).expect("fixture source");
    let source_failure = validate_language_wellformedness(&source, fixture)
        .expect_err("the exact source should violate Previous well-formedness");
    assert_eq!(source_failure.code, INVALID_PREVIOUS);

    let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("scalar {fixture}: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(
        scalar.analysis_kind,
        ConformanceMatchKind::SourceWellformednessRejection
    );

    let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("heap {fixture}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(
        heap.analysis_kind,
        ConformanceMatchKind::SourceWellformednessRejection
    );

    let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
    assert!(reference.passed, "{reference:#?}");
    assert_eq!(reference.expected, reference.actual);
}

#[test]
fn previous_accepts_an_enclosing_for_target_and_rejects_other_names() {
    let source = r#"from nagini_contracts.contracts import Invariant, Previous

def accepted(values: list[int]) -> None:
    for value in values:
        Invariant(Previous(value) == value)
"#;
    validate_language_wellformedness(source, "accepted.py")
        .expect("an enclosing iteration target is the canonical Previous operand");

    let wrong_target = source.replace("Previous(value)", "Previous(values)");
    let failure = validate_language_wellformedness(&wrong_target, "wrong.py")
        .expect_err("a non-target operand must be rejected");
    assert_eq!(failure.code, INVALID_PREVIOUS);
}

#[test]
fn previous_is_rejected_without_a_matching_enclosing_for_loop() {
    for source in [
        r#"from nagini_contracts.contracts import Previous

def outside(value: int) -> int:
    return Previous(value)
"#,
        r#"from nagini_contracts.contracts import Invariant, Previous

def while_loop(value: int) -> None:
    while value > 0:
        Invariant(Previous(value) == value)
        value -= 1
"#,
    ] {
        let failure = validate_language_wellformedness(source, "invalid_previous.py")
            .expect_err("Previous has no valid loop-invariant target in this context");
        assert_eq!(failure.code, INVALID_PREVIOUS);
    }
}

#[test]
fn aliases_and_qualified_contract_calls_preserve_previous_semantics() {
    let alias_source = r#"from nagini_contracts.contracts import Invariant as loop_invariant
from nagini_contracts.contracts import Previous as history

def alias(values: list[int]) -> None:
    for value in values:
        loop_invariant(history(values) == values)
"#;
    let alias_failure = validate_language_wellformedness(alias_source, "alias.py")
        .expect_err("canonical imported aliases retain Previous semantics");
    assert_eq!(alias_failure.code, INVALID_PREVIOUS);

    let qualified_source = r#"import nagini_contracts.contracts as contracts

def qualified(values: list[int]) -> None:
    for value in values:
        contracts.Invariant(contracts.Previous(values) == values)
"#;
    let qualified_failure = validate_language_wellformedness(qualified_source, "qualified.py")
        .expect_err("a qualified canonical call retains Previous semantics");
    assert_eq!(qualified_failure.code, INVALID_PREVIOUS);
}

#[test]
fn nested_loops_retain_outer_iteration_targets() {
    let valid = r#"from nagini_contracts.contracts import Invariant, Previous

def nested(rows: list[list[int]]) -> None:
    for row in rows:
        for value in row:
            Invariant(Previous(row) == row)
"#;
    validate_language_wellformedness(valid, "nested.py")
        .expect("an outer target remains associated with its enclosing loop");

    let invalid = valid.replace("Previous(row)", "Previous(rows)");
    let failure = validate_language_wellformedness(&invalid, "nested_invalid.py")
        .expect_err("a name that is not any enclosing target must be rejected");
    assert_eq!(failure.code, INVALID_PREVIOUS);
}

#[test]
fn tuple_loop_targets_match_naginis_first_element_rule() {
    let first = r#"from nagini_contracts.contracts import Invariant, Previous

def tuple_loop(values: list[tuple[int, int]]) -> None:
    for first, second in values:
        Invariant(len(Previous(first)) >= 0)
"#;
    validate_language_wellformedness(first, "tuple_first.py")
        .expect("Nagini associates Previous with the first tuple target");

    let second = first.replace("Previous(first)", "Previous(second)");
    let failure = validate_language_wellformedness(&second, "tuple_second.py")
        .expect_err("the second tuple element is not Nagini's iteration-history target");
    assert_eq!(failure.code, INVALID_PREVIOUS);
}

#[test]
fn source_owned_shadowing_is_not_misclassified_as_the_contract_builtin() {
    let source = r#"def Previous(value: int) -> int:
    return value

def source_owned(values: list[int]) -> None:
    for value in values:
        assert Previous(value) == value
"#;
    validate_language_wellformedness(source, "shadowed.py")
        .expect("source-owned functions are not canonical contract calls");
}
