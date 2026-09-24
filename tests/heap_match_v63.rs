use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refusal(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("unsupported pattern semantics must refuse before proof issuance")
}

#[test]
fn ordered_match_cases_support_singletons_values_captures_or_as_and_guards() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

def choose(value: int) -> int:
    Ensures(Result() >= 0)
    match value:
        case True:
            return 9
        case 0 | 1:
            return 0
        case int() as captured if captured > 0:
            return captured
        case _:
            return 0
"#,
        "v63_ordered_match.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn singleton_patterns_keep_python_bool_and_int_identity_rules_distinct() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

def int_subject() -> int:
    match 1:
        case True:
            assert False
            return 0
        case _:
            return 1

def bool_subject() -> int:
    match True:
        case 1:
            return 1
        case _:
            assert False
            return 0
"#,
        "v63_bool_int_match.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn qualified_value_patterns_are_permission_checked_heap_reads() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Point:
    def __init__(self, x: int, y: int) -> None:
        Ensures(Acc(self.x) and Acc(self.y))
        Ensures(self.x == x and self.y == y)
        self.x = x
        self.y = y

def run() -> None:
    point = Point(3, 4)
    match 4:
        case point.x:
            assert False
        case point.y:
            pass
        case _:
            assert False
"#,
        "v63_qualified_value_match.py",
    );

    assert!(verification.passed, "{verification:#?}");

    let missing_permission = verify(
        r#"from nagini_contracts.contracts import *

class Point:
    x: int

def run(point: Point) -> None:
    match 3:
        case point.x:
            pass
        case _:
            pass
"#,
        "v63_qualified_value_match_missing_permission.py",
    );
    assert!(!missing_permission.passed, "{missing_permission:#?}");
    assert!(
        missing_permission
            .obligations
            .iter()
            .any(|item| item.id.contains("field-permission") && !item.satisfied()),
        "{missing_permission:#?}"
    );
}

#[test]
fn pure_match_functions_may_inspect_reference_type_without_heap_effects() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

@Pure
def is_integer(value: object) -> bool:
    Ensures(Result() == isinstance(value, int))
    match value:
        case int():
            return True
        case _:
            return False
"#,
        "v63_pure_reference_match.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn unsupported_destructuring_and_dynamic_class_patterns_fail_closed() {
    let sequence = refusal(
        "def run(value: object) -> None:\n    match value:\n        case [first, second]:\n            pass\n",
        "v63_sequence_pattern.py",
    );
    assert_eq!(
        sequence.code, "frontend.python.heap.match-sequence-subject-unsupported",
        "{sequence:#?}"
    );

    let mapping = refusal(
        "def run(value: object) -> None:\n    match value:\n        case {'x': found}:\n            pass\n",
        "v63_mapping_pattern.py",
    );
    assert_eq!(
        mapping.code, "frontend.python.heap.match-mapping-unsupported",
        "{mapping:#?}"
    );

    let positional_class = refusal(
        "def run(value: object) -> None:\n    match value:\n        case int(found):\n            pass\n",
        "v63_positional_class_pattern.py",
    );
    assert_eq!(
        positional_class.code, "frontend.python.heap.match-class-arguments-unsupported",
        "{positional_class:#?}"
    );

    let shadowed = refusal(
        "def run(value: object, int: object) -> None:\n    match value:\n        case int():\n            pass\n",
        "v63_shadowed_class_pattern.py",
    );
    assert_eq!(
        shadowed.code, "frontend.python.heap.match-class-target-shadowed",
        "{shadowed:#?}"
    );
}

#[test]
fn exact_upstream_match_fixtures_preserve_all_expected_diagnostics() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/verification/test_match.py",
        "tests/functional/verification/test_match_pure.py",
    ] {
        let result = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("exact upstream {fixture} was refused: {error}"));
        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(result.expected, result.actual, "{fixture}: {result:#?}");
    }
}
