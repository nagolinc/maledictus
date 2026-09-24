use std::path::PathBuf;

use maledictus::conformance::{ConformanceMatchKind, check_heap_source, check_pinned_heap_fixture};
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
        .expect_err("unsupported tuple-return semantics must refuse before proof issuance")
}

#[test]
fn fixed_tuple_returns_are_checked_and_reusable_by_source_callers() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import Tuple

def pair(left: str, right: int) -> Tuple[str, int]:
    Ensures(Result()[0] == left)
    Ensures(Result()[1] == right)
    return left, right

def run() -> int:
    value = pair("ready", 7)
    assert value[0] == "ready"
    assert value[1] == 7
    return value[1]
"#,
        "v62_fixed_tuple_return.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn tuple_return_shape_mismatches_and_variadic_annotations_fail_closed() {
    let wrong_shape = refusal(
        "from typing import Tuple\n\ndef pair() -> Tuple[str, int]:\n    return 'ready', False\n",
        "v62_tuple_return_wrong_shape.py",
    );
    assert_eq!(
        wrong_shape.code, "frontend.python.heap.function-return-type-mismatch",
        "{wrong_shape:#?}"
    );

    let variadic = refusal(
        "from typing import Tuple\n\ndef values() -> Tuple[int, ...]:\n    return (1, 2)\n",
        "v62_variadic_tuple_return.py",
    );
    assert_eq!(
        variadic.code, "frontend.python.heap.type-unsupported",
        "{variadic:#?}"
    );
}

#[test]
fn multiline_tuple_postcondition_reports_the_failing_result_conjunct() {
    let result = check_heap_source(
        r#"from nagini_contracts.contracts import *
from typing import Tuple

def test(a: int, b: int) -> Tuple[int, int]:
    Ensures(
        ((True and
        True) and
        True) and
        #:: ExpectedOutput(postcondition.violated:assertion.false)
        (Result()[0] == a and
        Result()[1] == b)
        )
    return b, a
"#,
        "multiline_tuple_postcondition.py",
    )
    .unwrap_or_else(|error| panic!("multiline tuple-return source was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual.len(), 1, "{result:#?}");
    assert_eq!(result.actual[0].line, 10, "{result:#?}");
}

#[test]
fn pinned_ignored_tuple_fixture_is_not_reported_as_executed_semantics() {
    let suite = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(".upstream/nagini");
    let pin = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_heap_fixture(
        &suite,
        &pin,
        "tests/functional/verification/issues/00026.py",
    )
    .unwrap_or_else(|error| panic!("exact upstream tuple-return fixture was refused: {error}"));

    assert_eq!(result.analysis_kind, ConformanceMatchKind::ProfileIgnored);
    assert!(!result.passed, "{result:#?}");
    assert!(result.expected.is_empty(), "{result:#?}");
    assert!(result.actual.is_empty(), "{result:#?}");
}
