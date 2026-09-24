use std::path::PathBuf;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_heap_fixture};
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};
use maledictus::vc::ObligationStatus;

const FIXTURES: [&str; 3] = [
    "tests/functional/verification/issues/00271.py",
    "tests/functional/verification/issues/00276.py",
    "tests/functional/verification/issues/00278.py",
];

fn verify(source: &str) -> HeapContractVerification {
    verify_heap_module(source, "generic_pseq_wrapper.py", &[]).unwrap_or_else(|failure| {
        panic!(
            "expected generic PSeq wrapper source to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refuse(source: &str) -> ContractFailure {
    verify_heap_module(source, "generic_pseq_wrapper_adversary.py", &[])
        .expect_err("unsupported generic PSeq wrapper behavior must fail closed")
}

#[test]
fn exact_generic_pseq_wrapper_fixtures_convert_semantically() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    for fixture in FIXTURES {
        let result = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("heap classifier refused {fixture}: {error}"));
        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(result.expected, result.actual, "{fixture}: {result:#?}");
        assert!(result.semantic_verified, "{fixture}: {result:#?}");
        assert_eq!(
            result.analysis_kind,
            ConformanceMatchKind::SemanticVerification,
            "{fixture}: {result:#?}"
        );
    }
}

#[test]
fn direct_fixture_heap_semantics_prove() {
    for (path, source) in [
        (
            "00276.py",
            include_str!("../.upstream/nagini/tests/functional/verification/issues/00276.py"),
        ),
        (
            "00278.py",
            include_str!("../.upstream/nagini/tests/functional/verification/issues/00278.py"),
        ),
        (
            "00271.py",
            include_str!("../.upstream/nagini/tests/functional/verification/issues/00271.py"),
        ),
    ] {
        let verification = verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
            panic!(
                "heap verifier refused {path} with {}: {}",
                failure.code, failure.message
            )
        });
        assert!(verification.passed, "{path}: {verification:#?}");
        assert!(
            verification
                .obligations
                .iter()
                .all(|obligation| obligation.satisfied()),
            "{path}: {verification:#?}"
        );
    }
}

#[test]
fn multiple_closed_specializations_keep_distinct_field_sorts() {
    let verification = verify(
        r#"from typing import Generic, Optional, TypeVar
from nagini_contracts.contracts import *

T = TypeVar('T')

class Box(Generic[T]):
    def __init__(self, value: Optional[T]) -> None:
        Ensures(Acc(self.value) and self.value is value)
        self.value = value

def run() -> None:
    integer = Box[int](3)
    sequence = Box[PSeq[int]](PSeq(1, 2, 3))
    Assert(integer.value == 3)
    Assert(sequence.value[1] == 2)
"#,
    );
    assert!(verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn narrowed_optional_specializations_reject_none_and_omitted_values() {
    let prefix = r#"from typing import Generic, Optional, TypeVar
from nagini_contracts.contracts import *
T = TypeVar('T')
class Box(Generic[T]):
    def __init__(self, value: Optional[T] = None) -> None:
        Ensures(Acc(self.value) and self.value is value)
        self.value = value
"#;
    for body in [
        "def run() -> None:\n    value = Box[PSeq[int]]()\n",
        "def run() -> None:\n    value = Box[PSeq[int]](None)\n",
    ] {
        let failure = refuse(&format!("{prefix}{body}"));
        assert!(
            matches!(
                failure.code,
                "frontend.python.heap.call-argument-missing"
                    | "frontend.python.heap.constructor-call-arguments"
                    | "frontend.python.heap.constructor-argument-type"
                    | "frontend.python.heap.constructor-call-argument-type"
            ),
            "{failure:#?}"
        );
    }
}

#[test]
fn richer_pseq_specializations_and_typevar_placements_fail_closed() {
    let nested = refuse(
        r#"from typing import Generic, Optional, TypeVar
from nagini_contracts.contracts import *
T = TypeVar('T')
class Box(Generic[T]):
    def __init__(self, value: Optional[T]) -> None:
        self.value = value
def run() -> None:
    value = Box[PSeq[PSeq[int]]](PSeq(PSeq(1)))
"#,
    );
    assert_eq!(
        nested.code, "frontend.python.heap.typevar-specialization-unsupported",
        "{nested:#?}"
    );

    let rich_annotation = refuse(
        r#"from typing import Generic, Optional, TypeVar
from nagini_contracts.contracts import *
T = TypeVar('T')
class Box(Generic[T]):
    def __init__(self, value: PSeq[T]) -> None:
        self.value = value
def run() -> None:
    value = Box[int](PSeq(1))
"#,
    );
    assert_eq!(
        rich_annotation.code, "frontend.python.heap.typevar-annotation-unsupported",
        "{rich_annotation:#?}"
    );
}

#[test]
fn false_pseq_wrapper_postcondition_is_refuted() {
    let source = include_str!("../.upstream/nagini/tests/functional/verification/issues/00276.py")
        .replacen("len(Result().value) == 3", "len(Result().value) == 4", 1);
    let verification = verify_heap_module(&source, "false_generic_pseq_wrapper.py", &[])
        .expect("supported generic PSeq source should lower even when its claim is false");
    assert!(!verification.passed, "{verification:#?}");
    assert!(
        verification.obligations.iter().any(|obligation| {
            obligation.id.contains("test_produce_seq:postcondition")
                && obligation.status == ObligationStatus::Refuted
        }),
        "{verification:#?}"
    );
}

#[test]
fn constructor_factory_inlining_respects_local_shadowing() {
    let failure = refuse(
        r#"from typing import Generic, TypeVar
from nagini_contracts.contracts import *
T = TypeVar('T')
class Box(Generic[T]):
    def __init__(self, value: T) -> None:
        Ensures(Acc(self.value))
        self.value = value
def produce() -> Box[PSeq[int]]:
    return Box[PSeq[int]](PSeq(1, 2, 3))
def run(produce: object) -> None:
    value = produce()
"#,
    );
    assert_ne!(
        failure.code, "frontend.python.heap.field-unknown",
        "{failure:#?}"
    );
}
