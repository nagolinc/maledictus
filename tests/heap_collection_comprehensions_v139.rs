use std::path::PathBuf;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_heap_fixture};
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};
use maledictus::vc::ObligationStatus;

const FIXTURES: [&str; 3] = [
    "tests/functional/verification/test_list_comprehension_filter.py",
    "tests/functional/verification/test_set_comprehension.py",
    "tests/functional/verification/test_dict_comprehension.py",
];

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refuse(source: &str) -> ContractFailure {
    verify_heap_module(source, "unsupported_heap_comprehension.py", &[])
        .expect_err("unsupported comprehension behavior must fail closed")
}

#[test]
fn exact_collection_comprehension_fixtures_convert_semantically() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    for fixture in FIXTURES {
        let result = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("heap classifier refused {fixture}: {error}"));
        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(result.expected, result.actual, "{fixture}: {result:#?}");
        assert_eq!(
            result.analysis_kind,
            ConformanceMatchKind::SemanticVerification,
            "{fixture}: {result:#?}"
        );
    }
}

#[test]
fn list_set_and_dict_comprehensions_prove_forward_semantics() {
    let result = verify(
        r#"from typing import Dict, List, Set
from nagini_contracts.contracts import *

def check(src: List[int]) -> None:
    Requires(list_pred(src))
    Requires(len(src) > 0)
    Requires(src[0] > 5)
    Requires(src[len(src) - 1] > 5)
    values = [x + 1 for x in src if x > 5]  # type: List[int]
    elements = {x + 1 for x in src if x > 5}  # type: Set[int]
    mapping = {x: x + 1 for x in src if x > 5}  # type: Dict[int, int]
    Assert(src[0] + 1 in values)
    Assert(src[0] + 1 in elements)
    Assert(src[len(src) - 1] in mapping)
    Assert(mapping[src[len(src) - 1]] == src[len(src) - 1] + 1)
    Assert(len(values) <= len(src))
"#,
        "heap_collection_comprehensions.py",
    );
    assert!(result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .all(|obligation| obligation.satisfied()),
        "{result:#?}"
    );
}

#[test]
fn unsupported_membership_and_mapping_claims_are_refuted() {
    let result = verify(
        r#"from typing import Dict, List, Set
from nagini_contracts.contracts import *

def check(src: List[int]) -> None:
    Requires(list_pred(src))
    Requires(len(src) > 0)
    values = [x + 1 for x in src]  # type: List[int]
    elements = {x + 1 for x in src}  # type: Set[int]
    mapping = {x: x + 1 for x in src}  # type: Dict[int, int]
    Assert(src[0] in values)
    Assert(12345 in elements)
    Assert(12345 in mapping)
"#,
        "false_heap_collection_comprehensions.py",
    );
    assert!(!result.passed, "{result:#?}");
    assert_eq!(
        result
            .obligations
            .iter()
            .filter(|obligation| obligation.status == ObligationStatus::Refuted)
            .count(),
        3,
        "{result:#?}"
    );
}

#[test]
fn dictionary_lookup_requires_a_proven_comprehension_key() {
    let result = verify(
        r#"from typing import Dict, List
from nagini_contracts.contracts import *

def check(src: List[int]) -> None:
    Requires(list_pred(src))
    mapping = {x: x + 1 for x in src}  # type: Dict[int, int]
    missing = mapping[12345]
"#,
        "heap_dict_comprehension_missing_key.py",
    );
    assert!(!result.passed, "{result:#?}");
    assert!(
        result.obligations.iter().any(|obligation| {
            obligation.status == ObligationStatus::Refuted
                && obligation
                    .id
                    .contains(":application-precondition:KeyError:")
        }),
        "{result:#?}"
    );
}

#[test]
fn borrowed_sources_require_list_predicate_ownership() {
    let result = verify(
        r#"from typing import List

def check(src: List[int]) -> None:
    values = [x + 1 for x in src]  # type: List[int]
"#,
        "heap_comprehension_without_list_predicate.py",
    );
    assert!(!result.passed, "{result:#?}");
    assert!(
        result.obligations.iter().any(|obligation| {
            obligation.status == ObligationStatus::Refuted
                && obligation
                    .id
                    .contains(":property-precondition:list-predicate:")
        }),
        "{result:#?}"
    );
}

#[test]
fn effectful_or_structurally_richer_comprehensions_fail_closed() {
    let cases = [
        (
            "frontend.python.heap.comprehension-generator-count",
            "values = [x + y for x in src for y in src]  # type: List[int]",
        ),
        (
            "frontend.python.heap.comprehension-target-unsupported",
            "values = [x for x, y in src]  # type: List[int]",
        ),
        (
            "frontend.python.heap.comprehension-iterable-expression-unsupported",
            "values = [x for x in list(src)]  # type: List[int]",
        ),
        (
            "frontend.python.heap.comprehension-mapper-effect-unsupported",
            "values = [abs(x) for x in src]  # type: List[int]",
        ),
        (
            "frontend.python.heap.comprehension-filter-effect-unsupported",
            "values = [x for x in src if bool(x)]  # type: List[int]",
        ),
    ];

    for (expected_code, statement) in cases {
        let source = format!(
            "from typing import List\n\ndef check(src: List[int]) -> None:\n    {statement}\n"
        );
        let failure = refuse(&source);
        assert_eq!(failure.code, expected_code, "{failure:#?}");
    }
}
