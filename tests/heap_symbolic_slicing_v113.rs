use std::path::PathBuf;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_heap_fixture};
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str) -> HeapContractVerification {
    verify_heap_module(source, "heap_symbolic_slicing.py", &[]).unwrap_or_else(|failure| {
        panic!(
            "expected symbolic slicing source to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refuse(source: &str) -> ContractFailure {
    verify_heap_module(source, "heap_symbolic_slicing_adversary.py", &[])
        .expect_err("invalid symbolic slicing must refuse before proof issuance")
}

#[test]
fn symbolic_list_slice_is_typed_and_owns_its_fresh_result() {
    let verification = verify(
        r#"from typing import List
from nagini_contracts.contracts import Acc, Ensures, Requires, Result, list_pred

def stride(values: List[int]) -> List[int]:
    Requires(Acc(list_pred(values)))
    Ensures(Acc(list_pred(Result())))
    return values[::2]

def reverse(values: List[int]) -> List[int]:
    Requires(Acc(list_pred(values)))
    Ensures(Acc(list_pred(Result())))
    return values[::-1]
"#,
    );

    assert!(verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":postcondition:"))
            .all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn dynamic_and_zero_steps_remain_explicit_failures() {
    let dynamic = refuse(
        "from typing import List\ndef run(values: List[int], step: int) -> List[int]:\n    return values[::step]\n",
    );
    assert_eq!(
        dynamic.code, "frontend.python.heap.slice-step-unsupported",
        "{dynamic:#?}"
    );

    let zero = refuse(
        "from typing import List\ndef run(values: List[int]) -> List[int]:\n    return values[::0]\n",
    );
    assert_eq!(
        zero.code, "frontend.python.heap.slice-step-zero",
        "{zero:#?}"
    );
}

#[test]
fn upstream_slice_step_is_semantically_superseded_not_relabelled_as_an_exact_refusal() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let result = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/translation/test_slice_step.py",
    )
    .unwrap_or_else(|error| panic!("symbolic stepped slice was refused: {error}"));

    assert!(!result.passed, "must not relabel as exact: {result:#?}");
    assert!(result.semantic_verified, "{result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SupersededUpstreamUnsupported,
        "{result:#?}"
    );
    assert!(!result.expected.is_empty(), "{result:#?}");
    assert!(result.actual.is_empty(), "{result:#?}");
}
