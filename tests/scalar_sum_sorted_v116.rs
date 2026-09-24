use std::{fs, path::Path};

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};
use maledictus::python_contracts::verify_contract_module;

const FIXTURE: &str = "tests/functional/verification/test_sum_sorted.py";

#[test]
fn production_issuance_uses_the_new_direct_scalar_fragment_identity() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("sequence.py"),
        "from typing import List\n\ndef total(values: List[int]) -> int:\n    return sum(values)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "sequence.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
}

#[test]
fn integer_sum_obeys_empty_singleton_negative_and_concat_semantics() {
    let verification = verify_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(left: List[int], right: List[int]) -> None:
    Requires(list_pred(left) and list_pred(right))
    empty: List[int] = []
    singleton = [-7]
    combined = left + right
    assert sum(empty) == 0
    assert sum(singleton) == -7
    assert sum(combined) == sum(left) + sum(right)
"#,
        "sum_laws.py",
        &[],
    )
    .expect("integer sequence operations should lower to exact VC terms");

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn integer_sorted_is_fresh_ordered_and_preserves_duplicates_and_source() {
    let verification = verify_contract_module(
        r#"from nagini_contracts.contracts import *

def run() -> None:
    source = [3, 1, 2, 1]
    ordered = sorted(source)
    assert ordered is not source
    assert source == [3, 1, 2, 1]
    assert ordered == [1, 1, 2, 3]
    assert sum(ordered) == sum(source)
"#,
        "sorted_exact.py",
        &[],
    )
    .expect("default integer sorting should lower to its exact sequence value");

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn fresh_sorted_result_differs_from_inputs_but_inputs_may_alias() {
    let fresh = verify_contract_module(
        r#"from typing import List

def run(source: List[int], other: List[int]) -> None:
    ordered = sorted(source)
    assert ordered is not source
    assert ordered is not other
"#,
        "sorted_fresh_from_inputs.py",
        &[],
    )
    .expect("a sorted allocation is distinct from every live input list");
    assert!(fresh.passed, "{fresh:#?}");

    let may_alias = verify_contract_module(
        r#"from typing import List

def run(left: List[int], right: List[int]) -> None:
    assert left is not right
"#,
        "input_aliasing.py",
        &[],
    )
    .expect("input aliasing should remain a proof question");
    assert!(!may_alias.passed, "{may_alias:#?}");
}

#[test]
fn symbolic_sorted_proves_nondecreasing_neighbors_but_not_strict_order() {
    let verification = verify_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int]) -> None:
    Requires(list_pred(values))
    ordered = sorted(values)
    Assert(Forall(int, lambda i: (Implies(i >= 0 and i < len(ordered) - 1, ordered[i] <= ordered[i + 1]), [[ordered[i]]])))
    Assert(Forall(int, lambda i: (Implies(i >= 0 and i < len(ordered) - 1, ordered[i] < ordered[i + 1]), [[ordered[i]]])))
"#,
        "sorted_symbolic_order.py",
        &[],
    )
    .expect("well-guarded symbolic neighbor comparisons should lower");

    assert!(!verification.passed, "{verification:#?}");
    let failures = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":assert:") && !obligation.satisfied())
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{verification:#?}");
    assert_eq!(failures[0].line, 8, "{verification:#?}");
}

#[test]
fn equal_sum_nonpermutation_is_not_accepted_as_a_sorted_result() {
    let verification = verify_contract_module(
        r#"from nagini_contracts.contracts import *

def run() -> None:
    source = [3, 2]
    ordered = sorted(source)
    assert sum(ordered) == 5
    assert ordered == [1, 4]
"#,
        "sorted_not_equal_sum_summary.py",
        &[],
    )
    .expect("an incorrect sorted value should be refuted, not refused");

    assert!(!verification.passed, "{verification:#?}");
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":assert:") && !obligation.satisfied())
            .count(),
        1,
        "{verification:#?}"
    );
}

#[test]
fn partial_string_sorted_summary_does_not_invent_permutation_or_order() {
    let verification = verify_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[str]) -> None:
    Requires(list_pred(values))
    ordered = sorted(values)
    assert len(ordered) == len(values)
    assert ordered == values
"#,
        "sorted_string_partial.py",
        &[],
    )
    .expect("the existing string summary should remain sound but incomplete");

    assert!(!verification.passed, "{verification:#?}");
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":assert:") && !obligation.satisfied())
            .count(),
        1,
        "{verification:#?}"
    );
}

#[test]
fn canonical_sum_is_shadowing_aware() {
    let failure = verify_contract_module(
        "from typing import List\n\ndef run(sum: int, values: List[int]) -> int:\n    return sum(values)\n",
        "shadowed_sum.py",
        &[],
    )
    .expect_err("a parameter named sum must not receive builtin sequence semantics");
    assert_eq!(
        failure.code,
        "frontend.python.contracts.canonical-helper-shadowed"
    );

    let verification = verify_contract_module(
        "def sum(value: int) -> int:\n    return value + 1\n\ndef run() -> None:\n    assert sum(2) == 3\n",
        "source_sum.py",
        &[],
    )
    .expect("a source-owned sum function keeps its verified source semantics");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn sum_does_not_erase_an_exceptional_source_argument() {
    let failure = verify_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

def select(values: List[int], index: int) -> List[int]:
    Exsures(IndexError, True)
    return [values[index]]

def run(values: List[int], index: int) -> int:
    return sum(select(values, index))
"#,
        "sum_exceptional_argument.py",
        &[],
    )
    .expect_err("sum must not erase the source call's exceptional outcome");
    assert_eq!(
        failure.code,
        "frontend.python.contracts.sum-argument-exceptional-call-unsupported"
    );
}

#[test]
fn quantified_neighbor_guards_require_matching_length_and_one_element_slack() {
    let insufficient = verify_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int]) -> None:
    Assert(Forall(int, lambda i: (Implies(i >= 0 and i < len(values), values[i] <= values[i + 1]), [[values[i]]])))
"#,
        "quantifier_insufficient_slack.py",
        &[],
    )
    .expect_err("i + 1 requires one element of upper-bound slack");
    assert_eq!(
        insufficient.code,
        "frontend.python.contracts.quantified-index-unguarded"
    );

    let wrong_collection = verify_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int], other: List[int]) -> None:
    Assert(Forall(int, lambda i: (Implies(i >= 0 and i < len(other) - 1, values[i] <= values[i + 1]), [[values[i]]])))
"#,
        "quantifier_wrong_collection.py",
        &[],
    )
    .expect("a mismatched length guard must become a failed safety proof");
    assert!(!wrong_collection.passed, "{wrong_collection:#?}");
    assert!(
        wrong_collection.obligations.iter().any(|obligation| {
            obligation.id.contains("exception-undeclared:IndexError") && !obligation.satisfied()
        }),
        "{wrong_collection:#?}"
    );
}

#[test]
fn exact_sum_sorted_fixture_is_a_scalar_gain_only() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, FIXTURE)
        .unwrap_or_else(|error| panic!("scalar {FIXTURE}: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(scalar.actual, scalar.expected, "{scalar:#?}");

    let heap = check_pinned_heap_fixture(&suite, &pin, FIXTURE)
        .expect_err("the heap frontend does not yet implement exact sorted values");
    assert!(
        heap.contains("frontend.python.heap.expression-unsupported"),
        "{heap}"
    );

    let reference = check_pinned_reference_fixture(&suite, &pin, FIXTURE)
        .expect_err("the fixture has no nominal-reference declarations");
    assert!(
        reference.contains("frontend.python.references.empty-module"),
        "{reference}"
    );
}
