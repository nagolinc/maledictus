use std::path::PathBuf;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::{ContractVerification, verify_contract_module};

fn verify(source: &str, path: &str) -> ContractVerification {
    verify_contract_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it was refused with {}: {}",
            failure.code, failure.message
        )
    })
}

#[test]
fn sorted_returns_a_fresh_same_length_primitive_list() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def copy_length(values: List[int]) -> List[int]:
    Requires(list_pred(values))
    Ensures(list_pred(Result()))
    Ensures(len(Result()) == len(values))
    result = sorted(values)
    return result
"#,
        "sorted_same_length.py",
    );
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn direct_sorted_return_uses_the_same_total_summary() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def copy_length(values: List[str]) -> List[str]:
    Requires(list_pred(values))
    Ensures(len(Result()) == len(values))
    return sorted(values)
"#,
        "sorted_direct_return.py",
    );
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn sorted_summary_does_not_invent_identity_or_element_facts() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def not_identity(values: List[int]) -> None:
    Requires(list_pred(values))
    Requires(len(values) == 2)
    result = sorted(values)
    assert result[0] == values[0]
"#,
        "sorted_no_invented_element_fact.py",
    );
    assert!(!verification.passed, "{verification:#?}");
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":assert:"))
            .filter(|obligation| !obligation.satisfied())
            .count(),
        1,
        "{verification:#?}"
    );
}

#[test]
fn sorted_is_not_confused_with_a_shadowed_callable() {
    let failure = verify_contract_module(
        "from typing import List\n\ndef run(sorted: int, values: List[int]) -> List[int]:\n    return sorted(values)\n",
        "shadowed_sorted.py",
        &[],
    )
    .expect_err("shadowed sorted must not receive the canonical builtin summary");
    assert_eq!(
        failure.code,
        "frontend.python.contracts.canonical-helper-shadowed"
    );
}

#[test]
fn source_owned_sorted_function_keeps_its_own_verified_semantics() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def sorted(values: List[int]) -> List[int]:
    return values

def run(values: List[int]) -> List[int]:
    Ensures(Result() == values)
    return sorted(values)
"#,
        "source_sorted.py",
    );
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn repeated_sorted_results_fail_closed_until_invocations_are_distinguished() {
    let failure = verify_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int], flag: bool) -> None:
    Invariant(flag)
    while flag:
        copy = sorted(values)
"#,
        "repeated_sorted.py",
        &[],
    )
    .expect_err("looped sorted call must not reuse one symbolic result identity");
    assert_eq!(
        failure.code,
        "frontend.python.contracts.sorted-repeated-call-unsupported"
    );
}

#[test]
fn exact_upstream_sorted_fixture_matches_nagini() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/functional/verification/issues/00218.py";
    let result = check_pinned_scalar_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("scalar {fixture} was refused: {error}"));
    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual);
}

#[test]
fn sorted_refuses_a_nested_source_call_with_an_exceptional_outcome() {
    let failure = verify_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

def select(values: List[int], index: int) -> List[int]:
    Exsures(IndexError, True)
    return [values[index]]

def wrap(values: List[int], index: int) -> List[int]:
    Exsures(IndexError, True)
    return select(values, index)

def run(values: List[int], index: int) -> List[int]:
    return sorted(wrap(values, index))
"#,
        "sorted_exceptional_argument_call.py",
        &[],
    )
    .expect_err("sorted must not erase an exceptional outcome while lowering its argument");
    assert_eq!(
        failure.code,
        "frontend.python.contracts.sorted-argument-exceptional-call-unsupported"
    );
}

#[test]
fn sorted_evaluates_a_partial_argument_before_producing_its_normal_result() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int], index: int) -> List[int]:
    Exsures(IndexError, True)
    return sorted([values[index]])
"#,
        "sorted_partial_argument.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains(":exception-postcondition:")),
        "{verification:#?}"
    );
}

#[test]
fn sequential_integer_sorted_calls_are_distinct_allocations_with_the_same_exact_value() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int]) -> None:
    Requires(len(values) == 1)
    first = sorted(values)
    second = sorted(values)
    assert first is not second
    assert first[0] == second[0]
"#,
        "sorted_sequential_results.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn sorted_refuses_nonlists_global_shadowing_and_nested_contexts() {
    let nonlist = verify_contract_module(
        "from typing import Tuple\n\ndef run(values: Tuple[int, int]) -> Tuple[int, int]:\n    return sorted(values)\n",
        "sorted_nonlist.py",
        &[],
    )
    .expect_err("the current summary is defined only for homogeneous List values");
    assert_eq!(
        nonlist.code,
        "frontend.python.contracts.sorted-iterable-type-unsupported"
    );

    let global_shadow = verify_contract_module(
        "from typing import List\n\nsorted = 7\n\ndef run(values: List[int]) -> List[int]:\n    return sorted(values)\n",
        "sorted_global_shadow.py",
        &[],
    )
    .expect_err("a global runtime binding must suppress the builtin summary");
    assert_ne!(
        global_shadow.code,
        "frontend.python.contracts.sorted-iterable-type-unsupported"
    );

    let nested = verify_contract_module(
        "from typing import List\n\ndef run(values: List[int]) -> int:\n    return len(sorted(values))\n",
        "sorted_nested_context.py",
        &[],
    )
    .expect_err("unsupported nested sorted contexts must fail closed");
    assert_eq!(
        nested.code,
        "frontend.python.contracts.expression-unsupported"
    );
}
