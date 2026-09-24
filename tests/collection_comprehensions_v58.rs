use std::path::PathBuf;

use maledictus::conformance::{
    ExpectedDiagnostic, check_pinned_scalar_fixture, check_scalar_source,
};
use maledictus::python_contracts::{
    ContractFailure, ContractVerification, parse_external_contract_module,
    verify_and_export_source_contract_module, verify_contract_module,
    verify_contract_module_with_imports,
};
use maledictus::solver::discharge;
use maledictus::vc::{Obligation, ObligationExpectation, Sort, Term};

fn verify(source: &str, path: &str) -> ContractVerification {
    verify_contract_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it was refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refusal(source: &str, path: &str) -> ContractFailure {
    verify_contract_module(source, path, &[])
        .expect_err("expected the source to be refused before proof issuance")
}

fn assert_refusal(source: &str, path: &str, expected_code: &str) {
    let failure = refusal(source, path);
    assert_eq!(failure.code, expected_code, "{failure:#?}");
}

fn assert_all_assertions_proved(verification: &ContractVerification, expected: usize) {
    assert!(verification.passed, "{verification:#?}");
    let assertions = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":assert:"))
        .collect::<Vec<_>>();
    assert_eq!(assertions.len(), expected, "{verification:#?}");
    assert!(
        assertions.iter().all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

fn diagnostic(code: &str, line: u32) -> ExpectedDiagnostic {
    ExpectedDiagnostic {
        code: code.to_owned(),
        line,
    }
}

fn expected_fixture_diagnostics(fixture: &str) -> Vec<ExpectedDiagnostic> {
    let mut diagnostics = match fixture {
        "tests/functional/verification/test_list_comprehension.py" => vec![
            diagnostic("postcondition.violated:assertion.false", 24),
            diagnostic("assert.failed:assertion.false", 45),
        ],
        "tests/functional/verification/test_list_comprehension_filter.py" => vec![
            diagnostic("assert.failed:assertion.false", 23),
            diagnostic("assert.failed:assertion.false", 41),
            diagnostic("assert.failed:assertion.false", 55),
        ],
        "tests/functional/verification/test_dict_comprehension.py" => vec![
            diagnostic("assert.failed:assertion.false", 22),
            diagnostic("assert.failed:assertion.false", 40),
            diagnostic("application.precondition:assertion.false", 50),
            diagnostic("assert.failed:assertion.false", 69),
            diagnostic("assert.failed:assertion.false", 77),
            diagnostic("assert.failed:assertion.false", 100),
            diagnostic("assert.failed:assertion.false", 112),
        ],
        "tests/functional/verification/test_set_comprehension.py" => vec![
            diagnostic("assert.failed:assertion.false", 22),
            diagnostic("assert.failed:assertion.false", 38),
            diagnostic("assert.failed:assertion.false", 56),
            diagnostic("assert.failed:assertion.false", 66),
        ],
        _ => panic!("missing exact expectation map for {fixture}"),
    };
    diagnostics.sort();
    diagnostics
}

const UPSTREAM_COMPREHENSION_FIXTURES: [&str; 4] = [
    "tests/functional/verification/test_list_comprehension.py",
    "tests/functional/verification/test_list_comprehension_filter.py",
    "tests/functional/verification/test_dict_comprehension.py",
    "tests/functional/verification/test_set_comprehension.py",
];

#[test]
fn list_comprehensions_preserve_exact_length_indices_order_and_duplicates() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def run() -> None:
    singleton = [9]
    singleton_result = [x + 1 for x in singleton]  # type: List[int]
    assert len(singleton_result) == 1
    assert singleton_result[0] == 10

    source = [1, 2, 2, 3]
    identity = [x for x in source]  # type: List[int]
    mapped = [x + 10 for x in source]  # type: List[int]
    assert len(identity) == 4
    assert identity[0] == 1
    assert identity[1] == 2
    assert identity[2] == 2
    assert identity[3] == 3
    assert 2 in identity
    assert len(mapped) == 4
    assert mapped[0] == 11
    assert mapped[1] == 12
    assert mapped[2] == 12
    assert mapped[3] == 13
    assert source[0] == 1
    assert source[3] == 3
"#,
        "v58_list_exact_semantics.py",
    );

    assert_all_assertions_proved(&verification, 15);
}

#[test]
fn filtered_lists_preserve_selected_order_and_can_filter_every_element() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def run() -> None:
    source = [6, 1, 7]
    selected = [x + 1 for x in source if x > 5]  # type: List[int]
    assert len(selected) == 2
    assert selected[0] == 7
    assert selected[1] == 8
    assert 7 in selected
    assert 8 in selected

    rejected_source = [1, 2, 3]
    rejected = [x for x in rejected_source if x > 5]  # type: List[int]
    assert len(rejected) == 0
"#,
        "v58_filtered_list_order.py",
    );

    assert_all_assertions_proved(&verification, 6);
}

#[test]
fn comprehension_binders_shadow_without_overwriting_and_do_not_leak() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def run() -> None:
    x = 40
    source = [1, 2]
    mapped = [x + 1 for x in source]  # type: List[int]
    assert x == 40
    assert mapped[0] == 2
    assert mapped[1] == 3
"#,
        "v58_binder_shadowing.py",
    );
    assert_all_assertions_proved(&verification, 3);

    assert_refusal(
        r#"from typing import List

def run() -> None:
    source = [1]
    mapped = [x for x in source]  # type: List[int]
    assert x == 1
"#,
        "v58_binder_nonleak.py",
        "frontend.python.name.unresolved",
    );
}

#[test]
fn set_comprehensions_collapse_source_and_mapped_duplicates() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import List, Set

def run() -> None:
    source = [1, 1, 2, 3]
    identity = {x for x in source}  # type: Set[int]
    parity = {x % 2 for x in source}  # type: Set[int]
    assert len(identity) == 3
    assert 1 in identity
    assert 2 in identity
    assert 3 in identity
    assert len(parity) == 2
    assert 0 in parity
    assert 1 in parity
"#,
        "v58_set_duplicate_collapse.py",
    );

    assert_all_assertions_proved(&verification, 7);
}

#[test]
fn boolean_comprehension_keys_share_python_integer_key_identity() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import Dict, Set

def run() -> None:
    source = [False, True, True]
    keys = {x for x in source}  # type: Set[int]
    values = {x: (10 if x else 20) for x in source}  # type: Dict[int, int]
    assert len(keys) == 2
    assert False in keys and 0 in keys
    assert True in keys and 1 in keys
    assert len(values) == 2
    assert values[False] == 20 and values[0] == 20
    assert values[True] == 10 and values[1] == 10
"#,
        "v58_bool_int_key_normalization.py",
    );

    assert_all_assertions_proved(&verification, 6);
}

#[test]
fn dictionary_comprehensions_are_last_wins_and_ignore_later_filtered_duplicates() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import Dict

def run() -> None:
    source = [2, 4]
    last_wins = {x % 2: x for x in source}  # type: Dict[int, int]
    filtered = {x % 2: x for x in source if x < 4}  # type: Dict[int, int]
    assert len(last_wins) == 1 and 0 in last_wins and last_wins[0] == 4
    assert len(filtered) == 1 and 0 in filtered and filtered[0] == 2
"#,
        "v58_dict_last_wins.py",
    );

    assert_all_assertions_proved(&verification, 2);
}

#[test]
fn negative_modulo_in_comprehensions_uses_python_floor_semantics() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import Dict, List, Set

def run() -> None:
    source = [-3, -2, -1]
    remainders = [x % 2 for x in source]  # type: List[int]
    unique = {x % 2 for x in source}  # type: Set[int]
    by_remainder = {x % 2: x for x in source}  # type: Dict[int, int]
    assert remainders[0] == 1
    assert remainders[1] == 0
    assert remainders[2] == 1
    assert len(unique) == 2 and 0 in unique and 1 in unique
    assert by_remainder[0] == -2
    assert by_remainder[1] == -1
"#,
        "v58_negative_modulo.py",
    );

    assert_all_assertions_proved(&verification, 6);
}

#[test]
fn missing_dictionary_lookup_has_one_application_precondition_diagnostic() {
    let source = r#"from nagini_contracts.contracts import *
from typing import Dict, List

def run() -> None:
    source = [1, 2]
    values = {x: x + 1 for x in source}  # type: Dict[int, int]
    #:: ExpectedOutput(application.precondition:assertion.false)
    missing = values[99]
"#;
    let result = check_scalar_source(source, "v58_dict_missing_lookup.py").unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual, "{result:#?}");
    assert_eq!(result.actual.len(), 1, "{result:#?}");
    assert_eq!(
        result.actual[0].code,
        "application.precondition:assertion.false"
    );
    assert_eq!(result.actual[0].line, 8);
}

#[test]
fn repeated_comprehension_projections_share_one_sound_solver_obligation() {
    let binder = "item".to_owned();
    let comprehension = Term::ListComprehension {
        id: "repeated-projection".to_owned(),
        source: Box::new(Term::List {
            element_sort: Sort::Int,
            values: vec![
                Term::Int { value: 1 },
                Term::Int { value: 2 },
                Term::Int { value: 3 },
            ],
        }),
        binder: binder.clone(),
        element_sort: Sort::Int,
        mapped: Box::new(Term::Add {
            left: Box::new(Term::Variable {
                name: binder,
                sort: Sort::Int,
            }),
            right: Box::new(Term::Int { value: 1 }),
        }),
        filter: None,
    };
    let obligation = Obligation {
        id: "v58:repeated-comprehension-projections".to_owned(),
        expectation: ObligationExpectation::Prove,
        assumptions: Vec::new(),
        conclusion: Term::And {
            values: vec![
                Term::Equal {
                    left: Box::new(Term::ListLength {
                        value: Box::new(comprehension.clone()),
                    }),
                    right: Box::new(Term::Int { value: 3 }),
                },
                Term::Equal {
                    left: Box::new(Term::ListGet {
                        list: Box::new(comprehension.clone()),
                        index: Box::new(Term::Int { value: 1 }),
                    }),
                    right: Box::new(Term::Int { value: 3 }),
                },
                Term::ListContains {
                    list: Box::new(comprehension),
                    value: Box::new(Term::Int { value: 4 }),
                },
            ],
        },
        path: "v58_repeated_projection.vc".to_owned(),
        byte_offset: 0,
        line: 1,
        column: 1,
    };

    let result = discharge(&obligation).expect("repeated recursive terms must lower exactly once");
    assert!(result.satisfied(), "{result:#?}");
}

#[test]
fn malformed_or_effectful_typed_forall_triggers_cannot_waive_index_guards() {
    for (path, trigger) in [
        ("v58_forall_empty_trigger.py", "[]"),
        ("v58_forall_empty_trigger_group.py", "[[]]"),
    ] {
        let source = format!(
            r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int]) -> None:
    Requires(list_pred(values))
    Ensures(Forall(int, lambda i: (
        Implies(i >= 0 and i < len(values), values[i] == values[i]), {trigger})))
"#
        );
        assert_refusal(
            &source,
            path,
            "frontend.python.contracts.quantifier-trigger-unsupported",
        );
    }

    let effectful_trigger = verify(
        r#"from nagini_contracts.contracts import *

def observe(value: int) -> int:
    return value

def run() -> None:
    Ensures(Forall(int, lambda i: (i == i, [[observe(i)]])))
        "#,
        "v58_forall_effectful_trigger.py",
    );
    let purity_violations = effectful_trigger
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":purity-violation:"))
        .collect::<Vec<_>>();
    assert!(!effectful_trigger.passed, "{effectful_trigger:#?}");
    assert_eq!(purity_violations.len(), 1, "{effectful_trigger:#?}");
    assert_eq!(purity_violations[0].line, 7, "{effectful_trigger:#?}");
    assert!(!purity_violations[0].satisfied(), "{effectful_trigger:#?}");

    assert_refusal(
        r#"from nagini_contracts.contracts import *

def run() -> None:
    Ensures(Forall(int, lambda i: (i == i, [[i]])))
"#,
        "v58_forall_without_indexed_predicate.py",
        "frontend.python.contracts.quantified-index-unguarded",
    );

    assert_refusal(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int]) -> None:
    Requires(list_pred(values))
    Ensures(Forall(int, lambda i: (
        Implies(i >= 0 and i < len(values), values[i] == values[i]),
        [[undefined_trigger]])))
"#,
        "v58_forall_undefined_trigger.py",
        "frontend.python.name.unresolved",
    );

    assert_refusal(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int], scalar: int) -> None:
    Requires(list_pred(values))
    Ensures(Forall(int, lambda i: (
        Implies(i >= 0 and i < len(values), values[i] == values[i]),
        [[scalar[i]]])))
"#,
        "v58_forall_wrong_type_trigger.py",
        "frontend.python.contracts.quantified-index-collection-type",
    );

    assert_refusal(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int], scalar: int) -> None:
    Requires(list_pred(values))
    Ensures(Forall(int, lambda i: (
        Implies(i >= 0 and i < len(values), values[i] == values[i]),
        [[scalar]])))
"#,
        "v58_forall_free_name_trigger.py",
        "frontend.python.contracts.quantifier-trigger-unsupported",
    );

    for (path, trigger) in [
        ("v58_forall_mismatched_guard.py", "values[i]"),
        ("v58_forall_mismatched_trigger_guard.py", "bounds[i]"),
    ] {
        let source = format!(
            r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int], bounds: List[int]) -> None:
    Requires(list_pred(values))
    Requires(list_pred(bounds))
    Ensures(Forall(int, lambda i: (
        Implies(i >= 0 and i < len(bounds), values[i] == values[i]),
        [[{trigger}]])))
"#
        );
        assert_refusal(
            &source,
            path,
            "frontend.python.contracts.partial-operation-in-spec",
        );
    }
}

#[test]
fn every_guarded_forall_specification_context_routes_through_definedness_proof() {
    let loop_verification = verify_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int], bounds: List[int]) -> None:
    Requires(list_pred(values))
    Requires(list_pred(bounds))
    while False:
        Invariant(Forall(int, lambda i: (
            Implies(i >= 0 and i < len(bounds), values[i] == values[i]),
            [[values[i]]])))
"#,
        "v58_forall_loop_invariant_safety.py",
        &[],
    )
    .expect("a malformed invariant must become a failed proof, not a frontend panic");
    assert!(!loop_verification.passed, "{loop_verification:#?}");
    assert!(
        loop_verification.obligations.iter().any(|obligation| {
            obligation.id.contains("invariant-establishment") && !obligation.satisfied()
        }),
        "{loop_verification:#?}"
    );

    assert_refusal(
        r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int], bounds: List[int]) -> None:
    Requires(list_pred(values))
    Requires(list_pred(bounds))
    Exsures(ValueError, Forall(int, lambda i: (
        Implies(i >= 0 and i < len(bounds), values[i] == values[i]),
        [[values[i]]])))
    raise ValueError()
"#,
        "v58_forall_exceptional_postcondition_safety.py",
        "frontend.python.contracts.partial-operation-in-spec",
    );

    assert_refusal(
        r#"from nagini_contracts.contracts import *
from typing import List

values = [1]
flag: bool = Forall(int, lambda i: (
    Implies(i >= 0 and i < len(values), values[i] == values[i]),
    [[values[i]]]))
"#,
        "v58_forall_module_initializer_safety.py",
        "frontend.python.contracts.specification-safety-bypass",
    );
}

#[test]
fn guarded_forall_safety_survives_source_and_external_summary_boundaries() {
    let provider_source = r#"from nagini_contracts.contracts import *
from typing import List

def identity(values: List[int]) -> List[int]:
    Requires(list_pred(values))
    Ensures(list_pred(ResultT(List[int])))
    Ensures(len(Result()) == len(values))
    Ensures(Forall(int, lambda i: (
        Implies(i >= 0 and i < len(Result()), Result()[i] == values[i]),
        [[values[i]]])))
    return [value for value in values]
"#;
    let (provider_verification, provider) = verify_and_export_source_contract_module(
        provider_source,
        "v58_source_summary_provider.py",
        "v58_provider",
        &[],
    )
    .expect("the source provider and its quantified safety must verify before export");
    assert!(provider_verification.passed, "{provider_verification:#?}");

    let caller = r#"from nagini_contracts.contracts import *
from typing import List
from v58_provider import identity

def call(values: List[int]) -> List[int]:
    Requires(list_pred(values))
    Ensures(list_pred(ResultT(List[int])))
    Ensures(len(Result()) == len(values))
    return identity(values)
"#;
    let source_caller = verify_contract_module_with_imports(
        caller,
        "v58_source_summary_caller.py",
        &[],
        &[provider],
    )
    .expect("the verified source summary must remain callable");
    assert!(source_caller.passed, "{source_caller:#?}");

    let external = parse_external_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

@ContractOnly
def identity(values: List[int]) -> List[int]:
    Requires(list_pred(values))
    Ensures(list_pred(ResultT(List[int])))
    Ensures(len(Result()) == len(values))
    Ensures(Forall(int, lambda i: (
        Implies(i >= 0 and i < len(Result()), Result()[i] == values[i]),
        [[values[i]]])))
    pass
"#,
        "v58_external_summary_provider.py",
        "v58_external",
    )
    .expect("the explicit external boundary must retain typed safety clauses");
    let external_caller_source = caller.replace("v58_provider", "v58_external");
    let external_caller = verify_contract_module_with_imports(
        &external_caller_source,
        "v58_external_summary_caller.py",
        &[],
        &[external],
    )
    .expect("the checked external summary must remain callable");
    assert!(external_caller.passed, "{external_caller:#?}");

    let unsafe_external = parse_external_contract_module(
        r#"from nagini_contracts.contracts import *
from typing import List

@ContractOnly
def consume(values: List[int], bounds: List[int]) -> None:
    Requires(list_pred(values))
    Requires(list_pred(bounds))
    Requires(Forall(int, lambda i: (
        Implies(i >= 0 and i < len(bounds), values[i] == values[i]),
        [[values[i]]])))
    pass
"#,
        "v58_external_precondition_provider.py",
        "v58_unsafe_external",
    )
    .expect("external precondition safety is a caller obligation, not parser trust");
    let unsafe_caller = verify_contract_module_with_imports(
        r#"from nagini_contracts.contracts import *
from typing import List
from v58_unsafe_external import consume

def call(values: List[int], bounds: List[int]) -> None:
    Requires(list_pred(values))
    Requires(list_pred(bounds))
    consume(values, bounds)
"#,
        "v58_external_precondition_caller.py",
        &[],
        &[unsafe_external],
    )
    .expect("an unproved external precondition must be a failed obligation, not a panic");
    assert!(!unsafe_caller.passed, "{unsafe_caller:#?}");
}

#[test]
fn unsupported_comprehension_shapes_fail_closed_through_the_public_frontend() {
    let cases = [
        (
            "v58_multiple_generators.py",
            r#"from typing import List
def run() -> None:
    left = [1]
    right = [2]
    result = [x + y for x in left for y in right]  # type: List[int]
"#,
            "frontend.python.contracts.comprehension-generator-count",
        ),
        (
            "v58_tuple_target.py",
            r#"from typing import List
def run() -> None:
    source = [1, 2]
    result = [x + y for (x, y) in source]  # type: List[int]
"#,
            "frontend.python.contracts.comprehension-target-unsupported",
        ),
        (
            "v58_nested_comprehension.py",
            r#"from typing import List
def run() -> None:
    source = [1, 2]
    result = [[y for y in source] for x in source]  # type: List[int]
"#,
            "frontend.python.contracts.comprehension-mapper-effect-unsupported",
        ),
        (
            "v58_effectful_iterable.py",
            r#"from typing import List
def make() -> List[int]:
    return [1]
def run() -> None:
    result = [x for x in make()]  # type: List[int]
"#,
            "frontend.python.contracts.comprehension-iterable-expression-unsupported",
        ),
        (
            "v58_effectful_filter.py",
            r#"from typing import List
def keep(value: int) -> bool:
    return value > 0
def run() -> None:
    source = [1]
    result = [x for x in source if keep(x)]  # type: List[int]
"#,
            "frontend.python.contracts.comprehension-filter-effect-unsupported",
        ),
        (
            "v58_effectful_mapper.py",
            r#"from typing import List
def map_value(value: int) -> int:
    return value + 1
def run() -> None:
    source = [1]
    result = [map_value(x) for x in source]  # type: List[int]
"#,
            "frontend.python.contracts.comprehension-mapper-effect-unsupported",
        ),
        (
            "v58_mutating_mapper.py",
            r#"from typing import List
def run() -> None:
    source = [1]
    result = [(saved := x) for x in source]  # type: List[int]
"#,
            "frontend.python.contracts.comprehension-mapper-effect-unsupported",
        ),
        (
            "v58_non_list_iterable.py",
            r#"from typing import List
def run(source: range) -> None:
    result = [x for x in source]  # type: List[int]
"#,
            "frontend.python.contracts.comprehension-iterable-type",
        ),
        (
            "v58_custom_iterable.py",
            r#"from typing import List
class Values:
    pass
def run(source: Values) -> None:
    result = [x for x in source]  # type: List[int]
"#,
            "frontend.python.contracts.type-unsupported",
        ),
        (
            "v58_refined_key.py",
            r#"from typing import Dict
class Key(int):
    pass
def run() -> None:
    source = [1]
    result = {Key(x): x for x in source}  # type: Dict[int, int]
"#,
            "frontend.python.contracts.comprehension-mapper-effect-unsupported",
        ),
        (
            "v58_wrong_result_type_comment.py",
            r#"from typing import List
def run() -> None:
    source = [1]
    result = [x for x in source]  # type: List[str]
"#,
            "frontend.python.contracts.type-mismatch",
        ),
        (
            "v58_heterogeneous_mapper.py",
            r#"from typing import List
def run(source: List[int]) -> None:
    result = [x if x > 0 else "negative" for x in source]  # type: List[int]
"#,
            "frontend.python.contracts.conditional-result-type",
        ),
    ];

    for (path, source, code) in cases {
        assert_refusal(source, path, code);
    }
}

#[test]
fn canonical_collection_helpers_cannot_be_shadowed() {
    for (helper, use_site) in [
        ("Acc", "Requires(Acc(list_pred(values)))"),
        ("ResultT", "Ensures(len(ResultT(List[int])) >= 0)"),
        ("list_pred", "Requires(list_pred(values))"),
        ("len", "assert len(values) >= 0"),
        ("Forall", "Ensures(Forall(int, lambda i: (i == i, [[i]])))"),
    ] {
        let source = format!(
            r#"from nagini_contracts.contracts import *
from typing import List

def run(values: List[int], {helper}: int) -> None:
    {use_site}
    result = [x for x in values]  # type: List[int]
"#
        );
        assert_refusal(
            &source,
            &format!("v58_shadowed_{helper}.py"),
            "frontend.python.contracts.canonical-helper-shadowed",
        );
    }
}

#[test]
fn async_comprehensions_fail_closed_through_the_public_frontend() {
    assert_refusal(
        r#"from typing import List
async def run(source: List[int]) -> None:
    result = [x async for x in source]
        "#,
        "v58_async_comprehension.py",
        "frontend.python.contracts.module-statement-unsupported",
    );
}

#[test]
fn comprehension_vc_rejects_binder_sort_confusion_and_capture() {
    let malformed_binder_sort = Term::ListComprehension {
        id: "bad-sort".to_owned(),
        source: Box::new(Term::List {
            element_sort: Sort::Int,
            values: vec![Term::Int { value: 1 }],
        }),
        binder: "b".to_owned(),
        element_sort: Sort::Bool,
        mapped: Box::new(Term::Variable {
            name: "b".to_owned(),
            sort: Sort::Bool,
        }),
        filter: None,
    };
    assert!(malformed_binder_sort.sort().is_err());

    let captured_binder = Term::ForAll {
        binder: "b".to_owned(),
        binder_sort: Sort::Int,
        body: Box::new(Term::ForAll {
            binder: "b".to_owned(),
            binder_sort: Sort::Int,
            body: Box::new(Term::Bool { value: true }),
        }),
    };
    assert!(captured_binder.sort().is_err());
}

#[test]
fn comprehension_vc_allows_distinct_nested_binders_and_outer_references() {
    let well_scoped = Term::ForAll {
        binder: "outer".to_owned(),
        binder_sort: Sort::Int,
        body: Box::new(Term::ForAll {
            binder: "inner".to_owned(),
            binder_sort: Sort::Int,
            body: Box::new(Term::Less {
                left: Box::new(Term::Variable {
                    name: "outer".to_owned(),
                    sort: Sort::Int,
                }),
                right: Box::new(Term::Variable {
                    name: "inner".to_owned(),
                    sort: Sort::Int,
                }),
            }),
        }),
    };

    assert_eq!(well_scoped.sort().unwrap(), Sort::Bool);
}

#[test]
fn comprehension_vc_refuses_unsupported_dictionary_key_sorts() {
    let malformed = Term::DictComprehension {
        id: "refined-key".to_owned(),
        source: Box::new(Term::List {
            element_sort: Sort::Int,
            values: vec![Term::Int { value: 1 }],
        }),
        binder: "b".to_owned(),
        key_sort: Sort::Reference,
        value_sort: Sort::Int,
        key: Box::new(Term::NullReference),
        value: Box::new(Term::Variable {
            name: "b".to_owned(),
            sort: Sort::Int,
        }),
        filter: None,
    };

    assert!(malformed.sort().is_err());
}

#[test]
fn scalar_conformance_matches_all_four_exact_upstream_comprehension_fixtures() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    for fixture in UPSTREAM_COMPREHENSION_FIXTURES {
        let result = check_pinned_scalar_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("scalar {fixture} was refused: {error}"));
        assert_eq!(result.schema, "maledictus-nagini-scalar-conformance/v2");
        assert_eq!(result.fixture, fixture);
        assert_eq!(result.expected, expected_fixture_diagnostics(fixture));
        assert_eq!(result.actual, result.expected, "{result:#?}");
        assert!(result.passed, "{result:#?}");
    }
}
