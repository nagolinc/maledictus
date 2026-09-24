use std::path::PathBuf;

use maledictus::conformance::{ExpectedDiagnostic, check_pinned_scalar_fixture};
use maledictus::python_contracts::verify_contract_module;

#[test]
fn exact_upstream_conditional_definedness_fixture_matches_nagini() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/verification/issues/00252.py";
    let result = check_pinned_scalar_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap_or_else(|error| panic!("scalar {fixture} was refused: {error}"));

    assert_eq!(
        result.expected,
        vec![ExpectedDiagnostic {
            code: "expression.undefined:undefined.local.variable".to_owned(),
            line: 37,
        }]
    );
    assert_eq!(result.actual, result.expected, "{result:#?}");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn exact_upstream_exceptional_branch_definedness_fixture_matches_nagini() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/verification/issues/00053.py";
    let result = check_pinned_scalar_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap_or_else(|error| panic!("scalar {fixture} was refused: {error}"));

    assert_eq!(
        result.expected,
        vec![ExpectedDiagnostic {
            code: "expression.undefined:undefined.local.variable".to_owned(),
            line: 20,
        }]
    );
    assert_eq!(result.actual, result.expected, "{result:#?}");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn branch_local_reads_are_checked_on_each_symbolic_path() {
    let source = r#"from nagini_contracts.contracts import *

def both(flag: bool) -> int:
    if flag:
        selected = 1
    else:
        selected = 2
    return selected

def missing(flag: bool) -> int:
    if flag:
        selected = 1
    return selected
"#;

    let verification = verify_contract_module(source, "conditional_definedness.py", &[])
        .expect("undefined locals are semantic proof failures, not frontend refusals");
    let undefined = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":undefined-local:selected:"))
        .collect::<Vec<_>>();
    assert_eq!(undefined.len(), 1, "{verification:#?}");
    assert!(!undefined[0].satisfied(), "{verification:#?}");
    assert!(!verification.passed, "{verification:#?}");
}

#[test]
fn a_precondition_can_prove_the_missing_branch_unreachable() {
    let source = r#"from nagini_contracts.contracts import *

def selected(value: int) -> int:
    Requires(value > 0)
    if value > 0:
        result = 1
    return result
"#;

    let verification = verify_contract_module(source, "unreachable_undefined_local.py", &[])
        .expect("the path-sensitive definedness condition should lower");
    let obligation = verification
        .obligations
        .iter()
        .find(|obligation| obligation.id.contains(":undefined-local:result:"))
        .expect("the unreachable syntactic path remains explicit evidence");
    assert!(obligation.satisfied(), "{verification:#?}");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn python_function_scope_applies_even_before_the_assignment_statement() {
    let source = r#"def read_before_assignment() -> int:
    return value
    value = 1
"#;

    let verification = verify_contract_module(source, "read_before_assignment.py", &[])
        .expect("an unbound local is a modeled runtime failure");
    assert!(!verification.passed, "{verification:#?}");
    assert!(verification.obligations.iter().any(|obligation| {
        obligation.id.contains(":undefined-local:value:") && !obligation.satisfied()
    }));
}

#[test]
fn an_unknown_global_name_is_not_reclassified_as_a_local_definedness_failure() {
    let failure = verify_contract_module(
        "def typo() -> int:\n    return never_declared\n",
        "unknown_global.py",
        &[],
    )
    .expect_err("an unresolved nonlocal name remains outside this feature");
    assert_eq!(failure.code, "frontend.python.name.unresolved");
}

#[test]
fn guarded_conditional_expression_reads_remain_fail_closed() {
    let failure = verify_contract_module(
        r#"def choose(flag: bool) -> int:
    return missing if flag else 1
    missing = 2
"#,
        "guarded_undefined_local.py",
        &[],
    )
    .expect_err("guarded definedness needs a separate expression-path rule");
    assert_eq!(failure.code, "frontend.python.name.unresolved");
}
