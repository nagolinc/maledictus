use std::path::PathBuf;

use maledictus::conformance::{ExpectedDiagnostic, check_pinned_scalar_fixture};
use maledictus::python_contracts::verify_contract_module;

#[test]
fn scalar_conformance_matches_exact_source_order_global_definedness_fixture() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/verification/test_global_definedness_4.py";
    let result = check_pinned_scalar_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap_or_else(|error| panic!("scalar {fixture} was refused: {error}"));

    assert_eq!(
        result.expected,
        vec![ExpectedDiagnostic {
            code: "assert.failed:assertion.false".to_owned(),
            line: 22,
        }]
    );
    assert_eq!(result.actual, result.expected, "{result:#?}");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn transitive_calls_to_functions_defined_before_initialization_are_evaluated() {
    let source = r#"from nagini_contracts.contracts import *

def outer() -> int:
    return middle()

def middle() -> int:
    return inner()

def inner() -> int:
    return 12

VALUE = outer()

def prove_value() -> None:
    Assert(VALUE == 12)
"#;

    let verification = verify_contract_module(source, "defined_call_chain.py", &[])
        .expect("a completely defined initialization call graph must lower");

    assert!(verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains(":assert:") && obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn transitive_forward_call_is_a_refuted_initialization_obligation() {
    let source = r#"def outer() -> int:
    return middle()

def middle() -> int:
    return later()

BROKEN = outer()

def later() -> int:
    return 12
"#;

    let verification = verify_contract_module(source, "forward_call_chain.py", &[])
        .expect("a source-order NameError is a modeled failed execution, not a frontend refusal");

    assert!(!verification.passed, "{verification:#?}");
    let failures = verification
        .obligations
        .iter()
        .filter(|obligation| !obligation.satisfied())
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{verification:#?}");
    assert_eq!(failures[0].line, 7, "{verification:#?}");
    assert!(
        failures[0].id.starts_with("module:undefined-call:BROKEN"),
        "{verification:#?}"
    );
}

#[test]
fn a_forward_call_cannot_supply_a_later_global_value() {
    let source = r#"def outer() -> int:
    return later()

BROKEN = outer()
AFTER = 99

def later() -> int:
    return 12
"#;

    let verification = verify_contract_module(source, "halted_initialization.py", &[])
        .expect("the failing initialization must remain represented by an obligation");

    assert!(!verification.passed, "{verification:#?}");
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|obligation| !obligation.satisfied())
            .count(),
        1,
        "{verification:#?}"
    );
}

#[test]
fn function_defaults_are_checked_at_definition_time_not_at_the_later_call() {
    let source = r#"def choose(value: int = later()) -> int:
    return value

def later() -> int:
    return 12

VALUE = choose()
"#;

    let verification = verify_contract_module(source, "forward_default.py", &[])
        .expect("the definition-time NameError must be a modeled failed execution");

    assert!(!verification.passed, "{verification:#?}");
    let failures = verification
        .obligations
        .iter()
        .filter(|obligation| !obligation.satisfied())
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{verification:#?}");
    assert_eq!(failures[0].line, 1, "{verification:#?}");
    assert!(
        failures[0].id.starts_with("module:undefined-call:choose"),
        "{verification:#?}"
    );

    let defined_source = r#"from nagini_contracts.contracts import *

def default_value() -> int:
    return 7

def choose(value: int = default_value()) -> int:
    return value

VALUE = choose()

def prove_value() -> None:
    Assert(VALUE == 7)
"#;
    let defined = verify_contract_module(defined_source, "defined_default.py", &[])
        .expect("a default with a completely available call graph must lower");
    assert!(defined.passed, "{defined:#?}");
}
