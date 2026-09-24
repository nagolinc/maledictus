use maledictus::python_reference_contracts::{
    parse_external_reference_contract_module, verify_and_export_source_reference_module,
    verify_reference_module, verify_reference_module_with_imports,
};

#[test]
fn exact_source_marker_class_equality_uses_reference_identity() {
    let source = r#"
from nagini_contracts.contracts import Assert, Requires
from typing import Optional

class Token:
    pass

def reflexive(value: Token, maybe: Optional[Token]) -> None:
    Assert(value == value)
    Assert(maybe == maybe)

def distinct(left: Token, right: Token) -> None:
    Requires(left is not right)
    Assert(left != right)
"#;
    let verification = verify_reference_module(source, "source_identity_equality.py", &[]).unwrap();
    assert!(verification.passed, "{verification:#?}");
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":assert:"))
            .count(),
        3
    );
}

#[test]
fn source_verified_equality_fact_composes_across_a_module_summary() {
    let (_, provider) = verify_and_export_source_reference_module(
        r#"
from nagini_contracts.contracts import Pure

class Token:
    pass

@Pure
def same(left: Token, right: Token) -> bool:
    return left == right
"#,
        "provider.py",
        "provider",
        &[],
    )
    .unwrap();
    let consumer = verify_reference_module_with_imports(
        r#"
from nagini_contracts.contracts import Ensures
from provider import Token, same

def reflexive(value: Token) -> None:
    Ensures(same(value, value))
"#,
        "consumer.py",
        &[],
        &[provider],
    )
    .unwrap();
    assert!(consumer.passed, "{consumer:#?}");
}

#[test]
fn mixed_or_external_reference_equality_remains_fail_closed() {
    let mixed = verify_reference_module(
        r#"
from nagini_contracts.contracts import Assert

class Left:
    pass

class Right:
    pass

def compare(left: Left, right: Right) -> None:
    Assert(left == right)
"#,
        "mixed_identity_equality.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        mixed.code,
        "frontend.python.references.equality-dispatch-unsupported"
    );

    let external = parse_external_reference_contract_module(
        r#"
from nagini_contracts.contracts import ContractOnly

class ExternalToken:
    pass

@ContractOnly
def identity(value: ExternalToken) -> ExternalToken:
    ...
"#,
        "external_contract.py",
        "external_provider",
    )
    .unwrap();
    let external_equality = verify_reference_module_with_imports(
        r#"
from nagini_contracts.contracts import Assert
from external_provider import ExternalToken

def compare(left: ExternalToken, right: ExternalToken) -> None:
    Assert(left == right)
"#,
        "external_consumer.py",
        &[],
        &[external],
    )
    .unwrap_err();
    assert_eq!(
        external_equality.code,
        "frontend.python.references.equality-dispatch-unsupported"
    );
}

#[test]
fn custom_python_equality_is_rejected_as_behavior_not_relabelled_as_identity() {
    let custom = verify_reference_module(
        r#"
from nagini_contracts.contracts import Assert

class CustomToken:
    def __eq__(self, other: object) -> bool:
        return True

def compare(left: CustomToken, right: CustomToken) -> None:
    Assert(left == right)
"#,
        "custom_equality.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(custom.code, "frontend.python.references.class-unsupported");
}
