use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};
use maledictus::vc::ObligationStatus;

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refuse(source: &str) -> ContractFailure {
    verify_heap_module(source, "invalid_pure_nominal_result.py", &[])
        .expect_err("invalid pure nominal result composition must fail closed")
}

const VALID_CHAIN: &str = r#"from nagini_contracts.contracts import *

class Leaf:
    pass

class Holder:
    leaf: Leaf

    @Pure
    def build(self) -> Leaf:
        Requires(Acc(self.leaf))
        return self.leaf

    @Pure
    def get(self) -> Leaf:
        Requires(Acc(self.leaf))
        return self.build()
"#;

#[test]
fn verified_pure_method_results_compose_nominal_identity_and_nonnullness() {
    let result = verify(
        &format!(
            "{VALID_CHAIN}\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.leaf))\n    value = holder.get()\n    Assert(isinstance(value, Leaf))\n"
        ),
        "valid_pure_nominal_result.py",
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
fn composed_nominal_result_does_not_prove_an_unrelated_runtime_type() {
    let result = verify(
        &format!(
            "{VALID_CHAIN}\nclass Other:\n    pass\n\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.leaf))\n    value = holder.get()\n    Assert(isinstance(value, Other))\n"
        ),
        "false_pure_nominal_result.py",
    );
    assert!(!result.passed, "{result:#?}");
    assert!(
        result.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:")
                && obligation.status == ObligationStatus::Refuted
        }),
        "{result:#?}"
    );
}

#[test]
fn optional_nested_pure_results_cannot_be_promoted_to_nonoptional() {
    let failure = refuse(
        r#"from typing import Optional
from nagini_contracts.contracts import *

class Leaf:
    pass

class Holder:
    leaf: Optional[Leaf]

    @Pure
    def build(self) -> Optional[Leaf]:
        Requires(Acc(self.leaf))
        return self.leaf

    @Pure
    def get(self) -> Leaf:
        Requires(Acc(self.leaf))
        return self.build()  # type: ignore
"#,
    );
    assert_eq!(
        failure.code, "frontend.python.heap.return-nominal-type-optional",
        "{failure:#?}"
    );
}
