use maledictus::python_contracts::{ContractFailure, verify_contract_module};
use maledictus::vc::ObligationStatus;

fn verify(source: &str, path: &str) -> maledictus::python_contracts::ContractVerification {
    verify_contract_module(source, path, &[]).expect("fixture should lower")
}

fn refuse(source: &str, path: &str) -> ContractFailure {
    verify_contract_module(source, path, &[]).expect_err("fixture must fail closed")
}

#[test]
fn proves_symbolic_immutable_list_iteration_and_nested_loops() {
    let result = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def test1(a: List[int]) -> None:
    Requires(Acc(list_pred(a)))
    Ensures(Acc(list_pred(a)))
    for i in a:
        pass

def test2() -> None:
    a = [1, 2, 3]
    for i in a:
        pass
    Assert(Acc(list_pred(a)))

def test3() -> None:
    a = [1, 2, 3]
    b = [1, 2, 3]
    for i in a:
        Invariant(Acc(list_pred(b)))
        for j in b:
            pass

def test4(a: List[int], b: List[int]) -> None:
    Requires(Acc(list_pred(a)))
    Requires(Acc(list_pred(b)))
    for i in a:
        Invariant(Acc(list_pred(b)))
        for j in b:
            pass
"#,
        "tests/functional/verification/issues/00059.py",
    );
    assert!(result.passed, "{:#?}", result.obligations);
    assert!(result.obligations.iter().any(|obligation| {
        obligation.id.contains(":invariant-establishment:") && obligation.satisfied()
    }));
    assert!(result.obligations.iter().any(|obligation| {
        obligation.id.contains(":invariant-preservation:") && obligation.satisfied()
    }));
}

#[test]
fn proves_establishment_preservation_and_natural_exit_invariant() {
    let result = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def count(values: List[int]) -> None:
    result = 0
    for value in values:
        Invariant(result >= 0)
        result += 1
    assert result >= 0
"#,
        "symbolic_for_invariant.py",
    );
    assert!(result.passed, "{:#?}", result.obligations);
}

#[test]
fn refutes_unestablished_or_unpreserved_invariants() {
    let establishment = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def broken(values: List[int]) -> None:
    count = 0
    for value in values:
        Invariant(count > 0)
        pass
"#,
        "symbolic_for_establishment.py",
    );
    assert!(!establishment.passed);
    assert!(establishment.obligations.iter().any(|obligation| {
        obligation.id.contains(":invariant-establishment:")
            && obligation.status == ObligationStatus::Refuted
    }));

    let preservation = verify(
        r#"from nagini_contracts.contracts import *
from typing import List

def broken(values: List[int]) -> None:
    count = 0
    for value in values:
        Invariant(count >= 0)
        count -= 1
"#,
        "symbolic_for_preservation.py",
    );
    assert!(!preservation.passed);
    assert!(preservation.obligations.iter().any(|obligation| {
        obligation.id.contains(":invariant-preservation:")
            && obligation.status == ObligationStatus::Refuted
    }));
}

#[test]
fn refuses_iterable_alias_escape_and_rebinding() {
    let escaped = refuse(
        r#"from typing import List

def retain(values: List[int]) -> None:
    pass

def broken(values: List[int]) -> None:
    for value in values:
        retain(values)
"#,
        "symbolic_for_escape.py",
    );
    assert_eq!(
        escaped.code,
        "frontend.python.contracts.symbolic-for-iterable-alias-escape"
    );

    let rebound = refuse(
        r#"from typing import List

def broken(values: List[int]) -> None:
    for value in values:
        values = []
"#,
        "symbolic_for_rebind.py",
    );
    assert!(matches!(
        rebound.code,
        "frontend.python.contracts.symbolic-for-iterable-alias-escape"
            | "frontend.python.contracts.symbolic-for-iterable-mutation-unsupported"
    ));

    let mutated = refuse(
        r#"from typing import List

def broken(values: List[int]) -> None:
    for value in values:
        values.append(1)
"#,
        "symbolic_for_mutation.py",
    );
    assert_eq!(
        mutated.code,
        "frontend.python.contracts.statement-unsupported"
    );
}

#[test]
fn refuses_abrupt_and_exceptional_symbolic_loop_bodies() {
    for source in [
        "from typing import List\n\ndef broken(values: List[int]) -> None:\n    for value in values:\n        break\n",
        "from typing import List\n\ndef broken(values: List[int]) -> None:\n    for value in values:\n        continue\n",
        "from typing import List\n\ndef broken(values: List[int]) -> int:\n    for value in values:\n        return value\n    return 0\n",
    ] {
        let error = refuse(source, "symbolic_for_abrupt.py");
        assert!(matches!(
            error.code,
            "frontend.python.contracts.statement-unsupported"
                | "frontend.python.contracts.symbolic-for-abrupt-completion-unsupported"
        ));
    }

    let raised = refuse(
        "from typing import List\n\ndef broken(values: List[int]) -> None:\n    for value in values:\n        raise ValueError\n",
        "symbolic_for_raise.py",
    );
    assert_eq!(
        raised.code,
        "frontend.python.contracts.symbolic-for-body-exception-unsupported"
    );
}

#[test]
fn post_loop_target_read_from_possibly_empty_list_fails_closed() {
    let result = verify(
        r#"from typing import List

def broken(values: List[int]) -> int:
    for value in values:
        pass
    return value
"#,
        "symbolic_for_target_after.py",
    );
    assert!(!result.passed);
    assert!(result.obligations.iter().any(|obligation| {
        obligation.id.contains(":undefined-local:value:")
            && obligation.status == ObligationStatus::Refuted
    }));
}

#[test]
fn previous_requires_a_loop_history_model() {
    let error = refuse(
        r#"from nagini_contracts.contracts import *
from typing import List

def broken(values: List[int]) -> None:
    for value in values:
        Invariant(Previous(value) == value)
        pass
"#,
        "symbolic_for_previous.py",
    );
    assert!(matches!(
        error.code,
        "frontend.python.contracts.expression-unsupported"
            | "frontend.python.contracts.symbolic-for-previous-unsupported"
    ));
}
