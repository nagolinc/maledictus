use std::fs;
use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};
use maledictus::python_contracts::verify_contract_module;
use maledictus::python_heap_contracts::verify_heap_module;

fn purity_violation_lines(source: &str, path: &str) -> Vec<u32> {
    let result = verify_contract_module(source, path, &[]).unwrap();
    result
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":purity-violation:"))
        .map(|obligation| obligation.line)
        .collect()
}

fn heap_purity_violation_lines(source: &str, path: &str, symbols: &[String]) -> Vec<u32> {
    let result = verify_heap_module(source, path, symbols).unwrap();
    result
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":purity-violation:"))
        .map(|obligation| obligation.line)
        .collect()
}

#[test]
fn direct_impure_calls_are_located_in_every_required_purity_context() {
    let cases = [
        (
            "def condition(value: int) -> bool:\n    return value > 0\ndef run(value: int) -> None:\n    while condition(value):\n        value = value - 1\n",
            4,
        ),
        (
            "from nagini_contracts.contracts import Pure\ndef ordinary(value: int) -> int:\n    return value\n@Pure\ndef run(value: int) -> int:\n    result = ordinary(value)\n    return result\n",
            6,
        ),
        (
            "from nagini_contracts.contracts import Ensures, Result\ndef ordinary(value: int) -> int:\n    return value\ndef run(value: int) -> int:\n    Ensures(Result() == ordinary(value))\n    return value\n",
            5,
        ),
    ];
    for (source, expected_line) in cases {
        assert_eq!(
            purity_violation_lines(source, "impure_context.py"),
            vec![expected_line]
        );
    }
}

#[test]
fn impure_calls_are_executed_before_ordinary_if_and_assert_statements() {
    let source = "from nagini_contracts.contracts import Assert\ndef condition(value: int) -> bool:\n    return value > 0\ndef observe(value: int) -> int:\n    return value\ndef run(value: int) -> None:\n    if condition(value):\n        value = value - 1\n    Assert(observe(value) >= 0)\n";
    assert!(
        purity_violation_lines(source, "impure_statement_contexts.py").is_empty(),
        "ordinary if and Assert statements sequence impure calls before consuming their results"
    );
}

#[test]
fn predicate_resources_are_not_mislabeled_as_impure_source_calls() {
    let source = "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        self.value = 1\n\n@Predicate\ndef ready(cell: Cell) -> bool:\n    return Acc(cell.value)\n\ndef resource_client() -> int:\n    cell = Cell()\n    Fold(ready(cell))\n    Unfold(ready(cell))\n    Fold(ready(cell))\n    return Unfolding(ready(cell), cell.value)\n";
    assert!(
        heap_purity_violation_lines(
            source,
            "predicate_resources.py",
            &["resource_client".to_owned()]
        )
        .is_empty(),
        "predicate assertions and Fold/Unfold resources are not impure executable calls"
    );
}

#[test]
fn predicate_resource_arguments_still_require_purity() {
    let source = "from nagini_contracts.contracts import Fold, Predicate, Unfold\ndef impure(value: int) -> int:\n    return value\n@Predicate\ndef ready(value: int) -> bool:\n    return value >= 0\ndef client(value: int) -> None:\n    Fold(ready(impure(value)))\n    Unfold(ready(impure(value)))\n";
    assert_eq!(
        heap_purity_violation_lines(
            source,
            "predicate_resource_arguments.py",
            &["client".to_owned()]
        ),
        vec![8, 9]
    );
}

#[test]
fn unfolding_checks_its_value_without_flagging_its_predicate_resource() {
    let source = "from nagini_contracts.contracts import Predicate, Pure, Unfolding\n@Predicate\ndef ready(value: int) -> bool:\n    return value >= 0\ndef impure(value: int) -> int:\n    return value\n@Pure\ndef client(value: int) -> int:\n    return Unfolding(ready(value), impure(value))\n";
    assert_eq!(
        heap_purity_violation_lines(source, "pure_unfolding_value.py", &["client".to_owned()]),
        vec![9]
    );
}

#[test]
fn pure_source_calls_remain_valid_in_conditions_and_pure_functions() {
    let source = "from nagini_contracts.contracts import Invariant, Pure\n@Pure\ndef condition(value: int) -> bool:\n    return value > 0\n@Pure\ndef relay(value: int) -> bool:\n    return condition(value)\ndef run(value: int) -> None:\n    while condition(value):\n        Invariant(True)\n        value = value - 1\n";
    assert!(
        purity_violation_lines(source, "pure_neighbors.py").is_empty(),
        "a proved Pure source call was classified as impure"
    );
}

#[test]
fn ordinary_call_statements_are_not_mislabeled_as_purity_violations() {
    let source = "def ordinary(value: int) -> int:\n    return value\ndef run(value: int) -> int:\n    result = ordinary(value)\n    return result\n";
    assert!(
        purity_violation_lines(source, "ordinary_runtime_call.py").is_empty(),
        "ordinary executable call was incorrectly placed in a purity-required context"
    );
}

#[test]
fn local_shadowing_does_not_inherit_a_source_functions_purity_effect() {
    let source = "from nagini_contracts.contracts import Pure\ndef callback() -> bool:\n    return True\n@Pure\ndef run(callback: bool) -> bool:\n    return callback\n";
    assert!(
        purity_violation_lines(source, "shadowed_function.py").is_empty(),
        "a parameter shadow inherited the module function's effect"
    );
}

#[test]
fn public_strict_issuance_refutes_an_impure_call_inside_pure_code() {
    let directory = tempfile::tempdir().unwrap();
    let source = "from nagini_contracts.contracts import Pure\ndef ordinary(value: int) -> int:\n    return value\n@Pure\ndef run(value: int) -> int:\n    return ordinary(value)\n";
    fs::write(directory.path().join("purity.py"), source).unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "purity.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains(":purity-violation:"))
    );
}

#[test]
fn heap_unfolding_value_preserves_the_impure_call_failure() {
    let source = "from nagini_contracts.contracts import Acc, Predicate, Unfolding\nfrom typing import Optional\nclass Cell:\n    def __init__(self) -> None:\n        self.val = None  # type: Optional[Cell]\n@Predicate\ndef P(c: Cell) -> bool:\n    return Acc(c.val)\ndef client(c: Cell) -> None:\n    a = Unfolding(P(c), get_val(c))\ndef get_val(c: Cell) -> int:\n    return 4\n";
    let verification =
        verify_heap_module(source, "unfolding_impure_value.py", &["client".to_owned()]).unwrap();

    assert!(!verification.passed);
    assert_eq!(verification.methods, vec!["client"]);
    let violations = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":purity-violation:"))
        .collect::<Vec<_>>();
    assert_eq!(violations.len(), 1);
    assert_eq!(violations[0].line, 10);
}

#[test]
fn exact_unfolding_purity_fixture_matches_through_the_heap_backend() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/translation/test_unfolding_3.py";
    let result = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap_or_else(|error| panic!("exact upstream fixture {fixture} was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual, "{result:#?}");
}
