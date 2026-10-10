use maledictus::python_heap_contracts::{
    parse_external_heap_contract_module, verify_heap_module, verify_heap_module_with_imports,
};

fn contract(annotation: &str, default: &str) -> String {
    format!(
        "from nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Result\n\nclass Counter:\n    @ContractOnly\n    def __init__(self) -> None:\n        ...\n\n    @ContractOnly\n    def sample(self, value: {annotation} = {default}) -> {annotation}:\n        Ensures(Result() == value)\n        Exsures(Exception, True)\n        ...\n"
    )
}

fn verify_binding(annotation: &str, default: &str, arguments: &str, expected: &str) -> bool {
    let provider = parse_external_heap_contract_module(
        &contract(annotation, default),
        "counter_contract.py",
        "native_counter",
    )
    .unwrap();
    let source = format!(
        "from native_counter import Counter\n\ndef work() -> Counter:\n    counter = Counter()\n    try:\n        value = counter.sample({arguments})\n    except Exception:\n        return counter\n    assert value == {expected}\n    return counter\n"
    );
    verify_heap_module_with_imports(&source, "worker.py", &["work".to_owned()], &[provider])
        .unwrap()
        .passed
}

#[test]
fn signed_integer_defaults_reach_the_real_method_contract() {
    for literal in [
        "-1",
        "+1",
        "-0",
        "+0",
        "-9223372036854775808",
        "+9223372036854775807",
    ] {
        assert!(verify_binding("int", literal, "", literal), "{literal}");
    }
    assert!(!verify_binding("int", "-1", "", "1"));
    assert!(!verify_binding("int", "+1", "", "-1"));
}

#[test]
fn explicit_positional_and_keyword_arguments_override_the_signed_default() {
    assert!(verify_binding("int", "-1", "7", "7"));
    assert!(verify_binding("int", "-1", "value=9", "9"));
    assert!(verify_binding("int", "-1", "-2", "-2"));
    assert!(!verify_binding("int", "-1", "7", "-1"));
}

#[test]
fn signed_defaults_do_not_enable_arbitrary_expressions() {
    for expression in ["1 - 2", "abs(-1)", "--1", "-(1 + 2)"] {
        let error = parse_external_heap_contract_module(
            &contract("int", expression),
            "counter_contract.py",
            "native_counter",
        )
        .unwrap_err();
        assert_eq!(
            error.code, "frontend.python.heap.method-default-unsupported",
            "{expression}: {error:#?}"
        );
    }
}

#[test]
fn boolean_defaults_and_mismatched_signed_values_remain_distinct() {
    assert!(verify_binding("bool", "True", "", "True"));
    assert!(verify_binding("bool", "False", "", "False"));
    for (annotation, literal) in [
        ("int", "True"),
        ("int", "-True"),
        ("int", "+False"),
        ("bool", "-1"),
        ("str", "+1"),
        ("int", "-1.5"),
    ] {
        let error = parse_external_heap_contract_module(
            &contract(annotation, literal),
            "counter_contract.py",
            "native_counter",
        )
        .unwrap_err();
        assert_eq!(
            error.code, "frontend.python.heap.method-default-type-mismatch",
            "{annotation}={literal}: {error:#?}"
        );
    }
}

#[test]
fn signed_literals_outside_the_existing_integer_representation_are_refused() {
    for literal in [
        "-9223372036854775809",
        "+9223372036854775808",
        "-170141183460469231731687303715884105729",
    ] {
        let error = parse_external_heap_contract_module(
            &contract("int", literal),
            "counter_contract.py",
            "native_counter",
        )
        .unwrap_err();
        assert_eq!(
            error.code, "frontend.python.heap.method-default-out-of-range",
            "{literal}: {error:#?}"
        );
    }
}

#[test]
fn existing_negative_sequence_indexing_keeps_its_value() {
    let source = "from nagini_contracts.contracts import Ensures, Result\n\ndef work() -> int:\n    Ensures(Result() == 8)\n    values: tuple[int, int] = (4, 8)\n    return values[-1]\n";
    let result = verify_heap_module(source, "worker.py", &["work".to_owned()]).unwrap();
    assert!(result.passed, "{result:#?}");
}
