use maledictus::python_contracts::verify_contract_module;

fn refuse(source: &str, path: &str) -> maledictus::python_contracts::ContractFailure {
    verify_contract_module(source, path, &[])
        .expect_err("source outside the scalar docstring fragment must be refused")
}

#[test]
fn leading_docstrings_are_inert_at_module_class_and_function_scope() {
    let source = r#""""scalar module documentation"""
from nagini_contracts.contracts import *

class Marker:
    """passive marker documentation"""

class Count(int):
    """scalar subclass documentation"""
    pass

class Failure(Exception):
    """exception documentation"""
    pass

def increment(value: int) -> int:
    """function documentation"""
    Requires(value >= 0)
    Ensures(Result() == value + 1)
    return value + 1
"#;

    let verification = verify_contract_module(source, "leading_docstrings.py", &[])
        .expect("leading string statements are legitimate inert docstrings");
    assert!(verification.passed, "{verification:#?}");
    assert_eq!(verification.functions, ["increment"]);
}

#[test]
fn nonleading_string_statements_are_not_treated_as_docstrings() {
    let module_verification = verify_contract_module(
        "from nagini_contracts.contracts import *\n\"not a module docstring\"\n",
        "late_module_string.py",
        &[],
    )
    .expect("a literal string expression is an inert module statement");
    assert!(module_verification.passed, "{module_verification:#?}");
    assert!(module_verification.functions.is_empty());

    let function_verification = verify_contract_module(
        "def run() -> None:\n    pass\n    \"not a function docstring\"\n",
        "late_function_string.py",
        &[],
    )
    .expect("a literal string expression is inert inside a function");
    assert!(function_verification.passed, "{function_verification:#?}");
    assert_eq!(function_verification.functions, ["run"]);

    let late_contract = refuse(
        "from nagini_contracts.contracts import *\n\ndef run(value: int) -> int:\n    Requires(value >= 0)\n    \"inert, but executable\"\n    Ensures(Result() == value)\n    return value\n",
        "late_contract_after_string.py",
    );
    assert_eq!(
        late_contract.code,
        "frontend.python.contracts.late-contract"
    );

    let class_failure = refuse(
        "class Marker:\n    pass\n    \"not a class docstring\"\n",
        "late_class_string.py",
    );
    assert_eq!(
        class_failure.code,
        "frontend.python.contracts.module-statement-unsupported"
    );
}

#[test]
fn arbitrary_expression_statements_remain_outside_the_scalar_fragment() {
    let module_failure = refuse("1\n", "module_expression.py");
    assert_eq!(
        module_failure.code,
        "frontend.python.contracts.module-statement-unsupported"
    );

    let function_failure = refuse("def run() -> None:\n    1\n", "function_expression.py");
    assert_eq!(
        function_failure.code,
        "frontend.python.contracts.statement-unsupported"
    );

    let class_failure = refuse("class Marker:\n    1\n", "class_expression.py");
    assert_eq!(
        class_failure.code,
        "frontend.python.contracts.module-statement-unsupported"
    );
}
