use maledictus::conformance::check_scalar_source;
use maledictus::python_contracts::verify_contract_module;

fn refuse(source: &str) -> maledictus::python_contracts::ContractFailure {
    verify_contract_module(source, "class_island.py", &[])
        .expect_err("source must remain outside the scalar ownership boundary")
}

#[test]
fn independent_scalar_functions_can_coexist_with_unowned_class_declarations() {
    let verification = verify_contract_module(
        r#"from nagini_contracts.contracts import *

class Record:
    def __init__(self, value: int) -> None:
        self.value = value

    def effectful_method(self, value: int) -> int:
        print(value)
        return missing_runtime_value

def increment(value: int) -> int:
    Ensures(Result() == value + 1)
    return value + 1
"#,
        "independent_class_island.py",
        &[],
    )
    .expect("an inert class declaration must not block independent scalar verification");

    assert!(verification.passed, "{verification:#?}");
    assert_eq!(verification.functions, ["increment"]);
}

#[test]
fn scalar_dependencies_on_an_unowned_class_fail_closed() {
    let sources = [
        r#"class Record:
    def inspect(self) -> int:
        return 1

def run() -> int:
    return Record()
"#,
        r#"class Record:
    def inspect(self) -> int:
        return 1

def run(value: Record) -> int:
    return 1
"#,
        r#"class Record:
    def inspect(self) -> int:
        return 1

def run(value: int = Record()) -> int:
    return value
"#,
        r#"from nagini_contracts.contracts import *

class Record:
    def inspect(self) -> int:
        return 1

def run(value: object) -> int:
    Requires(isinstance(value, Record))
    return 1
"#,
        r#"class Record:
    def inspect(self) -> int:
        return 1

def helper() -> int:
    return Record()

def run() -> int:
    return helper()
"#,
    ];

    for source in sources {
        let error = refuse(source);
        assert_eq!(
            error.code, "frontend.python.contracts.class-declaration-island-dependency",
            "{error:#?}"
        );
    }
}

#[test]
fn declaration_time_class_effects_remain_unsupported() {
    let sources = [
        "class Base:\n    pass\nclass Record(Base):\n    def inspect(self) -> int:\n        return 1\ndef run() -> int:\n    return 1\n",
        "@decorated\nclass Record:\n    def inspect(self) -> int:\n        return 1\ndef run() -> int:\n    return 1\n",
        "class Record(metaclass=Meta):\n    def inspect(self) -> int:\n        return 1\ndef run() -> int:\n    return 1\n",
        "class Record:\n    value = make_value()\n    def inspect(self) -> int:\n        return 1\ndef run() -> int:\n    return 1\n",
        "class Record:\n    def inspect(self, value: int = make_value()) -> int:\n        return value\ndef run() -> int:\n    return 1\n",
        "class Record:\n    @staticmethod\n    def inspect() -> int:\n        return 1\ndef run() -> int:\n    return 1\n",
        "from typing import List\nclass Record:\n    def inspect(self, values: List[int]) -> int:\n        return 1\ndef run() -> int:\n    return 1\n",
    ];

    for source in sources {
        let error = refuse(source);
        assert_eq!(
            error.code, "frontend.python.contracts.module-statement-unsupported",
            "{error:#?}"
        );
    }
}

#[test]
fn class_island_names_cannot_be_rebound() {
    let error = refuse(
        "class Record:\n    def inspect(self) -> int:\n        return 1\nRecord = 1\ndef run() -> int:\n    return 1\n",
    );

    assert_eq!(
        error.code,
        "frontend.python.contracts.passive-class-binding-shadowed"
    );
}

#[test]
fn expected_diagnostics_inside_unowned_methods_are_not_silently_dropped() {
    for annotation in [
        "#:: ExpectedOutput(postcondition.violated:assertion.false)",
        "# ::   ExpectedOutput(carbon)(postcondition.violated:assertion.false)",
    ] {
        let source = format!(
            r#"class Record:
    def inspect(self) -> int:
        {annotation}
        return 1

def run() -> int:
    return 1
"#
        );
        let error = check_scalar_source(&source, "diagnostic_in_class_island.py").expect_err(
            "an expected diagnostic in an unowned method must defer the scalar frontend",
        );

        assert!(
            error.contains("class-declaration-island-diagnostic-unsupported"),
            "{error}"
        );
    }
}

#[test]
fn expected_output_lookalikes_inside_strings_are_not_annotations() {
    let verification = verify_contract_module(
        r##"class Record:
    "#:: ExpectedOutput(postcondition.violated:assertion.false)"

    def inspect(self) -> int:
        marker = "# :: ExpectedOutput(carbon)(assert.failed:assertion.false)"
        return 1

def run() -> int:
    return 1
"##,
        "class_annotation_lookalikes.py",
        &[],
    )
    .expect("the Python lexer must distinguish string contents from source annotations");

    assert!(verification.passed, "{verification:#?}");
    assert_eq!(verification.functions, ["run"]);
}

#[test]
fn class_only_modules_are_not_accepted_as_vacuous_scalar_proofs() {
    let error = refuse("class Record:\n    def inspect(self) -> int:\n        return 1\n");

    assert_eq!(
        error.code,
        "frontend.python.contracts.class-declaration-island-unowned"
    );
}

#[test]
fn canonical_adt_modules_remain_owned_by_the_adt_frontend() {
    let error = refuse(
        r#"from nagini_contracts.adt import ADT
from nagini_contracts.contracts import *

class Property:
    def __init__(self, value: int) -> None:
        self.value = value

def inspect(value: Property) -> int:
    return value.value
"#,
    );

    assert_eq!(
        error.code,
        "frontend.python.contracts.module-statement-unsupported"
    );
}
