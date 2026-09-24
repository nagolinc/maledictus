use maledictus::conformance::{ExpectedDiagnostic, check_heap_source};
use maledictus::python_heap_contracts::verify_heap_module;

fn diagnostic(code: &str, line: u32) -> ExpectedDiagnostic {
    ExpectedDiagnostic {
        code: code.to_owned(),
        line,
    }
}

#[test]
fn a_failed_assertion_is_assumed_for_the_remainder_of_its_success_path() {
    let source = r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

def run() -> None:
    Ensures(False)
    try:
        raise Failure()
    except Failure:
        #:: ExpectedOutput(assert.failed:assertion.false)
        Assert(False)
        Assert(False)
"#;

    let result = check_heap_source(source, "assert_path_semantics.py").unwrap();
    assert_eq!(
        result.actual,
        vec![diagnostic("assert.failed:assertion.false", 12)],
        "{result:#?}"
    );
    assert_eq!(result.expected, result.actual, "{result:#?}");
}

#[test]
fn an_undeclared_heap_exception_is_an_exhale_failure_at_the_function_boundary() {
    let source = r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

#:: ExpectedOutput(exhale.failed:assertion.false)
def run(flag: bool) -> None:
    if flag:
        raise Failure()
"#;

    let result = check_heap_source(source, "undeclared_heap_exception.py").unwrap();
    assert_eq!(
        result.actual,
        vec![diagnostic("exhale.failed:assertion.false", 7)],
        "{result:#?}"
    );
    assert_eq!(result.expected, result.actual, "{result:#?}");
}

#[test]
fn a_mixed_value_and_permission_precondition_reports_the_failing_value_part() {
    let source = r#"from nagini_contracts.contracts import *

class Cell:
    value: int

    def __init__(self) -> None:
        Ensures(Acc(self.value))
        self.value = 0

def require(cell: Cell) -> None:
    Requires(Acc(cell.value) and cell.value == 17)
    Ensures(Acc(cell.value))

def run() -> None:
    cell = Cell()
    #:: ExpectedOutput(call.precondition:assertion.false)
    require(cell)
"#;

    let verification = verify_heap_module(source, "mixed_precondition.py", &[])
        .unwrap_or_else(|failure| panic!("{}: {}", failure.code, failure.message));
    assert!(
        verification.obligations.iter().any(|obligation| {
            obligation.id.contains(":call-precondition:require:") && !obligation.satisfied()
        }),
        "{verification:#?}"
    );
    let result = check_heap_source(source, "mixed_precondition.py").unwrap();
    assert_eq!(
        result.actual,
        vec![diagnostic("call.precondition:assertion.false", 17)],
        "{result:#?}"
    );
    assert_eq!(result.expected, result.actual, "{result:#?}");
}
