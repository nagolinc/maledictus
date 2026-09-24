use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

#[test]
fn raised_constructor_call_binds_arguments_and_preserves_constructor_effects() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class ParameterizedFailure(Exception):
    code: int

    def __init__(self, code: int) -> None:
        Requires(code > 0)
        Ensures(Acc(self.code))
        Ensures(self.code == code)
        self.code = code

def run() -> None:
    try:
        raise ParameterizedFailure(52)
    except ParameterizedFailure as caught:
        Assert(caught.code == 52)
"#,
        "raise_parameterized_exception.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
    assert!(
        verification.obligations.iter().any(|obligation| {
            obligation
                .id
                .contains(":constructor-precondition:ParameterizedFailure:")
        }),
        "{verification:#?}"
    );
    assert!(
        verification
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains(":assert:")),
        "{verification:#?}"
    );
}
