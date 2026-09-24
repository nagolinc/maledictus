use std::path::PathBuf;

use maledictus::conformance::{
    ExpectedDiagnostic, check_pinned_heap_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_contracts::{ContractFailure, ContractVerification, verify_contract_module};
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn diagnostic(code: &str, line: u32) -> ExpectedDiagnostic {
    ExpectedDiagnostic {
        code: code.to_owned(),
        line,
    }
}

fn expected_fixture_diagnostics(fixture: &str) -> Vec<ExpectedDiagnostic> {
    let mut diagnostics = match fixture {
        "tests/functional/verification/test_varargs.py" => vec![
            diagnostic("call.precondition:assertion.false", 25),
            diagnostic("call.precondition:assertion.false", 30),
            diagnostic("call.precondition:assertion.false", 35),
            diagnostic("call.precondition:assertion.false", 40),
            diagnostic("call.precondition:assertion.false", 45),
            diagnostic("call.precondition:assertion.false", 50),
            diagnostic("postcondition.violated:assertion.false", 55),
        ],
        "tests/functional/verification/test_named_args.py" => vec![
            diagnostic("postcondition.violated:assertion.false", 62),
            diagnostic("postcondition.violated:assertion.false", 69),
            diagnostic("postcondition.violated:assertion.false", 77),
            diagnostic("postcondition.violated:assertion.false", 108),
            diagnostic("postcondition.violated:assertion.false", 116),
            diagnostic("postcondition.violated:assertion.false", 125),
        ],
        "tests/functional/verification/test_starred.py" => vec![
            diagnostic("call.precondition:assertion.false", 25),
            diagnostic("call.precondition:assertion.false", 30),
            diagnostic("call.precondition:assertion.false", 41),
            diagnostic("call.precondition:assertion.false", 48),
            diagnostic("call.precondition:assertion.false", 52),
        ],
        "tests/functional/verification/issues/00074.py" => vec![
            diagnostic("postcondition.violated:assertion.false", 13),
            diagnostic("postcondition.violated:assertion.false", 19),
        ],
        _ => panic!("missing exact expectation map for {fixture}"),
    };
    diagnostics.sort();
    diagnostics
}

fn verify_scalar(source: &str, path: &str) -> ContractVerification {
    verify_contract_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it was refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refuse_scalar(source: &str, path: &str) -> ContractFailure {
    verify_contract_module(source, path, &[])
        .expect_err("expected scalar source to be refused before proof issuance")
}

fn assert_scalar_refusal(source: &str, path: &str, expected_code: &str) {
    let failure = refuse_scalar(source, path);
    assert_eq!(failure.code, expected_code, "{failure:#?}");
}

fn verify_heap(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it was refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refuse_heap(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("expected heap source to be refused before proof issuance")
}

fn assert_heap_refusal(source: &str, path: &str, expected_code: &str) {
    let failure = refuse_heap(source, path);
    assert_eq!(failure.code, expected_code, "{failure:#?}");
}

fn assert_scalar_assertions_proved(verification: &ContractVerification, expected: usize) {
    assert!(verification.passed, "{verification:#?}");
    let assertions = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":assert:"))
        .collect::<Vec<_>>();
    assert_eq!(assertions.len(), expected, "{verification:#?}");
    assert!(
        assertions.iter().all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

fn assert_heap_assertions_proved(verification: &HeapContractVerification, expected: usize) {
    assert!(verification.passed, "{verification:#?}");
    let assertions = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":assert:"))
        .collect::<Vec<_>>();
    assert_eq!(assertions.len(), expected, "{verification:#?}");
    assert!(
        assertions.iter().all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn scalar_conformance_matches_exact_upstream_varargs_fixture() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/functional/verification/test_varargs.py";

    let result = check_pinned_scalar_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("scalar {fixture} was refused: {error}"));

    assert_eq!(result.schema, "maledictus-nagini-scalar-conformance/v2");
    assert_eq!(result.fixture, fixture);
    assert_eq!(result.expected, expected_fixture_diagnostics(fixture));
    assert_eq!(result.actual, result.expected, "{result:#?}");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn heap_conformance_matches_exact_upstream_named_starred_and_override_fixtures() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    for fixture in [
        "tests/functional/verification/test_named_args.py",
        "tests/functional/verification/test_starred.py",
        "tests/functional/verification/issues/00074.py",
    ] {
        let result = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("heap {fixture} was refused: {error}"));

        assert_eq!(result.schema, "maledictus-nagini-heap-conformance/v2");
        assert_eq!(result.fixture, fixture);
        assert_eq!(result.expected, expected_fixture_diagnostics(fixture));
        assert_eq!(result.actual, result.expected, "{result:#?}");
        assert!(result.passed, "{result:#?}");
    }
}

#[test]
fn named_arguments_bind_by_formal_name_and_defaults_fill_only_unassigned_slots() {
    let verification = verify_scalar(
        r#"from nagini_contracts.contracts import *

def encode(first: int, second: int = 7, *, offset: int = 11) -> int:
    return first * 100 + second * 10 + offset

def run() -> None:
    assert encode(2) == 281
    assert encode(second=3, first=1) == 141
    assert encode(2, offset=5) == 275
    assert encode(2, 3, offset=4) == 234
"#,
        "v59_named_defaults.py",
    );

    assert_scalar_assertions_proved(&verification, 4);
}

#[test]
fn required_keyword_only_arguments_bind_and_missing_ordinary_or_keyword_only_arguments_refuse() {
    let verification = verify_scalar(
        r#"from nagini_contracts.contracts import *

def encode(value: int, *, enabled: bool) -> int:
    return value if enabled else 0

def run() -> None:
    assert encode(enabled=True, value=17) == 17
    assert encode(17, enabled=False) == 0
"#,
        "v59_required_keyword_only.py",
    );
    assert_scalar_assertions_proved(&verification, 2);

    for (path, call) in [
        ("v59_missing_positional.py", "encode(enabled=True)"),
        ("v59_missing_keyword_only.py", "encode(17)"),
    ] {
        let source = format!(
            r#"def encode(value: int, *, enabled: bool) -> int:
    return value if enabled else 0

def run() -> int:
    return {call}
"#
        );
        assert_scalar_refusal(
            &source,
            path,
            "frontend.python.contracts.call-argument-missing",
        );
    }
}

#[test]
fn duplicate_keyword_syntax_and_positional_keyword_collisions_refuse_at_their_real_boundaries() {
    assert_scalar_refusal(
        r#"def select(value: int) -> int:
    return value

def run() -> int:
    return select(value=1, value=2)
"#,
        "v59_duplicate_keyword_syntax.py",
        "frontend.python.parse-error",
    );

    assert_scalar_refusal(
        r#"def select(value: int) -> int:
    return value

def run() -> int:
    return select(1, value=2)
"#,
        "v59_positional_keyword_collision.py",
        "frontend.python.contracts.call-argument-duplicate",
    );
}

#[test]
fn unexpected_keywords_refuse_unless_a_real_kwargs_formal_captures_them() {
    assert_scalar_refusal(
        r#"def select(value: int) -> int:
    return value

def run() -> int:
    return select(value=1, extra=2)
"#,
        "v59_unexpected_keyword.py",
        "frontend.python.contracts.call-keyword-unexpected",
    );

    let verification = verify_scalar(
        r#"from nagini_contracts.contracts import *

def select(value: int, **named: int) -> int:
    Requires(len(named) == 2)
    Requires('left' in named and named['left'] == 3)
    Requires('right' in named and named['right'] == 4)
    return value + named['left'] + named['right']

def run() -> None:
    assert select(2, right=4, left=3) == 9
"#,
        "v59_kwargs_capture.py",
    );
    assert_scalar_assertions_proved(&verification, 1);
}

#[test]
fn fixed_tuple_stars_expand_in_place_and_repeated_stars_preserve_order() {
    let verification = verify_scalar(
        r#"from nagini_contracts.contracts import *
from typing import Tuple

def encode(first: int, second: int, third: int, fourth: int) -> int:
    return first * 1000 + second * 100 + third * 10 + fourth

def through_parameter(middle: Tuple[int, int]) -> int:
    return encode(1, *middle, 4)

def run() -> None:
    first = (1, 2)
    second = (3, 4)
    assert encode(*first, *second) == 1234
    assert encode(*(1,), 2, *(3,), 4) == 1234
    assert through_parameter((2, 3)) == 1234
"#,
        "v59_fixed_tuple_star_order.py",
    );

    assert_scalar_assertions_proved(&verification, 3);
}

#[test]
fn unknown_length_star_iterables_and_dynamic_keyword_mappings_refuse() {
    assert_scalar_refusal(
        r#"from typing import List

def select(value: int) -> int:
    return value

def run(values: List[int]) -> int:
    return select(*values)
"#,
        "v59_dynamic_star.py",
        "frontend.python.contracts.call-star-dynamic-unsupported",
    );

    assert_scalar_refusal(
        r#"from typing import Dict

def select(value: int) -> int:
    return value

def run(values: Dict[str, int]) -> int:
    return select(**values)
"#,
        "v59_dynamic_keyword_star.py",
        "frontend.python.contracts.call-keyword-star-dynamic-unsupported",
    );
}

#[test]
fn argument_expressions_are_evaluated_once_in_python_left_to_right_order() {
    let verification = verify_heap(
        r#"from nagini_contracts.contracts import *

class Counter:
    value: int

    def __init__(self) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == 0)
        self.value = 0

    def take_first(self) -> int:
        Requires(Acc(self.value))
        Requires(self.value == 0)
        Ensures(Acc(self.value))
        Ensures(self.value == 1)
        Ensures(Result() == 1)
        self.value = 1
        return 1

    def take_second(self) -> int:
        Requires(Acc(self.value))
        Requires(self.value == 1)
        Ensures(Acc(self.value))
        Ensures(self.value == 2)
        Ensures(Result() == 2)
        self.value = 2
        return 2

    def take_third(self) -> int:
        Requires(Acc(self.value))
        Requires(self.value == 2)
        Ensures(Acc(self.value))
        Ensures(self.value == 3)
        Ensures(Result() == 3)
        self.value = 3
        return 3

def encode(first: int, second: int, *, third: int) -> int:
    return first * 100 + second * 10 + third

def run() -> None:
    counter = Counter()
    result = encode(counter.take_first(), second=counter.take_second(), third=counter.take_third())
    Assert(result == 123)
    Assert(counter.value == 3)
    counter.value = 0
    read_before_effect = encode(counter.value, second=counter.take_first(), third=counter.take_second())
    Assert(read_before_effect == 12)
    Assert(counter.value == 2)
"#,
        "v59_argument_effect_order.py",
    );

    assert_heap_assertions_proved(&verification, 4);
}

#[test]
fn bound_and_unbound_method_calls_inject_exactly_one_receiver_before_binding() {
    let verification = verify_heap(
        r#"from nagini_contracts.contracts import *

class Scale:
    factor: int

    def __init__(self) -> None:
        Ensures(Acc(self.factor))
        Ensures(self.factor == 100)
        self.factor = 100

    def encode(self, first: int, second: int = 7, *, offset: int = 1) -> int:
        Requires(Acc(self.factor))
        Ensures(Acc(self.factor))
        Ensures(Result() == self.factor + first * 10 + second + offset)
        return self.factor + first * 10 + second + offset

def run() -> None:
    scale = Scale()
    first = scale.encode(2)
    second = scale.encode(first=2, second=3, offset=4)
    third = Scale.encode(scale, 2, second=3, offset=4)
    Assert(first == 128)
    Assert(second == 127)
    Assert(third == 127)
"#,
        "v59_receiver_binding.py",
    );

    assert_heap_assertions_proved(&verification, 3);
}

#[test]
fn direct_method_statements_use_named_arguments_and_definition_defaults() {
    let verification = verify_heap(
        r#"from nagini_contracts.contracts import *

class Target:
    first: int
    second: int

    def __init__(self) -> None:
        Ensures(Acc(self.first))
        Ensures(Acc(self.second))
        self.first = 0
        self.second = 0

    def set_pair(self, first: int, second: int = 7) -> None:
        Requires(Acc(self.first))
        Requires(Acc(self.second))
        Ensures(Acc(self.first))
        Ensures(Acc(self.second))
        Ensures(self.first == first)
        Ensures(self.second == second)
        self.first = first
        self.second = second

def run() -> None:
    target = Target()
    target.set_pair(second=3, first=1)
    Assert(target.first == 1)
    Assert(target.second == 3)
    target.set_pair(2)
    Assert(target.first == 2)
    Assert(target.second == 7)
"#,
        "v59_method_statement_named_defaults.py",
    );

    assert_heap_assertions_proved(&verification, 4);
}

#[test]
fn method_binding_preserves_optional_reference_types() {
    let common = r#"from typing import Optional
from nagini_contracts.contracts import *

class Item:
    marker: int

class Holder:
    selected: Optional[Item]

class Target:
    def accept_required(self, value: Item) -> None:
        pass

    def accept_optional(self, value: Optional[Item]) -> None:
        pass
"#;

    for (path, call) in [
        (
            "v59_optional_positional_to_required.py",
            "target.accept_required(holder.selected)",
        ),
        (
            "v59_optional_named_to_required.py",
            "target.accept_required(value=holder.selected)",
        ),
    ] {
        let source = format!(
            "{common}\ndef run(target: Target, holder: Holder) -> None:\n    Requires(Acc(holder.selected))\n    {call}\n"
        );
        assert_heap_refusal(
            &source,
            path,
            "frontend.python.heap.method-call-argument-type",
        );
    }

    let verification = verify_heap(
        &format!(
            "{common}\ndef run(target: Target, holder: Holder, item: Item) -> None:\n    Requires(Acc(holder.selected))\n    target.accept_optional(item)\n    target.accept_optional(value=holder.selected)\n"
        ),
        "v59_optional_formal_acceptance.py",
    );
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn scalar_and_heap_call_arguments_are_checked_after_canonical_binding() {
    assert_scalar_refusal(
        r#"def consume(value: int) -> int:
    return value

def run() -> int:
    return consume(value='wrong')
"#,
        "v59_scalar_keyword_type_mismatch.py",
        "frontend.python.contracts.type-mismatch",
    );

    assert_heap_refusal(
        r#"class Item:
    pass

def consume(value: int) -> int:
    return value

def run() -> int:
    item = Item()
    return consume(value=item)
"#,
        "v59_heap_keyword_type_mismatch.py",
        "frontend.python.heap.function-call-argument-type-mismatch",
    );
}

#[test]
fn heap_binding_failures_use_the_heap_frontend_namespace() {
    assert_heap_refusal(
        r#"def select(value: int, *, flag: bool) -> int:
    return value if flag else 0

def run() -> int:
    return select(flag=True)
"#,
        "v59_heap_missing_argument.py",
        "frontend.python.heap.call-argument-missing",
    );

    assert_heap_refusal(
        r#"def select(value: int) -> int:
    return value

def run() -> int:
    return select(1, value=2)
"#,
        "v59_heap_duplicate_argument.py",
        "frontend.python.heap.call-argument-duplicate",
    );

    assert_heap_refusal(
        r#"def select(value: int) -> int:
    return value

def run() -> int:
    return select(value=1, extra=2)
"#,
        "v59_heap_unexpected_keyword.py",
        "frontend.python.heap.call-keyword-unexpected",
    );
}
