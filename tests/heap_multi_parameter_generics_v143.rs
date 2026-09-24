use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected multi-parameter Generic source to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refuse(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("ill-typed multi-parameter Generic source must fail closed")
}

fn assert_proved(verification: &HeapContractVerification) {
    assert!(verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

const PAIR_PREFIX: &str = r#"from typing import Generic, TypeVar
from nagini_contracts.contracts import *

Left = TypeVar('Left')
Right = TypeVar('Right')

class Pair(Generic[Left, Right]):
    def __init__(self, left: Left, right: Right) -> None:
        Ensures(Acc(self.left) and self.left == left)
        Ensures(Acc(self.right) and self.right == right)
        self.left: Left = left
        self.right: Right = right
"#;

#[test]
fn each_type_parameter_is_substituted_at_its_own_field_boundary() {
    let verification = verify(
        &format!(
            "{PAIR_PREFIX}\ndef run() -> None:\n    pair = Pair[int, bool](7, True)\n    Assert(pair.left == 7)\n    Assert(pair.right)\n"
        ),
        "multi_parameter_pair.py",
    );
    assert_proved(&verification);
}

#[test]
fn ordered_specialization_tuples_have_distinct_concrete_layouts() {
    let verification = verify(
        &format!(
            "{PAIR_PREFIX}\ndef run() -> None:\n    forward = Pair[int, bool](9, True)\n    reverse = Pair[bool, int](False, 4)\n    Assert(forward.left == 9)\n    Assert(forward.right)\n    Assert(not reverse.left)\n    Assert(reverse.right == 4)\n"
        ),
        "ordered_pair_specializations.py",
    );
    assert_proved(&verification);
}

#[test]
fn all_parameters_substitute_recursively_in_optional_and_tuple_annotations() {
    let verification = verify(
        r#"from typing import Generic, Optional, Tuple, TypeVar
from nagini_contracts.contracts import *

Left = TypeVar('Left')
Right = TypeVar('Right')

class Pair(Generic[Left, Right]):
    def __init__(self, left: Optional[Left], right: Optional[Right]) -> None:
        Ensures(Acc(self.left) and self.left is left)
        Ensures(Acc(self.right) and self.right is right)
        self.left: Optional[Left] = left
        self.right: Optional[Right] = right

    def values(self, left: Left, right: Right) -> Tuple[Left, Right]:
        return (left, right)

def run() -> None:
    pair = Pair[int, bool](3, False)
    values = pair.values(8, True)
    Assert(pair.left == 3)
    Assert(not pair.right)
    Assert(values[0] == 8)
    Assert(values[1])
"#,
        "nested_multi_parameter_annotations.py",
    );
    assert_proved(&verification);
}

#[test]
fn concrete_constructor_arguments_are_checked_against_every_substitution() {
    let failure = refuse(
        &format!(
            "{PAIR_PREFIX}\ndef run() -> None:\n    pair = Pair[int, bool]('not an int', 12)\n"
        ),
        "wrong_pair_constructor_arguments.py",
    );
    assert_eq!(
        failure.code, "frontend.python.heap.constructor-argument-type",
        "{failure:#?}"
    );
}

#[test]
fn concrete_method_arguments_use_the_complete_specialization_environment() {
    let source = format!(
        r#"{PAIR_PREFIX}
    def choose(self, left: Left, right: Right, take_left: bool) -> Left:
        if take_left:
            return left
        return self.left

def run() -> None:
    pair = Pair[int, bool](1, True)
    value = pair.choose('not an int', False, True)
"#
    );
    let failure = refuse(&source, "wrong_pair_method_argument.py");
    assert_eq!(
        failure.code, "frontend.python.heap.method-call-argument-type",
        "{failure:#?}"
    );
}

#[test]
fn specialization_arity_must_equal_declaration_arity() {
    for (name, use_site) in [
        ("missing", "Pair[int](1)"),
        ("extra", "Pair[int, bool, str](1, True, 'value')"),
    ] {
        let source = format!("{PAIR_PREFIX}\ndef run() -> None:\n    value = {use_site}\n");
        let failure = refuse(&source, &format!("{name}_generic_argument.py"));
        assert_eq!(
            failure.code, "frontend.python.heap.typevar-specialization-arity",
            "{failure:#?}"
        );
    }
}

#[test]
fn generic_parameter_lists_reject_duplicate_and_undeclared_typevars() {
    let duplicate = refuse(
        r#"from typing import Generic, TypeVar
T = TypeVar('T')
class Broken(Generic[T, T]):
    pass
def run() -> None:
    value = Broken[int, int]()
"#,
        "duplicate_generic_parameter.py",
    );
    assert_eq!(
        duplicate.code, "frontend.python.heap.typevar-generic-parameter-duplicate",
        "{duplicate:#?}"
    );

    let undeclared = refuse(
        r#"from typing import Generic, TypeVar
T = TypeVar('T')
class Broken(Generic[T, Missing]):
    pass
def run() -> None:
    value = Broken[int, bool]()
"#,
        "undeclared_generic_parameter.py",
    );
    assert_eq!(
        undeclared.code, "frontend.python.heap.typevar-generic-parameter-undeclared",
        "{undeclared:#?}"
    );
}

#[test]
fn generic_arity_is_structural_instead_of_limited_to_a_magic_maximum() {
    const ARITY: usize = 16;
    let typevars = (0..ARITY)
        .map(|index| format!("T{index}"))
        .collect::<Vec<_>>();
    let declarations = typevars
        .iter()
        .map(|name| format!("{name} = TypeVar('{name}')"))
        .collect::<Vec<_>>()
        .join("\n");
    let parameters = typevars.join(", ");
    let arguments = std::iter::repeat_n("int", ARITY)
        .collect::<Vec<_>>()
        .join(", ");
    let source = format!(
        "from typing import Generic, TypeVar\n{declarations}\nclass Wide(Generic[{parameters}]):\n    pass\ndef run() -> None:\n    value = Wide[{arguments}]()\n    assert isinstance(value, Wide)\n"
    );

    let verification = verify(&source, "structural_generic_arity.py");
    assert_proved(&verification);
}
