use std::num::NonZeroI128;

use maledictus::python_contracts::verify_contract_module;
use maledictus::solver::discharge;
use maledictus::vc::{Obligation, ObligationExpectation, ObligationStatus, Sort, SortError, Term};

fn obligation(id: &str, assumptions: Vec<Term>, conclusion: Term) -> Obligation {
    Obligation {
        id: id.to_owned(),
        expectation: ObligationExpectation::Prove,
        assumptions,
        conclusion,
        path: "variadic_tuple_v118.vc".to_owned(),
        byte_offset: 0,
        line: 1,
        column: 1,
    }
}

fn integer_tuple(name: &str) -> Term {
    Term::Variable {
        name: name.to_owned(),
        sort: Sort::VariadicTuple(Box::new(Sort::Int)),
    }
}

#[test]
fn vc_preserves_variadic_tuple_sort_and_rejects_heterogeneous_values() {
    let tuple = Term::VariadicTuple {
        element_sort: Sort::Int,
        values: vec![Term::Int { value: 1 }, Term::Int { value: 2 }],
    };
    assert_eq!(
        tuple.sort_typed(),
        Ok(Sort::VariadicTuple(Box::new(Sort::Int)))
    );
    assert_eq!(
        Term::VariadicTuple {
            element_sort: Sort::Int,
            values: vec![Term::Bool { value: true }],
        }
        .sort_typed(),
        Err(SortError::VariadicTupleElementSortMismatch {
            expected: Sort::Int,
            actual: Sort::Bool,
        })
    );
    assert_ne!(
        Sort::VariadicTuple(Box::new(Sort::Int)),
        Sort::List(Box::new(Sort::Int))
    );
    assert_ne!(
        Sort::VariadicTuple(Box::new(Sort::Int)),
        Sort::Tuple(vec![Sort::Int])
    );
    assert_eq!(
        Term::VariadicTuple {
            element_sort: Sort::Unit,
            values: Vec::new(),
        }
        .sort_typed(),
        Err(SortError::VariadicTupleElementSortUnsupported { sort: Sort::Unit })
    );
    assert_eq!(
        Term::VariadicTupleGet {
            tuple: Box::new(Term::List {
                element_sort: Sort::Int,
                values: Vec::new(),
            }),
            index: Box::new(Term::Int { value: 0 }),
        }
        .sort_typed(),
        Err(SortError::VariadicTupleOperandRequiredForIndex)
    );
}

#[test]
fn z3_proves_symbolic_length_index_and_static_slice_relations() {
    let values = integer_tuple("values");
    let length = Term::VariadicTupleLength {
        value: Box::new(values.clone()),
    };
    let first = Term::VariadicTupleGet {
        tuple: Box::new(values.clone()),
        index: Box::new(Term::Int { value: 0 }),
    };
    let first_is_seven = Term::Equal {
        left: Box::new(first),
        right: Box::new(Term::Int { value: 7 }),
    };
    let reuse = discharge(&obligation(
        "variadic-tuple-index",
        vec![
            Term::Greater {
                left: Box::new(length.clone()),
                right: Box::new(Term::Int { value: 0 }),
            },
            first_is_seven.clone(),
        ],
        first_is_seven,
    ))
    .expect("variadic tuple indexing must lower");
    assert_eq!(reuse.status, ObligationStatus::Proved);

    let reversed = Term::VariadicTupleSlice {
        source: Box::new(values),
        lower: None,
        upper: None,
        step: NonZeroI128::new(-1).expect("-1 is nonzero"),
    };
    let reverse_length = discharge(&obligation(
        "variadic-tuple-reverse-length",
        Vec::new(),
        Term::Equal {
            left: Box::new(Term::VariadicTupleLength {
                value: Box::new(reversed),
            }),
            right: Box::new(length),
        },
    ))
    .expect("variadic tuple slicing must lower");
    assert_eq!(reverse_length.status, ObligationStatus::Proved);
}

#[test]
fn scalar_frontend_verifies_variadic_tuple_literals_indexing_slicing_and_iteration() {
    let source = r#"from nagini_contracts.contracts import *
from typing import Tuple

def literal() -> Tuple[int, ...]:
    Ensures(len(Result()) == 3)
    Ensures(Result()[0] == 1)
    return (1, 2, 3)

def indexed(values: Tuple[int, ...], index: int) -> int:
    Requires(0 <= index and index < len(values))
    Ensures(Result() == values[index])
    return values[index]

def reversed_values(values: Tuple[int, ...]) -> Tuple[int, ...]:
    Ensures(len(Result()) == len(values))
    return values[::-1]

def visit(values: Tuple[int, ...]) -> None:
    for value in values:
        pass
"#;
    let verification = verify_contract_module(source, "variadic_tuple.py", &[])
        .unwrap_or_else(|failure| panic!("variadic tuple program was refused: {failure:#?}"));
    assert!(verification.passed, "{:#?}", verification.obligations);
}

#[test]
fn scalar_frontend_rejects_invalid_tuple_uses_and_accepts_supported_nested_elements() {
    let list_coercion = verify_contract_module(
        "from typing import List, Tuple\ndef bad(values: Tuple[int, ...]) -> List[int]:\n    return values\n",
        "variadic_tuple_is_not_list.py",
        &[],
    )
    .expect_err("a tuple must not silently become a list");
    assert_eq!(
        list_coercion.code,
        "frontend.python.contracts.type-mismatch"
    );

    let from_list = verify_contract_module(
        "from typing import List, Tuple\ndef bad(values: List[int]) -> Tuple[int, ...]:\n    return values\n",
        "list_is_not_variadic_tuple.py",
        &[],
    )
    .expect_err("a list must not silently become a tuple");
    assert_eq!(from_list.code, "frontend.python.contracts.type-mismatch");

    let fixed_tuple = verify_contract_module(
        "from typing import Tuple\ndef bad(values: Tuple[int, ...]) -> Tuple[int, int]:\n    return values\n",
        "variadic_tuple_is_not_fixed.py",
        &[],
    )
    .expect_err("a symbolic-width tuple must not silently become a fixed tuple");
    assert_eq!(fixed_tuple.code, "frontend.python.contracts.type-mismatch");

    let heterogeneous = verify_contract_module(
        "from typing import Tuple\ndef bad() -> Tuple[int, ...]:\n    return (1, 'wrong')\n",
        "heterogeneous_variadic_tuple.py",
        &[],
    )
    .expect_err("every element must satisfy the homogeneous tuple type");
    assert_eq!(
        heterogeneous.code,
        "frontend.python.contracts.type-mismatch"
    );

    let mutation = verify_contract_module(
        "from typing import Tuple\ndef bad(values: Tuple[int, ...]) -> None:\n    values.append(1)\n",
        "immutable_variadic_tuple.py",
        &[],
    )
    .expect_err("variadic tuples are immutable");
    assert!(
        matches!(
            mutation.code,
            "frontend.python.contracts.statement-unsupported"
                | "frontend.python.contracts.expression-unsupported"
        ),
        "{mutation:#?}"
    );

    let mutable_elements = verify_contract_module(
        "from typing import List, Tuple\ndef bad(values: Tuple[List[int], ...]) -> None:\n    pass\n",
        "mutable_variadic_tuple_elements.py",
        &[],
    )
    .unwrap_or_else(|failure| {
        panic!("supported nested mutable collection elements were refused: {failure:#?}")
    });
    assert!(mutable_elements.passed, "{mutable_elements:#?}");
}

#[test]
fn starred_iteration_is_exact_for_concrete_values_and_refuses_symbolic_width() {
    let concrete = r#"from nagini_contracts.contracts import *
from typing import List, Tuple

def unpack() -> None:
    entries: List[Tuple[int, ...]] = [(1, 2, 3)]
    for head, *rest in entries:
        Assert(head == 1)
        Assert(len(rest) == 2)
        Assert(rest[0] == 2)
"#;
    let verification = verify_contract_module(concrete, "concrete_starred_tuple.py", &[])
        .unwrap_or_else(|failure| panic!("concrete starred unpack was refused: {failure:#?}"));
    assert!(verification.passed, "{:#?}", verification.obligations);

    let symbolic = r#"from typing import List, Tuple
def unpack(entries: List[Tuple[int, ...]]) -> None:
    for head, *rest in entries:
        pass
"#;
    let refusal = verify_contract_module(symbolic, "symbolic_starred_tuple.py", &[])
        .expect_err("symbolic tuple width cannot be invented");
    assert_eq!(
        refusal.code,
        "frontend.python.contracts.symbolic-for-unpacking-unsupported"
    );
}
