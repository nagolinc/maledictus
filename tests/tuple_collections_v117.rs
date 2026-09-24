use maledictus::python_contracts::verify_contract_module;
use maledictus::solver::discharge;
use maledictus::vc::{Obligation, ObligationExpectation, ObligationStatus, Sort, Term};

fn tuple_sort() -> Sort {
    Sort::Tuple(vec![Sort::String, Sort::Int])
}

fn tuple(text: &str, number: i64) -> Term {
    Term::Tuple {
        values: vec![
            Term::String {
                value: text.to_owned(),
            },
            Term::Int { value: number },
        ],
    }
}

fn prove(assumptions: Vec<Term>, conclusion: Term) {
    let result = discharge(&Obligation {
        id: "v117:immutable-tuple-collections".to_owned(),
        expectation: ObligationExpectation::Prove,
        assumptions,
        conclusion,
        path: "tuple_collections_v117.vc".to_owned(),
        byte_offset: 0,
        line: 1,
        column: 1,
    })
    .expect("tuple collection obligation must lower");
    assert_eq!(result.status, ObligationStatus::Proved, "{result:#?}");
}

#[test]
fn z3_datatype_round_trips_tuple_elements_through_lists() {
    let pair = tuple("stable", 7);
    let list = Term::List {
        element_sort: tuple_sort(),
        values: vec![pair.clone(), tuple("other", 9)],
    };
    assert_eq!(list.sort_typed(), Ok(Sort::List(Box::new(tuple_sort()))));
    prove(
        Vec::new(),
        Term::Equal {
            left: Box::new(Term::TupleGet {
                tuple: Box::new(Term::ListGet {
                    list: Box::new(list.clone()),
                    index: Box::new(Term::Int { value: 0 }),
                }),
                index: 1,
            }),
            right: Box::new(Term::Int { value: 7 }),
        },
    );
    prove(
        Vec::new(),
        Term::ListContains {
            list: Box::new(list),
            value: Box::new(pair),
        },
    );
}

#[test]
fn z3_datatype_round_trips_nested_tuple_dictionary_values_and_keys() {
    let nested = Sort::Tuple(vec![Sort::Int, tuple_sort()]);
    let dictionary = Term::Variable {
        name: "records".to_owned(),
        sort: Sort::Dict(Box::new(tuple_sort()), Box::new(nested.clone())),
    };
    let key = tuple("key", 1);
    let expected = Term::Tuple {
        values: vec![Term::Int { value: 4 }, tuple("payload", 8)],
    };
    let lookup = Term::DictGet {
        dict: Box::new(dictionary),
        key: Box::new(key),
    };
    prove(
        vec![Term::Equal {
            left: Box::new(lookup.clone()),
            right: Box::new(expected),
        }],
        Term::Equal {
            left: Box::new(Term::TupleGet {
                tuple: Box::new(Term::TupleGet {
                    tuple: Box::new(lookup),
                    index: 1,
                }),
                index: 0,
            }),
            right: Box::new(Term::String {
                value: "payload".to_owned(),
            }),
        },
    );
}

#[test]
fn scalar_frontend_verifies_immutable_list_and_dictionary_tuple_access() {
    let source = r#"from nagini_contracts.contracts import *
from typing import Dict, List, Tuple

def first(values: List[Tuple[int, str]]) -> int:
    Requires(len(values) > 0)
    Ensures(Result() == values[0][0])
    return values[0][0]

def dictionary_value(values: Dict[int, Tuple[str, int]]) -> int:
    Requires(1 in values)
    Ensures(Result() == values[1][1])
    return values[1][1]

def tuple_key(values: Dict[Tuple[str, int], int], key: Tuple[str, int]) -> int:
    Requires(key in values)
    Ensures(Result() == values[key])
    return values[key]
"#;
    let verification = verify_contract_module(source, "immutable_tuple_collections.py", &[])
        .unwrap_or_else(|failure| panic!("immutable tuple collections were refused: {failure:#?}"));
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn scalar_frontend_verifies_closed_tuple_set_literals_and_symbolic_membership() {
    let source = r#"from nagini_contracts.contracts import *
from typing import Set, Tuple

def member(values: Set[Tuple[str, int]], key: Tuple[str, int]) -> bool:
    Ensures(Result() == (key in values))
    return key in values

def run() -> None:
    values = {('stable', 7), ('other', 9), ('stable', 7)}
    assert len(values) == 2
    assert ('stable', 7) in values
    assert ('missing', 7) not in values
"#;
    let verification = verify_contract_module(source, "immutable_tuple_sets.py", &[])
        .unwrap_or_else(|failure| panic!("immutable tuple sets were refused: {failure:#?}"));
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn mutable_tuple_members_are_precise_and_symbolic_set_construction_fails_closed() {
    let mutable = verify_contract_module(
        concat!(
            "def run() -> None:\n",
            "    values = [([1], 2)]\n",
            "    assert len(values) == 1\n",
            "    assert len(values[0][0]) == 1\n",
            "    assert values[0][0][0] == 1\n",
            "    assert values[0][1] == 2\n",
        ),
        "mutable_tuple_member.py",
        &[],
    )
    .unwrap_or_else(|failure| panic!("nested mutable tuple values were refused: {failure:#?}"));
    assert!(mutable.passed, "{mutable:#?}");

    let symbolic = verify_contract_module(
        "from typing import Set, Tuple\ndef run(value: Tuple[str, int]) -> None:\n    values = {value}\n",
        "symbolic_tuple_set.py",
        &[],
    )
    .expect_err("symbolic set literals need exact duplicate elimination before support");
    assert_eq!(
        symbolic.code,
        "frontend.python.contracts.set-literal-symbolic-unsupported"
    );
}
