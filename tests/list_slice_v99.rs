use std::num::NonZeroI128;

use maledictus::solver::discharge;
use maledictus::vc::{Obligation, ObligationExpectation, ObligationStatus, Sort, SortError, Term};

fn nonzero(value: i128) -> NonZeroI128 {
    NonZeroI128::new(value).expect("test slice step must be nonzero")
}

fn int(value: i64) -> Term {
    Term::Int { value }
}

fn int_list(values: impl IntoIterator<Item = i64>) -> Term {
    Term::List {
        element_sort: Sort::Int,
        values: values.into_iter().map(int).collect(),
    }
}

fn symbolic_int_list(name: &str) -> Term {
    Term::Variable {
        name: name.to_owned(),
        sort: Sort::List(Box::new(Sort::Int)),
    }
}

fn slice(source: Term, lower: Option<i128>, upper: Option<i128>, step: i128) -> Term {
    Term::ListSlice {
        source: Box::new(source),
        lower,
        upper,
        step: nonzero(step),
    }
}

fn length(value: Term) -> Term {
    Term::ListLength {
        value: Box::new(value),
    }
}

fn get(list: Term, index: i64) -> Term {
    Term::ListGet {
        list: Box::new(list),
        index: Box::new(int(index)),
    }
}

fn equal(left: Term, right: Term) -> Term {
    Term::Equal {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn solve(assumptions: Vec<Term>, conclusion: Term) -> ObligationStatus {
    discharge(&Obligation {
        id: "v99:static-list-slice".to_owned(),
        expectation: ObligationExpectation::Prove,
        assumptions,
        conclusion,
        path: "list_slice_v99.vc".to_owned(),
        byte_offset: 0,
        line: 1,
        column: 1,
    })
    .expect("static list-slice obligation must lower")
    .status
}

fn prove(assumptions: Vec<Term>, conclusion: Term) {
    assert_eq!(solve(assumptions, conclusion), ObligationStatus::Proved);
}

#[test]
fn list_slice_is_strongly_typed_and_zero_step_cannot_be_decoded() {
    let list_slice = slice(symbolic_int_list("items"), Some(-3), None, 1);
    assert_eq!(list_slice.sort_typed(), Ok(Sort::List(Box::new(Sort::Int))));

    let scalar_slice = slice(int(7), None, None, 1);
    assert_eq!(
        scalar_slice.sort_typed(),
        Err(SortError::ListSliceOperandNotList { actual: Sort::Int })
    );

    for roundtrip in [
        list_slice,
        slice(
            symbolic_int_list("extreme_items"),
            Some(i128::MIN),
            Some(i128::MAX),
            i128::MIN,
        ),
    ] {
        let encoded = serde_json::to_string(&roundtrip).expect("valid slice must serialize");
        assert_eq!(
            serde_json::from_str::<Term>(&encoded).expect("valid slice must decode"),
            roundtrip
        );
    }

    let malformed = r#"{
        "kind": "list-slice",
        "source": {"kind": "list", "element_sort": "int", "values": []},
        "lower": null,
        "upper": null,
        "step": 0
    }"#;
    assert!(serde_json::from_str::<Term>(malformed).is_err());

    let omitted_bounds = r#"{
        "kind": "list-slice",
        "source": {"kind": "list", "element_sort": "int", "values": []},
        "step": -1
    }"#;
    assert_eq!(
        serde_json::from_str::<Term>(omitted_bounds).expect("open bounds must decode"),
        slice(int_list([]), None, None, -1)
    );
}

#[test]
fn concrete_slices_preserve_python_bounds_and_output_order() {
    let source = int_list(0..6);
    for (actual, expected) in [
        (slice(source.clone(), Some(1), Some(5), 2), int_list([1, 3])),
        (
            slice(source.clone(), None, None, -1),
            int_list([5, 4, 3, 2, 1, 0]),
        ),
        (slice(source.clone(), None, Some(-1), -1), int_list([])),
        (
            slice(source.clone(), Some(i128::MIN), Some(i128::MAX), i128::MAX),
            int_list([0]),
        ),
        (slice(int_list([]), None, None, -1), int_list([])),
    ] {
        prove(Vec::new(), equal(actual, expected));
    }
}

#[test]
fn symbolic_slices_normalize_negative_bounds_and_map_each_result_index() {
    let source = symbolic_int_list("source");
    let sliced = slice(source.clone(), Some(-6), Some(6), 2);
    let source_length_is_seven = equal(length(source.clone()), int(7));
    let conclusion = Term::And {
        values: vec![
            equal(length(sliced.clone()), int(3)),
            equal(get(sliced.clone(), 0), get(source.clone(), 1)),
            equal(get(sliced.clone(), 1), get(source.clone(), 3)),
            equal(get(sliced, 2), get(source, 5)),
        ],
    };
    prove(vec![source_length_is_seven], conclusion);
}

#[test]
fn symbolic_reverse_and_extreme_step_have_exact_python_semantics() {
    let source = symbolic_int_list("reverse_source");
    let reverse = slice(source.clone(), None, None, -1);
    let extreme = slice(source.clone(), None, None, i128::MIN);
    let source_length_is_ten = equal(length(source.clone()), int(10));
    let conclusion = Term::And {
        values: vec![
            equal(length(reverse.clone()), int(10)),
            equal(get(reverse.clone(), 0), get(source.clone(), 9)),
            equal(get(reverse, 9), get(source.clone(), 0)),
            equal(length(extreme.clone()), int(1)),
            equal(get(extreme, 0), get(source, 9)),
        ],
    };
    prove(vec![source_length_is_ten], conclusion);
}

#[test]
fn symbolic_slice_has_no_materialization_cap_and_refutes_wrong_order() {
    let source = symbolic_int_list("large_source");
    let sliced = slice(source.clone(), Some(1), None, 3);
    let source_length = equal(length(source.clone()), int(100_000));
    prove(
        vec![source_length.clone()],
        equal(length(sliced.clone()), int(33_333)),
    );
    assert_eq!(
        solve(
            Vec::new(),
            equal(slice(int_list(0..6), Some(1), None, 3), int_list([1, 3]),),
        ),
        ObligationStatus::Refuted
    );
}
