use maledictus::solver;
use maledictus::vc::{Obligation, ObligationExpectation, ObligationStatus, Sort, SortError, Term};

fn integer_list(values: &[i64]) -> Term {
    Term::List {
        element_sort: Sort::Int,
        values: values
            .iter()
            .copied()
            .map(|value| Term::Int { value })
            .collect(),
    }
}

fn obligation(id: &str, conclusion: Term) -> Obligation {
    Obligation {
        id: id.to_owned(),
        expectation: ObligationExpectation::Prove,
        assumptions: Vec::new(),
        conclusion,
        path: "list_sequence_builtins_v115.py".to_owned(),
        byte_offset: 0,
        line: 1,
        column: 1,
    }
}

#[test]
fn protocol_roundtrips_the_three_typed_list_builtins() {
    let terms = [
        Term::ListConcat {
            left: Box::new(integer_list(&[1])),
            right: Box::new(integer_list(&[2])),
        },
        Term::ListSum {
            source: Box::new(integer_list(&[-1, 2])),
        },
        Term::ListSorted {
            source: Box::new(integer_list(&[2, 1])),
        },
    ];
    for (term, expected_kind) in terms
        .into_iter()
        .zip(["list-concat", "list-sum", "list-sorted"])
    {
        let json = serde_json::to_value(&term).unwrap();
        assert_eq!(json["kind"], expected_kind);
        assert_eq!(serde_json::from_value::<Term>(json).unwrap(), term);
    }
}

#[test]
fn typed_sort_errors_reject_wrong_list_builtin_operands() {
    assert_eq!(
        Term::ListConcat {
            left: Box::new(Term::Bool { value: true }),
            right: Box::new(integer_list(&[])),
        }
        .sort_typed(),
        Err(SortError::ListConcatLeftOperandNotList { actual: Sort::Bool })
    );
    assert_eq!(
        Term::ListConcat {
            left: Box::new(integer_list(&[])),
            right: Box::new(Term::List {
                element_sort: Sort::Bool,
                values: Vec::new(),
            }),
        }
        .sort_typed(),
        Err(SortError::ListConcatElementSortMismatch {
            left_element: Sort::Int,
            right_element: Sort::Bool,
        })
    );
    for error in [
        Term::ListSum {
            source: Box::new(Term::List {
                element_sort: Sort::Bool,
                values: Vec::new(),
            }),
        }
        .sort_typed(),
        Term::ListSorted {
            source: Box::new(Term::String {
                value: "not a list".to_owned(),
            }),
        }
        .sort_typed(),
    ] {
        assert!(error.is_err());
    }
}

#[test]
fn proves_exact_concat_length_law_for_symbolic_lists() {
    let left = Term::Variable {
        name: "concat-left".to_owned(),
        sort: Sort::List(Box::new(Sort::Int)),
    };
    let right = Term::Variable {
        name: "concat-right".to_owned(),
        sort: Sort::List(Box::new(Sort::Int)),
    };
    let result = solver::discharge(&obligation(
        "symbolic-list-concat-length",
        Term::And {
            values: vec![
                Term::Equal {
                    left: Box::new(Term::ListLength {
                        value: Box::new(Term::ListConcat {
                            left: Box::new(left.clone()),
                            right: Box::new(right.clone()),
                        }),
                    }),
                    right: Box::new(Term::Add {
                        left: Box::new(Term::ListLength {
                            value: Box::new(left.clone()),
                        }),
                        right: Box::new(Term::ListLength {
                            value: Box::new(right.clone()),
                        }),
                    }),
                },
                Term::Equal {
                    left: Box::new(Term::ListSum {
                        source: Box::new(Term::ListConcat {
                            left: Box::new(left.clone()),
                            right: Box::new(right.clone()),
                        }),
                    }),
                    right: Box::new(Term::Add {
                        left: Box::new(Term::ListSum {
                            source: Box::new(left),
                        }),
                        right: Box::new(Term::ListSum {
                            source: Box::new(right),
                        }),
                    }),
                },
            ],
        },
    ))
    .unwrap();
    assert_eq!(result.status, ObligationStatus::Proved, "{result:#?}");
}

#[test]
fn proves_symbolic_sorted_adjacent_order() {
    let source = Term::Variable {
        name: "sorted-source".to_owned(),
        sort: Sort::List(Box::new(Sort::Int)),
    };
    let sorted = Term::ListSorted {
        source: Box::new(source.clone()),
    };
    let mut request = obligation(
        "symbolic-list-sorted-adjacent-order",
        Term::LessEqual {
            left: Box::new(Term::ListGet {
                list: Box::new(sorted.clone()),
                index: Box::new(Term::Int { value: 0 }),
            }),
            right: Box::new(Term::ListGet {
                list: Box::new(sorted),
                index: Box::new(Term::Int { value: 1 }),
            }),
        },
    );
    request.assumptions.push(Term::GreaterEqual {
        left: Box::new(Term::ListLength {
            value: Box::new(source),
        }),
        right: Box::new(Term::Int { value: 2 }),
    });
    let result = solver::discharge(&request).unwrap();
    assert_eq!(result.status, ObligationStatus::Proved, "{result:#?}");
}

#[test]
fn proves_universal_symbolic_sorted_adjacent_order() {
    let sorted = Term::ListSorted {
        source: Box::new(Term::Variable {
            name: "universal-sorted-source".to_owned(),
            sort: Sort::List(Box::new(Sort::Int)),
        }),
    };
    let index = Term::Variable {
        name: "universal-sorted-index".to_owned(),
        sort: Sort::Int,
    };
    let successor = Term::Add {
        left: Box::new(index.clone()),
        right: Box::new(Term::Int { value: 1 }),
    };
    let result = solver::discharge(&obligation(
        "universal-symbolic-list-sorted-adjacent-order",
        Term::ForAll {
            binder: "universal-sorted-index".to_owned(),
            binder_sort: Sort::Int,
            body: Box::new(Term::Implies {
                left: Box::new(Term::And {
                    values: vec![
                        Term::GreaterEqual {
                            left: Box::new(index.clone()),
                            right: Box::new(Term::Int { value: 0 }),
                        },
                        Term::Less {
                            left: Box::new(successor.clone()),
                            right: Box::new(Term::ListLength {
                                value: Box::new(sorted.clone()),
                            }),
                        },
                    ],
                }),
                right: Box::new(Term::LessEqual {
                    left: Box::new(Term::ListGet {
                        list: Box::new(sorted.clone()),
                        index: Box::new(index),
                    }),
                    right: Box::new(Term::ListGet {
                        list: Box::new(sorted),
                        index: Box::new(successor),
                    }),
                }),
            }),
        },
    ))
    .unwrap();
    assert_eq!(result.status, ObligationStatus::Proved, "{result:#?}");
}

#[test]
fn proves_empty_and_negative_integer_sums() {
    for (id, values, expected) in [
        ("empty-list-sum", Vec::new(), 0),
        ("negative-list-sum", vec![-8, 3, -2], -7),
    ] {
        let result = solver::discharge(&obligation(
            id,
            Term::Equal {
                left: Box::new(Term::ListSum {
                    source: Box::new(integer_list(&values)),
                }),
                right: Box::new(Term::Int { value: expected }),
            },
        ))
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved, "{result:#?}");
    }
}

#[test]
fn proves_duplicate_preserving_insertion_sort() {
    let result = solver::discharge(&obligation(
        "duplicate-preserving-list-sort",
        Term::Equal {
            left: Box::new(Term::ListSorted {
                source: Box::new(integer_list(&[3, 1, 3, 2, 1])),
            }),
            right: Box::new(integer_list(&[1, 1, 2, 3, 3])),
        },
    ))
    .unwrap();
    assert_eq!(result.status, ObligationStatus::Proved, "{result:#?}");
}

#[test]
fn refutes_equal_sum_lists_as_sorted_permutations() {
    let result = solver::discharge(&obligation(
        "equal-sum-is-not-permutation",
        Term::Equal {
            left: Box::new(Term::ListSorted {
                source: Box::new(integer_list(&[1, 4])),
            }),
            right: Box::new(Term::ListSorted {
                source: Box::new(integer_list(&[2, 3])),
            }),
        },
    ))
    .unwrap();
    assert_eq!(result.status, ObligationStatus::Refuted, "{result:#?}");
}
