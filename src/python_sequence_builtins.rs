//! Exact scalar sequence operations that are represented directly in the VC term language.
//!
//! This module deliberately contains no fixture-specific summaries.  Each constructor denotes
//! the corresponding Python operation on a complete immutable sequence value; the solver owns
//! its recursive meaning.

use crate::vc::{Sort, Term};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SequenceBuiltinError {
    ExpectedList {
        operation: &'static str,
        actual: Sort,
    },
    MismatchedConcatElements {
        left: Sort,
        right: Sort,
    },
    ExpectedIntegerElements {
        operation: &'static str,
        actual: Sort,
    },
}

pub(crate) fn concatenate(left: Term, right: Term) -> Result<Term, SequenceBuiltinError> {
    let left_sort = left
        .sort()
        .expect("the scalar frontend constructs sorted VC terms before sequence lowering");
    let right_sort = right
        .sort()
        .expect("the scalar frontend constructs sorted VC terms before sequence lowering");
    let Sort::List(left_element) = &left_sort else {
        return Err(SequenceBuiltinError::ExpectedList {
            operation: "list concatenation left operand",
            actual: left_sort,
        });
    };
    let Sort::List(right_element) = &right_sort else {
        return Err(SequenceBuiltinError::ExpectedList {
            operation: "list concatenation right operand",
            actual: right_sort,
        });
    };
    if left_element != right_element {
        return Err(SequenceBuiltinError::MismatchedConcatElements {
            left: left_element.as_ref().clone(),
            right: right_element.as_ref().clone(),
        });
    }
    Ok(Term::ListConcat {
        left: Box::new(left),
        right: Box::new(right),
    })
}

pub(crate) fn sum(source: Term) -> Result<Term, SequenceBuiltinError> {
    require_integer_list(&source, "sum")?;
    Ok(Term::ListSum {
        source: Box::new(source),
    })
}

pub(crate) fn sorted(source: Term) -> Result<Term, SequenceBuiltinError> {
    require_integer_list(&source, "sorted")?;
    Ok(Term::ListSorted {
        source: Box::new(source),
    })
}

fn require_integer_list(
    source: &Term,
    operation: &'static str,
) -> Result<(), SequenceBuiltinError> {
    let actual = source
        .sort()
        .expect("the scalar frontend constructs sorted VC terms before sequence lowering");
    match actual {
        Sort::List(element) if element.as_ref() == &Sort::Int => Ok(()),
        Sort::List(element) => Err(SequenceBuiltinError::ExpectedIntegerElements {
            operation,
            actual: element.as_ref().clone(),
        }),
        actual => Err(SequenceBuiltinError::ExpectedList { operation, actual }),
    }
}
