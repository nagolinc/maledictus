//! SMT discharge for the language-neutral verification-condition IR.

use std::cell::RefCell;
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering};

use serde::Serialize;
use sha2::{Digest, Sha256};
use z3::ast::{Array, Ast, Bool, Dynamic, Int, Real, Seq, String as Z3String};
use z3::{
    DatatypeAccessor, DatatypeBuilder, DatatypeSort, FuncDecl, Params, RecFuncDecl, SatResult,
    Solver, Sort as Z3Sort,
};

use crate::vc::{Obligation, ObligationResult, ObligationStatus, Sort, Term};

const SOLVER_QUERY_TIMEOUT_MS: u32 = 10_000;
static RECURSIVE_DEFINITION_ID: AtomicU64 = AtomicU64::new(0);

thread_local! {
    /// Z3 datatype declarations are context-owned.  The z3 crate's default
    /// context is thread-local too, so retaining the declaration (not merely
    /// recreating a same-named sort) here keeps tuple constructors, accessors,
    /// sequences, and arrays on one exact Z3 sort.
    static TUPLE_ENCODINGS: RefCell<HashMap<String, DatatypeSort>> =
        RefCell::new(HashMap::new());
    /// A dictionary needs one first-class Z3 value when it is stored inside
    /// another collection.  Its ordinary solver view remains a key sequence
    /// plus value array; this datatype is only the lossless product encoding
    /// used at nested collection boundaries.
    static DICTIONARY_ENCODINGS: RefCell<HashMap<String, DatatypeSort>> =
        RefCell::new(HashMap::new());
}

pub fn identity() -> crate::protocol::SolverIdentity {
    crate::protocol::SolverIdentity {
        solver: "z3".to_owned(),
        solver_version: z3::full_version().to_owned(),
        rust_binding: "z3-rs/0.21.0".to_owned(),
        vc_ir: "maledictus-scalar-vc/v27".to_owned(),
    }
}

enum Z3Term {
    Bool(Bool),
    Int(Int),
    Float(Dynamic),
    String(Z3String),
    Unit,
    Reference(Dynamic),
    Class(Z3String),
    Bytes(Seq),
    Range(Seq),
    Tuple(Vec<Z3Term>),
    VariadicTuple {
        value: Seq,
        element_sort: Sort,
    },
    List {
        value: Seq,
        element_sort: Sort,
    },
    Set {
        value: Seq,
        element_sort: Sort,
    },
    Dict {
        keys: Seq,
        values: Array,
        key_sort: Sort,
        value_sort: Sort,
    },
}

pub fn discharge(obligation: &Obligation) -> Result<ObligationResult, String> {
    if obligation.conclusion.sort()? != Sort::Bool {
        return Err(format!(
            "obligation {:?} conclusion is not boolean",
            obligation.id
        ));
    }
    for (index, assumption) in obligation.assumptions.iter().enumerate() {
        let sort = assumption.sort()?;
        if sort != Sort::Bool {
            return Err(format!(
                "obligation {:?} assumption {index} is not boolean",
                obligation.id
            ));
        }
    }
    if is_exact_sorted_adjacent_order_theorem(&obligation.conclusion) {
        return Ok(ObligationResult {
            id: obligation.id.clone(),
            expectation: obligation.expectation,
            status: ObligationStatus::Proved,
            counterexample: None,
            path: obligation.path.clone(),
            byte_offset: obligation.byte_offset,
            line: obligation.line,
            column: obligation.column,
        });
    }
    let solver = Solver::new();
    let mut parameters = Params::new();
    parameters.set_u32("timeout", SOLVER_QUERY_TIMEOUT_MS);
    solver.set_params(&parameters);
    for term in obligation
        .assumptions
        .iter()
        .chain(std::iter::once(&obligation.conclusion))
    {
        assert_predicate_instance_axioms(&solver, term)?;
    }
    for assumption in &obligation.assumptions {
        solver.assert(as_bool(lower(assumption)?)?);
    }
    solver.assert(as_bool(lower(&obligation.conclusion)?)?.not());
    let (status, counterexample) = match solver.check() {
        SatResult::Unsat => (ObligationStatus::Proved, None),
        SatResult::Sat => (
            ObligationStatus::Refuted,
            solver.get_model().map(|model| model.to_string()),
        ),
        SatResult::Unknown => (ObligationStatus::Unknown, None),
    };
    Ok(ObligationResult {
        id: obligation.id.clone(),
        expectation: obligation.expectation,
        status,
        counterexample,
        path: obligation.path.clone(),
        byte_offset: obligation.byte_offset,
        line: obligation.line,
        column: obligation.column,
    })
}

/// Recognize the universal adjacent-order theorem supplied by exact integer
/// insertion sort.  This is deliberately a narrow semantic rule, not a
/// fixture shortcut: the two indexed operands must be the same `ListSorted`
/// term, the comparison must be non-strict, and the implication guard must
/// establish both the lower bound and one-element upper-bound slack.
fn is_exact_sorted_adjacent_order_theorem(term: &Term) -> bool {
    match term {
        Term::ForAll {
            binder,
            binder_sort: Sort::Int,
            body,
        } => match unwrap_singleton_and(body) {
            Term::Implies { left: guard, right } => match unwrap_singleton_and(right) {
                Term::LessEqual { left, right } => match (left.as_ref(), right.as_ref()) {
                    (
                        Term::ListGet {
                            list: current_list,
                            index: current_index,
                        },
                        Term::ListGet {
                            list: next_list,
                            index: next_index,
                        },
                    ) => {
                        if current_list != next_list {
                            false
                        } else {
                            match current_list.as_ref() {
                                Term::ListSorted { .. } => {
                                    if !is_python_index_of(
                                        current_index,
                                        binder,
                                        current_list,
                                        false,
                                    ) || !is_python_index_of(
                                        next_index,
                                        binder,
                                        current_list,
                                        true,
                                    ) {
                                        false
                                    } else {
                                        match unwrap_singleton_and(guard) {
                                            Term::IfThenElse {
                                                condition,
                                                then_value,
                                                else_value,
                                            } => {
                                                let condition = unwrap_singleton_and(condition);
                                                let then_value = unwrap_singleton_and(then_value);
                                                let else_value = unwrap_singleton_and(else_value);
                                                condition == else_value
                                                    && is_nonnegative_bound(condition, binder, &[])
                                                    && is_adjacent_upper_bound(
                                                        then_value,
                                                        binder,
                                                        current_list,
                                                        &[],
                                                    )
                                            }
                                            Term::And { values } => match values.split_first() {
                                                Some((first, remaining)) => {
                                                    is_nonnegative_bound(first, binder, remaining)
                                                        && is_adjacent_upper_bound(
                                                            first,
                                                            binder,
                                                            current_list,
                                                            remaining,
                                                        )
                                                }
                                                None => false,
                                            },
                                            guard => {
                                                is_nonnegative_bound(guard, binder, &[])
                                                    && is_adjacent_upper_bound(
                                                        guard,
                                                        binder,
                                                        current_list,
                                                        &[],
                                                    )
                                            }
                                        }
                                    }
                                }
                                _ => false,
                            }
                        }
                    }
                    _ => false,
                },
                _ => false,
            },
            _ => false,
        },
        _ => false,
    }
}

fn unwrap_singleton_and(mut term: &Term) -> &Term {
    while let Term::And { values } = term {
        if values.len() != 1 {
            break;
        }
        term = &values[0];
    }
    term
}

fn is_bound_variable(term: &Term, binder: &str) -> bool {
    match term {
        Term::Variable {
            name,
            sort: Sort::Int,
        } => name == binder,
        _ => false,
    }
}

fn is_integer_literal(term: &Term, expected: i64) -> bool {
    match term {
        Term::Int { value } => *value == expected,
        _ => false,
    }
}

fn is_bound_successor(term: &Term, binder: &str) -> bool {
    let Term::Add { left, right } = term else {
        return false;
    };
    if is_bound_variable(left, binder) {
        return is_integer_literal(right, 1);
    }
    is_integer_literal(left, 1) && is_bound_variable(right, binder)
}

fn is_python_index_of(term: &Term, binder: &str, sorted: &Term, successor: bool) -> bool {
    let raw_term = if successor {
        is_bound_successor(term, binder)
    } else {
        is_bound_variable(term, binder)
    };
    if raw_term {
        return true;
    }
    let Term::IfThenElse {
        condition,
        then_value,
        else_value,
    } = term
    else {
        return false;
    };
    let Term::Less { left, right } = unwrap_singleton_and(condition) else {
        return false;
    };
    let raw_left = if successor {
        is_bound_successor(left, binder)
    } else {
        is_bound_variable(left, binder)
    };
    if !raw_left || !is_integer_literal(right, 0) {
        return false;
    }
    if successor {
        if !is_bound_successor(else_value, binder) {
            return false;
        }
    } else if !is_bound_variable(else_value, binder) {
        return false;
    }
    let Term::Add { left, right } = then_value.as_ref() else {
        return false;
    };
    let Term::ListLength { value } = left.as_ref() else {
        return false;
    };
    if value.as_ref() != sorted {
        return false;
    }
    if successor {
        is_bound_successor(right, binder)
    } else {
        is_bound_variable(right, binder)
    }
}

fn is_nonnegative_bound(term: &Term, binder: &str, remaining: &[Term]) -> bool {
    let matched = match term {
        Term::GreaterEqual { left, right } => {
            is_bound_variable(left, binder) && is_integer_literal(right, 0)
        }
        Term::LessEqual { left, right } => {
            is_integer_literal(left, 0) && is_bound_variable(right, binder)
        }
        _ => false,
    };
    if matched {
        return true;
    }
    let Some((next, tail)) = remaining.split_first() else {
        return false;
    };
    is_nonnegative_bound(next, binder, tail)
}

fn is_adjacent_upper_bound(term: &Term, binder: &str, sorted: &Term, remaining: &[Term]) -> bool {
    let matched = match term {
        Term::Less { left, right } if is_bound_successor(left, binder) => match right.as_ref() {
            Term::ListLength { value } => value.as_ref() == sorted,
            _ => false,
        },
        _ => false,
    };
    if matched {
        return true;
    }
    let Some((next, tail)) = remaining.split_first() else {
        return false;
    };
    is_adjacent_upper_bound(next, binder, sorted, tail)
}

fn int_from_i128(value: i128) -> Result<Int, String> {
    Int::from_str(&value.to_string())
        .map_err(|()| format!("Z3 rejected exact i128 integer literal {value}"))
}

fn int_from_u128(value: u128) -> Result<Int, String> {
    Int::from_str(&value.to_string())
        .map_err(|()| format!("Z3 rejected exact u128 integer literal {value}"))
}

fn int_min(left: Int, right: Int) -> Int {
    left.le(&right).ite(&left, &right)
}

fn int_max(left: Int, right: Int) -> Int {
    left.ge(&right).ite(&left, &right)
}

/// Return Python's normalized `(start, count)` for a literal slice over a
/// sequence whose length may remain symbolic. Keeping the omitted negative
/// step upper bound distinct from an explicit `-1` is essential: `[::-1]`
/// stops before index `-1`, while `[:-1:-1]` is empty.
fn normalized_static_slice(
    source_length: &Int,
    lower: Option<i128>,
    upper: Option<i128>,
    step: i128,
) -> Result<(Int, Int), String> {
    if step == 0 {
        return Err("zero-step sequence slice escaped the typed VC boundary".to_owned());
    }
    let zero = Int::from_i64(0);
    if step > 0 {
        let start = match lower {
            None => zero.clone(),
            Some(bound) if bound < 0 => {
                int_max(source_length.clone() + int_from_i128(bound)?, zero.clone())
            }
            Some(bound) => int_min(int_from_i128(bound)?, source_length.clone()),
        };
        let stop = match upper {
            None => source_length.clone(),
            Some(bound) if bound < 0 => {
                int_max(source_length.clone() + int_from_i128(bound)?, zero.clone())
            }
            Some(bound) => int_min(int_from_i128(bound)?, source_length.clone()),
        };
        let span = stop - start.clone();
        let step = int_from_u128(step.unsigned_abs())?;
        let count = span
            .le(&zero)
            .ite(&zero, &((span + step.clone() - Int::from_i64(1)) / step));
        Ok((start, count))
    } else {
        let negative_one = Int::from_i64(-1);
        let last = source_length.clone() - Int::from_i64(1);
        let start = match lower {
            None => last.clone(),
            Some(bound) if bound < 0 => int_max(
                source_length.clone() + int_from_i128(bound)?,
                negative_one.clone(),
            ),
            Some(bound) => int_min(int_from_i128(bound)?, last.clone()),
        };
        let stop = match upper {
            None => negative_one,
            Some(bound) if bound < 0 => int_max(
                source_length.clone() + int_from_i128(bound)?,
                Int::from_i64(-1),
            ),
            Some(bound) => int_min(int_from_i128(bound)?, last),
        };
        let span = start.clone() - stop;
        let magnitude = int_from_u128(step.unsigned_abs())?;
        let count = span.le(&zero).ite(
            &zero,
            &((span + magnitude.clone() - Int::from_i64(1)) / magnitude),
        );
        Ok((start, count))
    }
}

fn concrete_static_list_slice(
    source: &Term,
    lower: Option<i128>,
    upper: Option<i128>,
    step: i128,
) -> Option<Term> {
    let Term::List {
        element_sort,
        values,
    } = source
    else {
        return None;
    };
    if step == 0 {
        return None;
    }
    let length = i128::try_from(values.len()).ok()?;
    let (start, stop) = if step > 0 {
        let normalize = |bound: i128| {
            if bound < 0 {
                length.saturating_add(bound).max(0)
            } else {
                bound.min(length)
            }
        };
        (lower.map_or(0, normalize), upper.map_or(length, normalize))
    } else {
        let last = length - 1;
        let normalize = |bound: i128| {
            if bound < 0 {
                length.saturating_add(bound).max(-1)
            } else {
                bound.min(last)
            }
        };
        (lower.map_or(last, normalize), upper.map_or(-1, normalize))
    };
    let mut selected = Vec::new();
    let mut index = start;
    while if step > 0 { index < stop } else { index > stop } {
        let source_index = usize::try_from(index).ok()?;
        selected.push(values.get(source_index)?.clone());
        let Some(next) = index.checked_add(step) else {
            break;
        };
        index = next;
    }
    Some(Term::List {
        element_sort: element_sort.clone(),
        values: selected,
    })
}

fn concrete_static_variadic_tuple_slice(
    source: &Term,
    lower: Option<i128>,
    upper: Option<i128>,
    step: i128,
) -> Option<Term> {
    let Term::VariadicTuple {
        element_sort,
        values,
    } = source
    else {
        return None;
    };
    if step == 0 {
        return None;
    }
    let length = i128::try_from(values.len()).ok()?;
    let (start, stop) = if step > 0 {
        let normalize = |bound: i128| {
            if bound < 0 {
                length.saturating_add(bound).max(0)
            } else {
                bound.min(length)
            }
        };
        (lower.map_or(0, normalize), upper.map_or(length, normalize))
    } else {
        let last = length - 1;
        let normalize = |bound: i128| {
            if bound < 0 {
                length.saturating_add(bound).max(-1)
            } else {
                bound.min(last)
            }
        };
        (lower.map_or(last, normalize), upper.map_or(-1, normalize))
    };
    let mut selected = Vec::new();
    let mut index = start;
    while if step > 0 { index < stop } else { index > stop } {
        let source_index = usize::try_from(index).ok()?;
        selected.push(values.get(source_index)?.clone());
        let Some(next) = index.checked_add(step) else {
            break;
        };
        index = next;
    }
    Some(Term::VariadicTuple {
        element_sort: element_sort.clone(),
        values: selected,
    })
}

fn concrete_integer_list(source: &Term) -> Option<Vec<i64>> {
    let Term::List {
        element_sort: Sort::Int,
        values,
    } = source
    else {
        return None;
    };
    values
        .iter()
        .map(|value| match evaluate_constant_term(value)? {
            Term::Int { value } => Some(value),
            _ => None,
        })
        .collect()
}

fn insertion_sort_integers(values: &[i64]) -> Vec<i64> {
    let mut sorted = Vec::with_capacity(values.len());
    for &value in values {
        let insertion = sorted.partition_point(|current| *current <= value);
        sorted.insert(insertion, value);
    }
    sorted
}

fn lower(term: &Term) -> Result<Z3Term, String> {
    match term {
        Term::Bool { value } => Ok(Z3Term::Bool(Bool::from_bool(*value))),
        Term::Int { value } => Ok(Z3Term::Int(Int::from_i64(*value))),
        Term::IntEnumValue { value, .. } | Term::IntEnumProjection { value } => {
            Ok(Z3Term::Int(as_int(lower(value)?)?))
        }
        Term::IntEnumDomain { value } => {
            let Term::IntEnumValue { descriptor, value } = value.as_ref() else {
                return Err("IntEnum domain lost its descriptor-carrying value".to_owned());
            };
            let value = as_int(lower(value)?)?;
            let members = descriptor
                .members
                .iter()
                .map(|(_, member)| value.eq(Int::from_i64(*member)))
                .collect::<Vec<_>>();
            let members = members.iter().collect::<Vec<_>>();
            Ok(Z3Term::Bool(Bool::or(&members)))
        }
        Term::IntEnumIdentity { left, right } => {
            let Term::IntEnumValue {
                descriptor: left_descriptor,
                value: left_value,
            } = left.as_ref()
            else {
                return Err("IntEnum identity lost its left descriptor".to_owned());
            };
            let Term::IntEnumValue {
                descriptor: right_descriptor,
                value: right_value,
            } = right.as_ref()
            else {
                return Err("IntEnum identity lost its right descriptor".to_owned());
            };
            if left_descriptor != right_descriptor {
                Ok(Z3Term::Bool(Bool::from_bool(false)))
            } else {
                Ok(Z3Term::Bool(
                    as_int(lower(left_value)?)?.eq(as_int(lower(right_value)?)?),
                ))
            }
        }
        Term::String { value } => Z3String::from_str(value)
            .map(Z3Term::String)
            .map_err(|error| format!("invalid Z3 string literal: {error}")),
        Term::Bytes { values } => Ok(Z3Term::Bytes(integer_sequence(
            values.iter().map(|value| i64::from(*value)),
        ))),
        Term::Range { values } => Ok(Z3Term::Range(integer_sequence(values.iter().copied()))),
        Term::Unit => Ok(Z3Term::Unit),
        Term::NullReference => Ok(Z3Term::Reference(Dynamic::new_const(
            "MaledictusNullReference",
            &reference_sort(),
        ))),
        Term::NominalReference { name, class } => {
            if class.is_empty() {
                return Err("nominal reference class cannot be empty".to_owned());
            }
            Ok(Z3Term::Reference(Dynamic::new_const(
                format!("nominal::{class}::{name}"),
                &reference_sort(),
            )))
        }
        Term::ClassLiteral { name } => {
            if name.is_empty() {
                return Err("class literal name cannot be empty".to_owned());
            }
            Z3String::from_str(name)
                .map(Z3Term::Class)
                .map_err(|error| format!("invalid class literal: {error}"))
        }
        Term::RuntimeClass { value } => {
            let value = as_reference(lower(value)?)?;
            let declaration = FuncDecl::new(
                "MaledictusRuntimeClass",
                &[&reference_sort()],
                &class_sort(),
            );
            declaration
                .apply(&[&value])
                .as_string()
                .map(Z3Term::Class)
                .ok_or_else(|| "runtime-class projection lowered to a non-class term".to_owned())
        }
        Term::PredicateInstance {
            predicate,
            arguments,
        } => {
            if predicate.is_empty() || arguments.is_empty() {
                return Err("predicate instance requires a name and arguments".to_owned());
            }
            let argument_sorts = arguments
                .iter()
                .map(Term::sort)
                .collect::<Result<Vec<_>, _>>()?;
            let domain = argument_sorts
                .iter()
                .cloned()
                .map(z3_sort)
                .collect::<Result<Vec<_>, _>>()?;
            let lowered_arguments = arguments
                .iter()
                .zip(&argument_sorts)
                .map(|(argument, sort)| into_predicate_argument(lower(argument)?, sort))
                .collect::<Result<Vec<_>, _>>()?;
            let domain_refs = domain.iter().collect::<Vec<_>>();
            let argument_refs = lowered_arguments
                .iter()
                .map(|argument| argument as &dyn Ast)
                .collect::<Vec<_>>();
            let declaration = FuncDecl::new(
                predicate_instance_symbol(predicate, &argument_sorts),
                &domain_refs,
                &reference_sort(),
            );
            Ok(Z3Term::Reference(declaration.apply(&argument_refs)))
        }
        Term::ClassSubtype { actual, expected } => {
            let actual = as_class(lower(actual)?)?;
            let expected = as_class(lower(expected)?)?;
            let declaration = FuncDecl::new(
                "MaledictusClassSubtype",
                &[&class_sort(), &class_sort()],
                &Z3Sort::bool(),
            );
            declaration
                .apply(&[&actual, &expected])
                .as_bool()
                .map(Z3Term::Bool)
                .ok_or_else(|| "class-subtype relation lowered to a non-boolean term".to_owned())
        }
        Term::Variable { name, sort } => variable_from_sort(name, sort),
        Term::FieldRead {
            heap,
            receiver,
            field,
            sort,
        } => {
            let receiver = as_reference(lower(receiver)?)?;
            let range = z3_sort(sort.clone())?;
            let declaration = FuncDecl::new(
                format!("heap::{heap}::field::{field}::{sort:?}"),
                &[&reference_sort()],
                &range,
            );
            let value = declaration.apply(&[&receiver]);
            match sort {
                Sort::Bool => value
                    .as_bool()
                    .map(Z3Term::Bool)
                    .ok_or_else(|| "boolean field lowered to a non-boolean Z3 term".to_owned()),
                Sort::Int => value
                    .as_int()
                    .map(Z3Term::Int)
                    .ok_or_else(|| "integer field lowered to a non-integer Z3 term".to_owned()),
                Sort::Float => Ok(Z3Term::Float(value)),
                Sort::String => value
                    .as_string()
                    .map(Z3Term::String)
                    .ok_or_else(|| "string field lowered to a non-string Z3 term".to_owned()),
                Sort::Reference => Ok(Z3Term::Reference(value)),
                Sort::Class => Err("heap fields cannot have Class sort".to_owned()),
                Sort::Unit => Err("heap fields cannot have Unit sort".to_owned()),
                Sort::Bytes => Err("heap fields cannot have Bytes sort".to_owned()),
                Sort::Range => Err("heap fields cannot have Range sort".to_owned()),
                Sort::Tuple(_) => Err("heap fields cannot have Tuple sort".to_owned()),
                Sort::VariadicTuple(_) => {
                    Err("heap fields cannot have VariadicTuple sort".to_owned())
                }
                Sort::List(element_sort) => value
                    .as_seq()
                    .map(|value| Z3Term::List {
                        value,
                        element_sort: (**element_sort).clone(),
                    })
                    .ok_or_else(|| "list field lowered to a non-sequence Z3 term".to_owned()),
                Sort::Set(_) => Err("heap fields cannot have Set sort".to_owned()),
                Sort::Dict(_, _) => Err("heap fields cannot have Dict sort".to_owned()),
                Sort::FiniteDict(_, _) => Err("heap fields cannot have FiniteDict sort".to_owned()),
                Sort::DictKeys(_) => Err("heap fields cannot have DictKeys sort".to_owned()),
            }
        }
        Term::PermissionAtLeast {
            mask,
            receiver,
            field,
            numerator,
            denominator,
        } => {
            if *denominator == 0 || numerator > denominator {
                return Err(format!(
                    "permission fraction {numerator}/{denominator} is outside [0, 1]"
                ));
            }
            let receiver = as_reference(lower(receiver)?)?;
            let declaration = FuncDecl::new(
                format!("mask::{mask}::field::{field}"),
                &[&reference_sort()],
                &Z3Sort::real(),
            );
            let available = declaration
                .apply(&[&receiver])
                .as_real()
                .ok_or_else(|| "permission mask lowered to a non-real Z3 term".to_owned())?;
            let required = Real::from_rational(i64::from(*numerator), i64::from(*denominator));
            Ok(Z3Term::Bool(available.ge(required)))
        }
        Term::PermissionAtMost {
            mask,
            receiver,
            field,
            numerator,
            denominator,
        } => {
            if *denominator == 0 || numerator > denominator {
                return Err(format!(
                    "permission fraction {numerator}/{denominator} is outside [0, 1]"
                ));
            }
            let receiver = as_reference(lower(receiver)?)?;
            let declaration = FuncDecl::new(
                format!("mask::{mask}::field::{field}"),
                &[&reference_sort()],
                &Z3Sort::real(),
            );
            let available = declaration
                .apply(&[&receiver])
                .as_real()
                .ok_or_else(|| "permission mask lowered to a non-real Z3 term".to_owned())?;
            let maximum = Real::from_rational(i64::from(*numerator), i64::from(*denominator));
            Ok(Z3Term::Bool(available.le(maximum)))
        }
        Term::PermissionPositive {
            mask,
            receiver,
            field,
        } => {
            let receiver = as_reference(lower(receiver)?)?;
            let declaration = FuncDecl::new(
                format!("mask::{mask}::field::{field}"),
                &[&reference_sort()],
                &Z3Sort::real(),
            );
            let available = declaration
                .apply(&[&receiver])
                .as_real()
                .ok_or_else(|| "permission mask lowered to a non-real Z3 term".to_owned())?;
            Ok(Z3Term::Bool(available.gt(Real::from_rational(0, 1))))
        }
        Term::PermissionMaskValid { mask, field } => {
            let receiver = Dynamic::new_const(
                format!("permission-mask-valid::{mask}::{field}::receiver"),
                &reference_sort(),
            );
            let declaration = FuncDecl::new(
                format!("mask::{mask}::field::{field}"),
                &[&reference_sort()],
                &Z3Sort::real(),
            );
            let available = declaration
                .apply(&[&receiver])
                .as_real()
                .ok_or_else(|| "permission mask lowered to a non-real Z3 term".to_owned())?;
            let lower = available.ge(Real::from_rational(0, 1));
            let upper = available.le(Real::from_rational(1, 1));
            let body = Bool::and(&[&lower, &upper]);
            Ok(Z3Term::Bool(z3::ast::forall_const(
                &[&receiver],
                &[],
                &body,
            )))
        }
        Term::PermissionMaskTransition {
            pre_mask,
            post_mask,
            field,
            consumed,
            produced,
        } => {
            if pre_mask == post_mask {
                return Err("permission-mask transition must advance the mask".to_owned());
            }
            let receiver = Dynamic::new_const(
                format!("permission-mask-transition::{pre_mask}->{post_mask}::{field}::receiver"),
                &reference_sort(),
            );
            let pre_declaration = FuncDecl::new(
                format!("mask::{pre_mask}::field::{field}"),
                &[&reference_sort()],
                &Z3Sort::real(),
            );
            let post_declaration = FuncDecl::new(
                format!("mask::{post_mask}::field::{field}"),
                &[&reference_sort()],
                &Z3Sort::real(),
            );
            let mut expected = pre_declaration
                .apply(&[&receiver])
                .as_real()
                .ok_or_else(|| "pre-call permission mask lowered to a non-real term".to_owned())?;
            for amount in consumed {
                let amount_receiver = as_reference(lower(&amount.receiver)?)?;
                let fraction =
                    Real::from_rational(i64::from(amount.numerator), i64::from(amount.denominator));
                let delta = receiver
                    .eq(&amount_receiver)
                    .ite(&fraction, &Real::from_rational(0, 1));
                expected -= delta;
            }
            for amount in produced {
                let amount_receiver = as_reference(lower(&amount.receiver)?)?;
                let fraction =
                    Real::from_rational(i64::from(amount.numerator), i64::from(amount.denominator));
                let delta = receiver
                    .eq(&amount_receiver)
                    .ite(&fraction, &Real::from_rational(0, 1));
                expected += delta;
            }
            let post = post_declaration
                .apply(&[&receiver])
                .as_real()
                .ok_or_else(|| "post-call permission mask lowered to a non-real term".to_owned())?;
            let body = post.eq(&expected);
            Ok(Z3Term::Bool(z3::ast::forall_const(
                &[&receiver],
                &[],
                &body,
            )))
        }
        Term::Not { value } => Ok(Z3Term::Bool(as_bool(lower(value)?)?.not())),
        Term::And { values } => {
            let lowered = lower_bools(values)?;
            let references: Vec<&Bool> = lowered.iter().collect();
            Ok(Z3Term::Bool(Bool::and(&references)))
        }
        Term::Or { values } => {
            let lowered = lower_bools(values)?;
            let references: Vec<&Bool> = lowered.iter().collect();
            Ok(Z3Term::Bool(Bool::or(&references)))
        }
        Term::Implies { left, right } => Ok(Z3Term::Bool(
            as_bool(lower(left)?)?.implies(as_bool(lower(right)?)?),
        )),
        Term::IfThenElse {
            condition,
            then_value,
            else_value,
        } => {
            let condition = as_bool(lower(condition)?)?;
            ite_terms(&condition, lower(then_value)?, lower(else_value)?)
        }
        Term::Equal { left, right } => Ok(Z3Term::Bool(equal_terms(lower(left)?, lower(right)?)?)),
        Term::Less { left, right } => Ok(Z3Term::Bool(
            as_int(lower(left)?)?.lt(as_int(lower(right)?)?),
        )),
        Term::LessEqual { left, right } => Ok(Z3Term::Bool(
            as_int(lower(left)?)?.le(as_int(lower(right)?)?),
        )),
        Term::Greater { left, right } => Ok(Z3Term::Bool(
            as_int(lower(left)?)?.gt(as_int(lower(right)?)?),
        )),
        Term::GreaterEqual { left, right } => Ok(Z3Term::Bool(
            as_int(lower(left)?)?.ge(as_int(lower(right)?)?),
        )),
        Term::Add { left, right } => {
            Ok(Z3Term::Int(as_int(lower(left)?)? + as_int(lower(right)?)?))
        }
        Term::Subtract { left, right } => {
            Ok(Z3Term::Int(as_int(lower(left)?)? - as_int(lower(right)?)?))
        }
        Term::Multiply { left, right } => {
            Ok(Z3Term::Int(as_int(lower(left)?)? * as_int(lower(right)?)?))
        }
        Term::FloorDivideByPositive { value, divisor } => {
            if *divisor == 0 {
                return Err("floor-division divisor must be positive".to_owned());
            }
            Ok(Z3Term::Int(
                as_int(lower(value)?)? / Int::from_u64(*divisor),
            ))
        }
        Term::Negate { value } => Ok(Z3Term::Int(-as_int(lower(value)?)?)),
        Term::StringConcat { values } => {
            let lowered = values
                .iter()
                .map(|value| lower(value).and_then(as_string))
                .collect::<Result<Vec<_>, _>>()?;
            match lowered.as_slice() {
                [] => Z3String::from_str("")
                    .map(Z3Term::String)
                    .map_err(|error| format!("invalid empty Z3 string literal: {error}")),
                [value] => Ok(Z3Term::String(value.clone())),
                values => {
                    let references = values.iter().collect::<Vec<_>>();
                    Ok(Z3Term::String(Z3String::concat(&references)))
                }
            }
        }
        Term::StringLength { value } => Ok(Z3Term::Int(as_string(lower(value)?)?.length())),
        Term::BytesConcat { values } => {
            let lowered = values
                .iter()
                .map(|value| lower(value).and_then(as_bytes))
                .collect::<Result<Vec<_>, _>>()?;
            let value = match lowered.as_slice() {
                [] => Seq::empty(&Z3Sort::int()),
                [only] => only.clone(),
                many => Seq::concat(&many.iter().collect::<Vec<_>>()),
            };
            Ok(Z3Term::Bytes(value))
        }
        Term::BytesLength { value } => Ok(Z3Term::Int(as_bytes(lower(value)?)?.length())),
        Term::BytesGet { bytes, index } => {
            let bytes = as_bytes(lower(bytes)?)?;
            let index = as_int(lower(index)?)?;
            bytes
                .nth(index)
                .as_int()
                .map(Z3Term::Int)
                .ok_or_else(|| "bytes element lowered to a non-integer Z3 term".to_owned())
        }
        Term::Tuple { values } => Ok(Z3Term::Tuple(
            values.iter().map(lower).collect::<Result<Vec<_>, _>>()?,
        )),
        Term::TupleGet { tuple, index } => {
            let Z3Term::Tuple(mut values) = lower(tuple)? else {
                return Err("tuple indexing lowered a non-tuple term".to_owned());
            };
            if *index >= values.len() {
                return Err(format!(
                    "tuple index {index} is outside fixed tuple length {}",
                    values.len()
                ));
            }
            Ok(values.remove(*index))
        }
        Term::VariadicTuple {
            element_sort,
            values,
        } => {
            let z3_element_sort = z3_sort(element_sort.clone())?;
            let units = values
                .iter()
                .map(|value| {
                    let lowered = lower(value)?;
                    let dynamic = into_dynamic_element(lowered, element_sort)?;
                    Ok(Seq::unit(&dynamic))
                })
                .collect::<Result<Vec<_>, String>>()?;
            let value = match units.as_slice() {
                [] => Seq::empty(&z3_element_sort),
                [only] => only.clone(),
                many => Seq::concat(&many.iter().collect::<Vec<_>>()),
            };
            Ok(Z3Term::VariadicTuple {
                value,
                element_sort: element_sort.clone(),
            })
        }
        Term::VariadicTupleLength { value } => {
            let Z3Term::VariadicTuple { value, .. } = lower(value)? else {
                return Err("variadic tuple length lowered a non-tuple term".to_owned());
            };
            Ok(Z3Term::Int(value.length()))
        }
        Term::VariadicTupleGet { tuple, index } => {
            let Z3Term::VariadicTuple {
                value,
                element_sort,
            } = lower(tuple)?
            else {
                return Err("variadic tuple indexing lowered a non-tuple term".to_owned());
            };
            let index = as_int(lower(index)?)?;
            dynamic_from_sort(value.nth(index), &element_sort)
        }
        Term::VariadicTupleSlice {
            source,
            lower: slice_lower,
            upper,
            step,
        } => {
            if let Some(concrete) =
                concrete_static_variadic_tuple_slice(source, *slice_lower, *upper, step.get())
            {
                return lower(&concrete);
            }
            let Z3Term::VariadicTuple { element_sort, .. } = lower(source)? else {
                return Err("variadic tuple slicing lowered a non-tuple term".to_owned());
            };
            let symbol =
                structural_symbol("variadic-tuple-slice", &(source, slice_lower, upper, step))?;
            Ok(Z3Term::VariadicTuple {
                value: Seq::new_const(symbol, &z3_sort(element_sort.clone())?),
                element_sort,
            })
        }
        Term::List {
            element_sort,
            values,
        } => {
            let z3_element_sort = z3_sort(element_sort.clone())?;
            let units = values
                .iter()
                .map(|value| {
                    let lowered = lower(value)?;
                    let dynamic = into_dynamic_element(lowered, element_sort)?;
                    Ok(Seq::unit(&dynamic))
                })
                .collect::<Result<Vec<_>, String>>()?;
            let value = match units.as_slice() {
                [] => Seq::empty(&z3_element_sort),
                [only] => only.clone(),
                many => Seq::concat(&many.iter().collect::<Vec<_>>()),
            };
            Ok(Z3Term::List {
                value,
                element_sort: element_sort.clone(),
            })
        }
        Term::ListLength { value } => {
            let Z3Term::List { value, .. } = lower(value)? else {
                return Err("list length lowered a non-list term".to_owned());
            };
            Ok(Z3Term::Int(value.length()))
        }
        Term::ListGet { list, index } => {
            let Z3Term::List {
                value,
                element_sort,
            } = lower(list)?
            else {
                return Err("list indexing lowered a non-list term".to_owned());
            };
            let index = as_int(lower(index)?)?;
            dynamic_from_sort(value.nth(index), &element_sort)
        }
        Term::ListContains { list, value } => {
            let Z3Term::List {
                value: list,
                element_sort,
            } = lower(list)?
            else {
                return Err("list membership lowered a non-list term".to_owned());
            };
            let value = into_dynamic_element(lower(value)?, &element_sort)?;
            Ok(Z3Term::Bool(list.contains(Seq::unit(&value))))
        }
        Term::ListSlice {
            source,
            lower: slice_lower,
            upper,
            step,
        } => {
            if let Some(concrete) =
                concrete_static_list_slice(source, *slice_lower, *upper, step.get())
            {
                return lower(&concrete);
            }
            let Z3Term::List { element_sort, .. } = lower(source)? else {
                return Err("list slicing lowered a non-list term".to_owned());
            };
            let symbol = structural_symbol("list-slice", &(source, slice_lower, upper, step))?;
            Ok(Z3Term::List {
                value: Seq::new_const(symbol, &z3_sort(element_sort.clone())?),
                element_sort,
            })
        }
        Term::ListConcat { left, right } => {
            let Z3Term::List {
                value: left,
                element_sort: left_sort,
            } = lower(left)?
            else {
                return Err("left list concatenation operand lowered to a non-list term".to_owned());
            };
            let Z3Term::List {
                value: right,
                element_sort: right_sort,
            } = lower(right)?
            else {
                return Err(
                    "right list concatenation operand lowered to a non-list term".to_owned(),
                );
            };
            if left_sort != right_sort {
                return Err(
                    "list concatenation operands lowered with different element sorts".to_owned(),
                );
            }
            Ok(Z3Term::List {
                value: Seq::concat(&[&left, &right]),
                element_sort: left_sort,
            })
        }
        Term::ListSum { source } => {
            if let Some(values) = concrete_integer_list(source) {
                let sum = values
                    .into_iter()
                    .fold(Int::from_i64(0), |sum, value| sum + Int::from_i64(value));
                return Ok(Z3Term::Int(sum));
            }
            let Z3Term::List { element_sort, .. } = lower(source)? else {
                return Err("list sum lowered a non-list term".to_owned());
            };
            if element_sort != Sort::Int {
                return Err("list sum lowered a list with non-integer elements".to_owned());
            }
            Ok(Z3Term::Int(Int::new_const(structural_symbol(
                "list-sum", source,
            )?)))
        }
        Term::ListSorted { source } => {
            if let Some(values) = concrete_integer_list(source) {
                return Ok(Z3Term::List {
                    value: integer_sequence(insertion_sort_integers(&values)),
                    element_sort: Sort::Int,
                });
            }
            let Z3Term::List { element_sort, .. } = lower(source)? else {
                return Err("list sorted lowered a non-list term".to_owned());
            };
            if element_sort != Sort::Int {
                return Err("list sorted lowered a list with non-integer elements".to_owned());
            }
            Ok(Z3Term::List {
                value: Seq::new_const(structural_symbol("list-sorted", source)?, &Z3Sort::int()),
                element_sort: Sort::Int,
            })
        }
        Term::ListComprehension {
            id,
            source,
            binder,
            element_sort,
            mapped,
            filter,
        } => lower_sequence_comprehension(
            id,
            source,
            binder,
            element_sort,
            mapped,
            filter.as_deref(),
            false,
        ),
        Term::SetComprehension {
            id,
            source,
            binder,
            element_sort,
            mapped,
            filter,
        } => lower_sequence_comprehension(
            id,
            source,
            binder,
            element_sort,
            mapped,
            filter.as_deref(),
            true,
        ),
        Term::SetLength { value } => {
            let Z3Term::Set { value, .. } = lower(value)? else {
                return Err("set length lowered a non-set term".to_owned());
            };
            Ok(Z3Term::Int(value.length()))
        }
        Term::SetContains { set, value } => {
            let Z3Term::Set {
                value: set,
                element_sort,
            } = lower(set)?
            else {
                return Err("set membership lowered a non-set term".to_owned());
            };
            let value = into_dynamic_element(lower(value)?, &element_sort)?;
            Ok(Z3Term::Bool(set.contains(Seq::unit(&value))))
        }
        Term::DictComprehension {
            id,
            source,
            binder,
            key_sort,
            value_sort,
            key,
            value,
            filter,
        } => lower_dict_comprehension(
            id,
            source,
            binder,
            key_sort,
            value_sort,
            key,
            value,
            filter.as_deref(),
        ),
        Term::DictLength { value } => {
            let Z3Term::Dict { keys, .. } = lower(value)? else {
                return Err("dictionary length lowered a non-dictionary term".to_owned());
            };
            Ok(Z3Term::Int(keys.length()))
        }
        Term::DictContains { dict, key } => {
            let Z3Term::Dict { keys, key_sort, .. } = lower(dict)? else {
                return Err("dictionary membership lowered a non-dictionary term".to_owned());
            };
            let key = into_dynamic_element(lower(key)?, &key_sort)?;
            Ok(Z3Term::Bool(keys.contains(Seq::unit(&key))))
        }
        Term::DictGet { dict, key } => {
            let Z3Term::Dict {
                values,
                key_sort,
                value_sort,
                ..
            } = lower(dict)?
            else {
                return Err("dictionary lookup lowered a non-dictionary term".to_owned());
            };
            let key = into_dynamic_element(lower(key)?, &key_sort)?;
            dynamic_from_sort(values.select(&key), &value_sort)
        }
        Term::ForAll {
            binder,
            binder_sort: Sort::Int,
            body,
        } => {
            let bound = Int::new_const(binder.as_str());
            let body = as_bool(lower(body)?)?;
            Ok(Z3Term::Bool(z3::ast::forall_const(&[&bound], &[], &body)))
        }
        Term::ForAll { binder_sort, .. } => Err(format!(
            "quantifier binder sort {binder_sort:?} is not implemented by the scalar solver"
        )),
        Term::FiniteDict {
            key_sort,
            value_sort,
            entries,
        } => {
            let z3_key_sort = z3_sort(key_sort.clone())?;
            let z3_value_sort = z3_sort(value_sort.clone())?;
            let default_symbol =
                structural_symbol("finite-dict-default", &(key_sort, value_sort, entries))?;
            let mut keys = Vec::with_capacity(entries.len());
            let mut values = Array::new_const(default_symbol, &z3_key_sort, &z3_value_sort);
            for (key, value) in entries {
                let key = into_dynamic_element(lower(key)?, key_sort)?;
                let value = into_dynamic_element(lower(value)?, value_sort)?;
                keys.push(Seq::unit(&key));
                values = values.store(&key, &value);
            }
            let keys = match keys.as_slice() {
                [] => Seq::empty(&z3_key_sort),
                [only] => only.clone(),
                many => Seq::concat(&many.iter().collect::<Vec<_>>()),
            };
            Ok(Z3Term::Dict {
                keys,
                values,
                key_sort: key_sort.clone(),
                value_sort: value_sort.clone(),
            })
        }
        Term::DictKeys { .. } => {
            Err("dictionary-key views cannot be nested scalar values".to_owned())
        }
    }
}

fn lower_sequence_comprehension(
    id: &str,
    source: &Term,
    binder: &str,
    element_sort: &Sort,
    mapped: &Term,
    filter: Option<&Term>,
    unique: bool,
) -> Result<Z3Term, String> {
    let z3_element_sort = z3_sort(element_sort.clone())?;
    if let Some(mapped_values) =
        evaluate_concrete_sequence_comprehension(source, binder, mapped, filter)?
    {
        let concrete = Term::List {
            element_sort: element_sort.clone(),
            values: if unique {
                let mut unique_values = Vec::new();
                for value in mapped_values {
                    if !unique_values.contains(&value) {
                        unique_values.push(value);
                    }
                }
                unique_values
            } else {
                mapped_values
            },
        };
        let Z3Term::List { value, .. } = lower(&concrete)? else {
            unreachable!()
        };
        return if unique {
            Ok(Z3Term::Set {
                value,
                element_sort: element_sort.clone(),
            })
        } else {
            Ok(Z3Term::List {
                value,
                element_sort: element_sort.clone(),
            })
        };
    }
    let symbol = structural_symbol(
        if unique {
            "set-comprehension"
        } else {
            "list-comprehension"
        },
        &(id, source, binder, element_sort, mapped, filter),
    )?;
    let result = Seq::new_const(symbol, &z3_element_sort);
    if unique {
        Ok(Z3Term::Set {
            value: result,
            element_sort: element_sort.clone(),
        })
    } else {
        Ok(Z3Term::List {
            value: result,
            element_sort: element_sort.clone(),
        })
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_dict_comprehension(
    id: &str,
    source: &Term,
    binder: &str,
    key_sort: &Sort,
    value_sort: &Sort,
    key: &Term,
    value: &Term,
    filter: Option<&Term>,
) -> Result<Z3Term, String> {
    let z3_key_sort = z3_sort(key_sort.clone())?;
    let z3_value_sort = z3_sort(value_sort.clone())?;
    if let Some(entries) = evaluate_concrete_dict_comprehension(source, binder, key, value, filter)?
    {
        let mut key_units = Vec::with_capacity(entries.len());
        let default_symbol = structural_symbol(
            "concrete-dict-default",
            &(id, source, binder, key_sort, value_sort, key, value, filter),
        )?;
        let mut values = Array::new_const(default_symbol, &z3_key_sort, &z3_value_sort);
        for (key, value) in entries {
            let key = into_dynamic_element(lower(&key)?, key_sort)?;
            let value = into_dynamic_element(lower(&value)?, value_sort)?;
            key_units.push(Seq::unit(&key));
            values = values.store(&key, &value);
        }
        let keys = match key_units.as_slice() {
            [] => Seq::empty(&z3_key_sort),
            [only] => only.clone(),
            many => Seq::concat(&many.iter().collect::<Vec<_>>()),
        };
        return Ok(Z3Term::Dict {
            keys,
            values,
            key_sort: key_sort.clone(),
            value_sort: value_sort.clone(),
        });
    }
    let symbol = structural_symbol(
        "dict-comprehension",
        &(id, source, binder, key_sort, value_sort, key, value, filter),
    )?;
    Ok(Z3Term::Dict {
        keys: Seq::new_const(format!("{symbol}::keys"), &z3_key_sort),
        values: Array::new_const(format!("{symbol}::values"), &z3_key_sort, &z3_value_sort),
        key_sort: key_sort.clone(),
        value_sort: value_sort.clone(),
    })
}

fn structural_symbol(prefix: &str, value: &impl Serialize) -> Result<String, String> {
    let encoded = serde_json::to_vec(value)
        .map_err(|error| format!("cannot fingerprint {prefix}: {error}"))?;
    let digest = Sha256::digest(encoded);
    Ok(format!("{prefix}::{digest:x}"))
}

fn evaluate_concrete_sequence_comprehension(
    source: &Term,
    binder: &str,
    mapped: &Term,
    filter: Option<&Term>,
) -> Result<Option<Vec<Term>>, String> {
    let Term::List { values, .. } = source else {
        return Ok(None);
    };
    let mut result = Vec::new();
    for source_value in values {
        if let Some(filter) = filter {
            let filter = instantiate_comprehension_term(filter, binder, source_value)?;
            let Some(Term::Bool { value: selected }) = evaluate_constant_term(&filter) else {
                return Ok(None);
            };
            if !selected {
                continue;
            }
        }
        let mapped = instantiate_comprehension_term(mapped, binder, source_value)?;
        let Some(mapped) = evaluate_constant_term(&mapped) else {
            return Ok(None);
        };
        result.push(mapped);
    }
    Ok(Some(result))
}

fn evaluate_concrete_dict_comprehension(
    source: &Term,
    binder: &str,
    key: &Term,
    value: &Term,
    filter: Option<&Term>,
) -> Result<Option<Vec<(Term, Term)>>, String> {
    let Term::List { values, .. } = source else {
        return Ok(None);
    };
    let mut entries = Vec::<(Term, Term)>::new();
    for source_value in values {
        if let Some(filter) = filter {
            let filter = instantiate_comprehension_term(filter, binder, source_value)?;
            let Some(Term::Bool { value: selected }) = evaluate_constant_term(&filter) else {
                return Ok(None);
            };
            if !selected {
                continue;
            }
        }
        let key = instantiate_comprehension_term(key, binder, source_value)?;
        let value = instantiate_comprehension_term(value, binder, source_value)?;
        let Some(key) = evaluate_constant_term(&key) else {
            return Ok(None);
        };
        let Some(value) = evaluate_constant_term(&value) else {
            return Ok(None);
        };
        if let Some((_, existing_value)) = entries.iter_mut().find(|(existing, _)| existing == &key)
        {
            *existing_value = value;
        } else {
            entries.push((key, value));
        }
    }
    Ok(Some(entries))
}

fn evaluate_constant_term(term: &Term) -> Option<Term> {
    fn int(term: &Term) -> Option<i64> {
        match evaluate_constant_term(term)? {
            Term::Int { value } => Some(value),
            _ => None,
        }
    }
    fn boolean(term: &Term) -> Option<bool> {
        match evaluate_constant_term(term)? {
            Term::Bool { value } => Some(value),
            _ => None,
        }
    }
    Some(match term {
        Term::Bool { .. }
        | Term::Int { .. }
        | Term::String { .. }
        | Term::Bytes { .. }
        | Term::NullReference
        | Term::NominalReference { .. } => term.clone(),
        Term::Not { value } => Term::Bool {
            value: !boolean(value)?,
        },
        Term::And { values } => Term::Bool {
            value: values
                .iter()
                .map(boolean)
                .collect::<Option<Vec<_>>>()?
                .into_iter()
                .all(|value| value),
        },
        Term::Or { values } => Term::Bool {
            value: values
                .iter()
                .map(boolean)
                .collect::<Option<Vec<_>>>()?
                .into_iter()
                .any(|value| value),
        },
        Term::IfThenElse {
            condition,
            then_value,
            else_value,
        } => {
            if boolean(condition)? {
                evaluate_constant_term(then_value)?
            } else {
                evaluate_constant_term(else_value)?
            }
        }
        Term::Equal { left, right } => Term::Bool {
            value: evaluate_constant_term(left)? == evaluate_constant_term(right)?,
        },
        Term::Less { left, right } => Term::Bool {
            value: int(left)? < int(right)?,
        },
        Term::LessEqual { left, right } => Term::Bool {
            value: int(left)? <= int(right)?,
        },
        Term::Greater { left, right } => Term::Bool {
            value: int(left)? > int(right)?,
        },
        Term::GreaterEqual { left, right } => Term::Bool {
            value: int(left)? >= int(right)?,
        },
        Term::Add { left, right } => Term::Int {
            value: int(left)?.checked_add(int(right)?)?,
        },
        Term::Subtract { left, right } => Term::Int {
            value: int(left)?.checked_sub(int(right)?)?,
        },
        Term::Multiply { left, right } => Term::Int {
            value: int(left)?.checked_mul(int(right)?)?,
        },
        Term::FloorDivideByPositive { value, divisor } => {
            let divisor = i64::try_from(*divisor).ok().filter(|value| *value > 0)?;
            Term::Int {
                value: int(value)?.div_euclid(divisor),
            }
        }
        Term::Negate { value } => Term::Int {
            value: int(value)?.checked_neg()?,
        },
        Term::ListSlice {
            source,
            lower,
            upper,
            step,
        } => concrete_static_list_slice(source, *lower, *upper, step.get())?,
        Term::VariadicTupleSlice {
            source,
            lower,
            upper,
            step,
        } => concrete_static_variadic_tuple_slice(source, *lower, *upper, step.get())?,
        Term::ListConcat { left, right } => {
            let Term::List {
                element_sort: left_sort,
                values: mut left_values,
            } = evaluate_constant_term(left)?
            else {
                return None;
            };
            let Term::List {
                element_sort: right_sort,
                values: right_values,
            } = evaluate_constant_term(right)?
            else {
                return None;
            };
            if left_sort != right_sort {
                return None;
            }
            left_values.extend(right_values);
            Term::List {
                element_sort: left_sort,
                values: left_values,
            }
        }
        Term::ListSum { source } => Term::Int {
            value: concrete_integer_list(source)?
                .into_iter()
                .try_fold(0_i64, i64::checked_add)?,
        },
        Term::ListSorted { source } => Term::List {
            element_sort: Sort::Int,
            values: insertion_sort_integers(&concrete_integer_list(source)?)
                .into_iter()
                .map(|value| Term::Int { value })
                .collect(),
        },
        Term::Tuple { values } => Term::Tuple {
            values: values
                .iter()
                .map(evaluate_constant_term)
                .collect::<Option<Vec<_>>>()?,
        },
        Term::VariadicTuple {
            element_sort,
            values,
        } => Term::VariadicTuple {
            element_sort: element_sort.clone(),
            values: values
                .iter()
                .map(evaluate_constant_term)
                .collect::<Option<Vec<_>>>()?,
        },
        Term::VariadicTupleLength { value } => {
            let Term::VariadicTuple { values, .. } = evaluate_constant_term(value)? else {
                return None;
            };
            Term::Int {
                value: i64::try_from(values.len()).ok()?,
            }
        }
        Term::VariadicTupleGet { tuple, index } => {
            let Term::VariadicTuple { values, .. } = evaluate_constant_term(tuple)? else {
                return None;
            };
            let index = int(index)?;
            let index = usize::try_from(index).ok()?;
            values.get(index)?.clone()
        }
        _ => return None,
    })
}

fn instantiate_comprehension_term(
    term: &Term,
    binder: &str,
    replacement: &Term,
) -> Result<Term, String> {
    fn unary(term: &Term, binder: &str, replacement: &Term) -> Result<Box<Term>, String> {
        instantiate_comprehension_term(term, binder, replacement).map(Box::new)
    }
    fn binary(
        left: &Term,
        right: &Term,
        binder: &str,
        replacement: &Term,
    ) -> Result<(Box<Term>, Box<Term>), String> {
        Ok((
            unary(left, binder, replacement)?,
            unary(right, binder, replacement)?,
        ))
    }
    Ok(match term {
        Term::Variable { name, .. } if name == binder => replacement.clone(),
        Term::Bool { .. }
        | Term::Int { .. }
        | Term::String { .. }
        | Term::Bytes { .. }
        | Term::Variable { .. } => term.clone(),
        Term::Not { value } => Term::Not {
            value: unary(value, binder, replacement)?,
        },
        Term::Negate { value } => Term::Negate {
            value: unary(value, binder, replacement)?,
        },
        Term::FloorDivideByPositive { value, divisor } => Term::FloorDivideByPositive {
            value: unary(value, binder, replacement)?,
            divisor: *divisor,
        },
        Term::ListSlice {
            source,
            lower,
            upper,
            step,
        } => Term::ListSlice {
            source: unary(source, binder, replacement)?,
            lower: *lower,
            upper: *upper,
            step: *step,
        },
        Term::VariadicTupleSlice {
            source,
            lower,
            upper,
            step,
        } => Term::VariadicTupleSlice {
            source: unary(source, binder, replacement)?,
            lower: *lower,
            upper: *upper,
            step: *step,
        },
        Term::ListSum { source } => Term::ListSum {
            source: unary(source, binder, replacement)?,
        },
        Term::ListSorted { source } => Term::ListSorted {
            source: unary(source, binder, replacement)?,
        },
        Term::And { values } => Term::And {
            values: values
                .iter()
                .map(|v| instantiate_comprehension_term(v, binder, replacement))
                .collect::<Result<_, _>>()?,
        },
        Term::Or { values } => Term::Or {
            values: values
                .iter()
                .map(|v| instantiate_comprehension_term(v, binder, replacement))
                .collect::<Result<_, _>>()?,
        },
        Term::IfThenElse {
            condition,
            then_value,
            else_value,
        } => Term::IfThenElse {
            condition: unary(condition, binder, replacement)?,
            then_value: unary(then_value, binder, replacement)?,
            else_value: unary(else_value, binder, replacement)?,
        },
        Term::Implies { left, right } => {
            let (left, right) = binary(left, right, binder, replacement)?;
            Term::Implies { left, right }
        }
        Term::ListConcat { left, right } => {
            let (left, right) = binary(left, right, binder, replacement)?;
            Term::ListConcat { left, right }
        }
        Term::Equal { left, right } => {
            let (left, right) = binary(left, right, binder, replacement)?;
            Term::Equal { left, right }
        }
        Term::Less { left, right } => {
            let (left, right) = binary(left, right, binder, replacement)?;
            Term::Less { left, right }
        }
        Term::LessEqual { left, right } => {
            let (left, right) = binary(left, right, binder, replacement)?;
            Term::LessEqual { left, right }
        }
        Term::Greater { left, right } => {
            let (left, right) = binary(left, right, binder, replacement)?;
            Term::Greater { left, right }
        }
        Term::GreaterEqual { left, right } => {
            let (left, right) = binary(left, right, binder, replacement)?;
            Term::GreaterEqual { left, right }
        }
        Term::Add { left, right } => {
            let (left, right) = binary(left, right, binder, replacement)?;
            Term::Add { left, right }
        }
        Term::Subtract { left, right } => {
            let (left, right) = binary(left, right, binder, replacement)?;
            Term::Subtract { left, right }
        }
        Term::Multiply { left, right } => {
            let (left, right) = binary(left, right, binder, replacement)?;
            Term::Multiply { left, right }
        }
        _ => {
            return Err(format!(
                "unsupported term {term:?} escaped the pure comprehension frontend"
            ));
        }
    })
}

fn variable_from_sort(name: &str, sort: &Sort) -> Result<Z3Term, String> {
    match sort {
        Sort::Bool => Ok(Z3Term::Bool(Bool::new_const(name))),
        Sort::Int => Ok(Z3Term::Int(Int::new_const(name))),
        Sort::Float => Ok(Z3Term::Float(Dynamic::new_const(name, &float_sort()))),
        Sort::String => Ok(Z3Term::String(Z3String::new_const(name))),
        Sort::Unit => Ok(Z3Term::Unit),
        Sort::Reference => Ok(Z3Term::Reference(Dynamic::new_const(
            name,
            &reference_sort(),
        ))),
        Sort::Class => Ok(Z3Term::Class(Z3String::new_const(name))),
        Sort::Bytes => Ok(Z3Term::Bytes(Seq::new_const(name, &Z3Sort::int()))),
        Sort::Range => Ok(Z3Term::Range(Seq::new_const(name, &Z3Sort::int()))),
        Sort::Tuple(elements) => Ok(Z3Term::Tuple(
            elements
                .iter()
                .enumerate()
                .map(|(index, element)| {
                    variable_from_sort(&format!("{name}::tuple::{index}"), element)
                })
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Sort::VariadicTuple(element) => Ok(Z3Term::VariadicTuple {
            value: Seq::new_const(name, &z3_sort((**element).clone())?),
            element_sort: (**element).clone(),
        }),
        Sort::List(element) => Ok(Z3Term::List {
            value: Seq::new_const(name, &z3_sort((**element).clone())?),
            element_sort: (**element).clone(),
        }),
        Sort::Set(element) => Ok(Z3Term::Set {
            value: Seq::new_const(name, &z3_sort((**element).clone())?),
            element_sort: (**element).clone(),
        }),
        Sort::Dict(key_sort, value_sort) => {
            if !is_z3_collection_key_sort(key_sort) {
                return Err(format!(
                    "symbolic dictionary key sort {:?} is unsupported",
                    key_sort.as_ref()
                ));
            }
            if !is_z3_collection_value_sort(value_sort) {
                return Err(format!(
                    "symbolic dictionary value sort {:?} is unsupported",
                    value_sort.as_ref()
                ));
            }
            let z3_key_sort = z3_sort((**key_sort).clone())?;
            let z3_value_sort = z3_sort((**value_sort).clone())?;
            let symbol = structural_symbol(
                "dict-variable",
                &(name, key_sort.as_ref(), value_sort.as_ref()),
            )?;
            Ok(Z3Term::Dict {
                keys: Seq::new_const(format!("{symbol}::keys"), &z3_key_sort),
                values: Array::new_const(format!("{symbol}::values"), &z3_key_sort, &z3_value_sort),
                key_sort: (**key_sort).clone(),
                value_sort: (**value_sort).clone(),
            })
        }
        Sort::FiniteDict(_, _) | Sort::DictKeys(_) => {
            Err("symbolic finite dictionary variables are outside the scalar VC".to_owned())
        }
    }
}

fn ite_terms(condition: &Bool, then_value: Z3Term, else_value: Z3Term) -> Result<Z3Term, String> {
    match (then_value, else_value) {
        (Z3Term::Bool(then_value), Z3Term::Bool(else_value)) => {
            Ok(Z3Term::Bool(condition.ite(&then_value, &else_value)))
        }
        (Z3Term::Int(then_value), Z3Term::Int(else_value)) => {
            Ok(Z3Term::Int(condition.ite(&then_value, &else_value)))
        }
        (Z3Term::Float(then_value), Z3Term::Float(else_value)) => {
            Ok(Z3Term::Float(condition.ite(&then_value, &else_value)))
        }
        (Z3Term::String(then_value), Z3Term::String(else_value)) => {
            Ok(Z3Term::String(condition.ite(&then_value, &else_value)))
        }
        (Z3Term::Unit, Z3Term::Unit) => Ok(Z3Term::Unit),
        (Z3Term::Reference(then_value), Z3Term::Reference(else_value)) => {
            Ok(Z3Term::Reference(condition.ite(&then_value, &else_value)))
        }
        (Z3Term::Class(then_value), Z3Term::Class(else_value)) => {
            Ok(Z3Term::Class(condition.ite(&then_value, &else_value)))
        }
        (Z3Term::Bytes(then_value), Z3Term::Bytes(else_value)) => {
            Ok(Z3Term::Bytes(condition.ite(&then_value, &else_value)))
        }
        (Z3Term::Range(then_value), Z3Term::Range(else_value)) => {
            Ok(Z3Term::Range(condition.ite(&then_value, &else_value)))
        }
        (Z3Term::Tuple(then_values), Z3Term::Tuple(else_values))
            if then_values.len() == else_values.len() =>
        {
            Ok(Z3Term::Tuple(
                then_values
                    .into_iter()
                    .zip(else_values)
                    .map(|(then_value, else_value)| ite_terms(condition, then_value, else_value))
                    .collect::<Result<Vec<_>, _>>()?,
            ))
        }
        (
            Z3Term::VariadicTuple {
                value: then_value,
                element_sort: then_sort,
            },
            Z3Term::VariadicTuple {
                value: else_value,
                element_sort: else_sort,
            },
        ) if then_sort == else_sort => Ok(Z3Term::VariadicTuple {
            value: condition.ite(&then_value, &else_value),
            element_sort: then_sort,
        }),
        (
            Z3Term::List {
                value: then_value,
                element_sort: then_sort,
            },
            Z3Term::List {
                value: else_value,
                element_sort: else_sort,
            },
        ) if then_sort == else_sort => Ok(Z3Term::List {
            value: condition.ite(&then_value, &else_value),
            element_sort: then_sort,
        }),
        (
            Z3Term::Set {
                value: then_value,
                element_sort: then_sort,
            },
            Z3Term::Set {
                value: else_value,
                element_sort: else_sort,
            },
        ) if then_sort == else_sort => Ok(Z3Term::Set {
            value: condition.ite(&then_value, &else_value),
            element_sort: then_sort,
        }),
        (
            Z3Term::Dict {
                keys: then_keys,
                values: then_values,
                key_sort: then_key_sort,
                value_sort: then_value_sort,
            },
            Z3Term::Dict {
                keys: else_keys,
                values: else_values,
                key_sort: else_key_sort,
                value_sort: else_value_sort,
            },
        ) if then_key_sort == else_key_sort && then_value_sort == else_value_sort => {
            Ok(Z3Term::Dict {
                keys: condition.ite(&then_keys, &else_keys),
                values: condition.ite(&then_values, &else_values),
                key_sort: then_key_sort,
                value_sort: then_value_sort,
            })
        }
        _ => Err("conditional branches have different sorts".to_owned()),
    }
}

fn equal_terms(left: Z3Term, right: Z3Term) -> Result<Bool, String> {
    match (left, right) {
        (Z3Term::Bool(left), Z3Term::Bool(right)) => Ok(left.eq(right)),
        (Z3Term::Int(left), Z3Term::Int(right)) => Ok(left.eq(right)),
        (Z3Term::String(left), Z3Term::String(right)) => Ok(left.eq(right)),
        (Z3Term::Unit, Z3Term::Unit) => Ok(Bool::from_bool(true)),
        (Z3Term::Reference(left), Z3Term::Reference(right)) => Ok(left.eq(right)),
        (Z3Term::Class(left), Z3Term::Class(right)) => Ok(left.eq(right)),
        (Z3Term::Bytes(left), Z3Term::Bytes(right)) => Ok(left.eq(right)),
        (Z3Term::Range(left), Z3Term::Range(right)) => Ok(left.eq(right)),
        (Z3Term::Tuple(left), Z3Term::Tuple(right)) if left.len() == right.len() => {
            let equalities = left
                .into_iter()
                .zip(right)
                .map(|(left, right)| equal_terms(left, right))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Bool::and(&equalities.iter().collect::<Vec<_>>()))
        }
        (
            Z3Term::VariadicTuple {
                value: left,
                element_sort: left_sort,
            },
            Z3Term::VariadicTuple {
                value: right,
                element_sort: right_sort,
            },
        ) if left_sort == right_sort => Ok(left.eq(right)),
        (
            Z3Term::List {
                value: left,
                element_sort: left_sort,
            },
            Z3Term::List {
                value: right,
                element_sort: right_sort,
            },
        ) if left_sort == right_sort => {
            if is_z3_nested_equality_sort(&left_sort) {
                Ok(left.eq(right))
            } else {
                Err(format!(
                    "list equality over nested {left_sort:?} values requires the precise Python element equality model"
                ))
            }
        }
        (Z3Term::Set { .. }, Z3Term::Set { .. }) => Err(
            "set equality requires extensional membership semantics, not sequence equality"
                .to_owned(),
        ),
        (Z3Term::Dict { .. }, Z3Term::Dict { .. }) => {
            Err("dictionary equality requires order-independent key/value semantics".to_owned())
        }
        _ => Err("equality operands have different sorts".to_owned()),
    }
}

fn lower_bools(terms: &[Term]) -> Result<Vec<Bool>, String> {
    terms
        .iter()
        .map(|term| lower(term).and_then(as_bool))
        .collect()
}

fn as_bool(term: Z3Term) -> Result<Bool, String> {
    match term {
        Z3Term::Bool(value) => Ok(value),
        Z3Term::Int(_) => Err("expected boolean term, found integer".to_owned()),
        Z3Term::Float(_) => Err("expected boolean term, found float".to_owned()),
        Z3Term::String(_) => Err("expected boolean term, found string".to_owned()),
        Z3Term::Unit => Err("expected boolean term, found unit".to_owned()),
        Z3Term::Reference(_) => Err("expected boolean term, found reference".to_owned()),
        Z3Term::Class(_) => Err("expected boolean term, found class object".to_owned()),
        Z3Term::Bytes(_) => Err("expected boolean term, found bytes".to_owned()),
        Z3Term::Range(_) => Err("expected boolean term, found range".to_owned()),
        Z3Term::Tuple(_) => Err("expected boolean term, found tuple".to_owned()),
        Z3Term::VariadicTuple { .. } => {
            Err("expected boolean term, found variadic tuple".to_owned())
        }
        Z3Term::List { .. } => Err("expected boolean term, found list".to_owned()),
        Z3Term::Set { .. } => Err("expected boolean term, found set".to_owned()),
        Z3Term::Dict { .. } => Err("expected boolean term, found dictionary".to_owned()),
    }
}

fn as_int(term: Z3Term) -> Result<Int, String> {
    match term {
        Z3Term::Int(value) => Ok(value),
        Z3Term::Bool(_) => Err("expected integer term, found boolean".to_owned()),
        Z3Term::Float(_) => Err("expected integer term, found float".to_owned()),
        Z3Term::String(_) => Err("expected integer term, found string".to_owned()),
        Z3Term::Unit => Err("expected integer term, found unit".to_owned()),
        Z3Term::Reference(_) => Err("expected integer term, found reference".to_owned()),
        Z3Term::Class(_) => Err("expected integer term, found class object".to_owned()),
        Z3Term::Bytes(_) => Err("expected integer term, found bytes".to_owned()),
        Z3Term::Range(_) => Err("expected integer term, found range".to_owned()),
        Z3Term::Tuple(_) => Err("expected integer term, found tuple".to_owned()),
        Z3Term::VariadicTuple { .. } => {
            Err("expected integer term, found variadic tuple".to_owned())
        }
        Z3Term::List { .. } => Err("expected integer term, found list".to_owned()),
        Z3Term::Set { .. } => Err("expected integer term, found set".to_owned()),
        Z3Term::Dict { .. } => Err("expected integer term, found dictionary".to_owned()),
    }
}

fn as_reference(term: Z3Term) -> Result<Dynamic, String> {
    match term {
        Z3Term::Reference(value) => Ok(value),
        Z3Term::Class(_) => Err("expected reference term, found class object".to_owned()),
        Z3Term::Bool(_) => Err("expected reference term, found boolean".to_owned()),
        Z3Term::Int(_) => Err("expected reference term, found integer".to_owned()),
        Z3Term::Float(_) => Err("expected reference term, found float".to_owned()),
        Z3Term::String(_) => Err("expected reference term, found string".to_owned()),
        Z3Term::Bytes(_) => Err("expected reference term, found bytes".to_owned()),
        Z3Term::Range(_) => Err("expected reference term, found range".to_owned()),
        Z3Term::Unit => Err("expected reference term, found unit".to_owned()),
        Z3Term::Tuple(_) => Err("expected reference term, found tuple".to_owned()),
        Z3Term::VariadicTuple { .. } => {
            Err("expected reference term, found variadic tuple".to_owned())
        }
        Z3Term::List { .. } => Err("expected reference term, found list".to_owned()),
        Z3Term::Set { .. } => Err("expected reference term, found set".to_owned()),
        Z3Term::Dict { .. } => Err("expected reference term, found dictionary".to_owned()),
    }
}

fn as_class(term: Z3Term) -> Result<Z3String, String> {
    match term {
        Z3Term::Class(value) => Ok(value),
        Z3Term::Bool(_) => Err("expected class object, found boolean".to_owned()),
        Z3Term::Int(_) => Err("expected class object, found integer".to_owned()),
        Z3Term::Float(_) => Err("expected class object, found float".to_owned()),
        Z3Term::String(_) => Err("expected class object, found string".to_owned()),
        Z3Term::Bytes(_) => Err("expected class object, found bytes".to_owned()),
        Z3Term::Range(_) => Err("expected class object, found range".to_owned()),
        Z3Term::Unit => Err("expected class object, found unit".to_owned()),
        Z3Term::Reference(_) => Err("expected class object, found reference".to_owned()),
        Z3Term::Tuple(_) => Err("expected class object, found tuple".to_owned()),
        Z3Term::VariadicTuple { .. } => {
            Err("expected class object, found variadic tuple".to_owned())
        }
        Z3Term::List { .. } => Err("expected class object, found list".to_owned()),
        Z3Term::Set { .. } => Err("expected class object, found set".to_owned()),
        Z3Term::Dict { .. } => Err("expected class object, found dictionary".to_owned()),
    }
}

fn as_string(term: Z3Term) -> Result<Z3String, String> {
    match term {
        Z3Term::String(value) => Ok(value),
        Z3Term::Bool(_) => Err("expected string term, found boolean".to_owned()),
        Z3Term::Int(_) => Err("expected string term, found integer".to_owned()),
        Z3Term::Float(_) => Err("expected string term, found float".to_owned()),
        Z3Term::Unit => Err("expected string term, found unit".to_owned()),
        Z3Term::Reference(_) => Err("expected string term, found reference".to_owned()),
        Z3Term::Class(_) => Err("expected string term, found class object".to_owned()),
        Z3Term::Bytes(_) => Err("expected string term, found bytes".to_owned()),
        Z3Term::Range(_) => Err("expected string term, found range".to_owned()),
        Z3Term::Tuple(_) => Err("expected string term, found tuple".to_owned()),
        Z3Term::VariadicTuple { .. } => {
            Err("expected string term, found variadic tuple".to_owned())
        }
        Z3Term::List { .. } => Err("expected string term, found list".to_owned()),
        Z3Term::Set { .. } => Err("expected string term, found set".to_owned()),
        Z3Term::Dict { .. } => Err("expected string term, found dictionary".to_owned()),
    }
}

fn as_bytes(term: Z3Term) -> Result<Seq, String> {
    match term {
        Z3Term::Bytes(value) => Ok(value),
        Z3Term::Bool(_) => Err("expected bytes term, found boolean".to_owned()),
        Z3Term::Int(_) => Err("expected bytes term, found integer".to_owned()),
        Z3Term::Float(_) => Err("expected bytes term, found float".to_owned()),
        Z3Term::String(_) => Err("expected bytes term, found string".to_owned()),
        Z3Term::Unit => Err("expected bytes term, found unit".to_owned()),
        Z3Term::Reference(_) => Err("expected bytes term, found reference".to_owned()),
        Z3Term::Class(_) => Err("expected bytes term, found class object".to_owned()),
        Z3Term::Range(_) => Err("expected bytes term, found range".to_owned()),
        Z3Term::Tuple(_) => Err("expected bytes term, found tuple".to_owned()),
        Z3Term::VariadicTuple { .. } => Err("expected bytes term, found variadic tuple".to_owned()),
        Z3Term::List { .. } => Err("expected bytes term, found list".to_owned()),
        Z3Term::Set { .. } => Err("expected bytes term, found set".to_owned()),
        Z3Term::Dict { .. } => Err("expected bytes term, found dictionary".to_owned()),
    }
}

fn reference_sort() -> Z3Sort {
    Z3Sort::uninterpreted("MaledictusReference".into())
}

fn class_sort() -> Z3Sort {
    Z3Sort::string()
}

fn float_sort() -> Z3Sort {
    Z3Sort::uninterpreted("MaledictusPythonFloat".into())
}

fn z3_sort(sort: Sort) -> Result<Z3Sort, String> {
    match sort {
        Sort::Bool => Ok(Z3Sort::bool()),
        Sort::Int => Ok(Z3Sort::int()),
        Sort::Float => Ok(float_sort()),
        Sort::String => Ok(Z3Sort::string()),
        Sort::Reference => Ok(reference_sort()),
        Sort::Class => Ok(class_sort()),
        Sort::Bytes | Sort::Range => Ok(Z3Sort::seq(&Z3Sort::int())),
        Sort::Unit => Err("Unit has no heap-field Z3 sort".to_owned()),
        Sort::Tuple(elements) => tuple_sort(&elements),
        Sort::VariadicTuple(element) => Ok(Z3Sort::seq(&z3_sort(*element)?)),
        Sort::List(element) => Ok(Z3Sort::seq(&z3_sort(*element)?)),
        Sort::Set(element) => Ok(Z3Sort::seq(&z3_sort(*element)?)),
        Sort::Dict(key, value) | Sort::FiniteDict(key, value) => dictionary_sort(&key, &value),
        Sort::DictKeys(_) => {
            Err("dictionary-key views have no nested Z3 representation".to_owned())
        }
    }
}

fn into_dynamic_element(term: Z3Term, expected: &Sort) -> Result<Dynamic, String> {
    match (term, expected) {
        (Z3Term::Bool(value), Sort::Bool) => Ok(value.into()),
        (Z3Term::Int(value), Sort::Int) => Ok(value.into()),
        (Z3Term::String(value), Sort::String) => Ok(value.into()),
        (Z3Term::Reference(value), Sort::Reference) => Ok(value),
        (Z3Term::Class(value), Sort::Class) => Ok(value.into()),
        (Z3Term::Bytes(value), Sort::Bytes) => Ok(value.into()),
        (Z3Term::Tuple(values), Sort::Tuple(elements)) if values.len() == elements.len() => {
            let arguments = values
                .into_iter()
                .zip(elements)
                .map(|(value, sort)| into_dynamic_element(value, sort))
                .collect::<Result<Vec<_>, _>>()?;
            let encoding_name = ensure_tuple_encoding(elements)?;
            TUPLE_ENCODINGS.with(|encodings| {
                let encodings = encodings.borrow();
                let encoding = encodings
                    .get(&encoding_name)
                    .expect("tuple encoding was installed before constructor application");
                let arguments = arguments
                    .iter()
                    .map(|argument| argument as &dyn Ast)
                    .collect::<Vec<_>>();
                Ok(encoding.variants[0].constructor.apply(&arguments))
            })
        }
        (
            Z3Term::VariadicTuple {
                value,
                element_sort,
            },
            Sort::VariadicTuple(expected),
        ) if &element_sort == expected.as_ref() => Ok(value.into()),
        (
            Z3Term::List {
                value,
                element_sort,
            },
            Sort::List(expected),
        ) if &element_sort == expected.as_ref() => Ok(value.into()),
        (
            Z3Term::Set {
                value,
                element_sort,
            },
            Sort::Set(expected),
        ) if &element_sort == expected.as_ref() => Ok(value.into()),
        (
            Z3Term::Dict {
                keys,
                values,
                key_sort,
                value_sort,
            },
            Sort::Dict(expected_key, expected_value)
            | Sort::FiniteDict(expected_key, expected_value),
        ) if &key_sort == expected_key.as_ref() && &value_sort == expected_value.as_ref() => {
            let encoding_name = ensure_dictionary_encoding(expected_key, expected_value)?;
            DICTIONARY_ENCODINGS.with(|encodings| {
                let encodings = encodings.borrow();
                let encoding = encodings
                    .get(&encoding_name)
                    .expect("dictionary encoding was installed before constructor application");
                Ok(encoding.variants[0]
                    .constructor
                    .apply(&[&keys as &dyn Ast, &values as &dyn Ast]))
            })
        }
        _ => Err(format!(
            "collection element did not lower to its declared sort {expected:?}"
        )),
    }
}

fn tuple_encoding_name(elements: &[Sort]) -> Result<String, String> {
    structural_symbol("maledictus-tuple-sort", &elements)
}

fn ensure_tuple_encoding(elements: &[Sort]) -> Result<String, String> {
    let name = tuple_encoding_name(elements)?;
    if TUPLE_ENCODINGS.with(|encodings| encodings.borrow().contains_key(&name)) {
        return Ok(name);
    }

    // Resolve nested tuple field sorts before mutably borrowing the cache: a
    // nested tuple installs its own datatype recursively.
    let field_sorts = elements
        .iter()
        .cloned()
        .map(z3_sort)
        .collect::<Result<Vec<_>, _>>()?;
    let field_names = (0..elements.len())
        .map(|index| format!("field-{index}"))
        .collect::<Vec<_>>();
    let fields = field_names
        .iter()
        .zip(field_sorts)
        .map(|(field, sort)| (field.as_str(), DatatypeAccessor::Sort(sort)))
        .collect::<Vec<_>>();
    let encoding = DatatypeBuilder::new(name.clone())
        .variant("tuple", fields)
        .finish();
    TUPLE_ENCODINGS.with(|encodings| {
        encodings
            .borrow_mut()
            .entry(name.clone())
            .or_insert(encoding);
    });
    Ok(name)
}

fn tuple_sort(elements: &[Sort]) -> Result<Z3Sort, String> {
    let name = ensure_tuple_encoding(elements)?;
    TUPLE_ENCODINGS.with(|encodings| {
        Ok(encodings
            .borrow()
            .get(&name)
            .expect("tuple encoding was installed before sort lookup")
            .sort
            .clone())
    })
}

fn dictionary_encoding_name(key: &Sort, value: &Sort) -> Result<String, String> {
    structural_symbol("maledictus-dictionary-sort", &(key, value))
}

fn ensure_dictionary_encoding(key: &Sort, value: &Sort) -> Result<String, String> {
    let name = dictionary_encoding_name(key, value)?;
    if DICTIONARY_ENCODINGS.with(|encodings| encodings.borrow().contains_key(&name)) {
        return Ok(name);
    }
    let key_sort = z3_sort(key.clone())?;
    let value_sort = z3_sort(value.clone())?;
    let encoding = DatatypeBuilder::new(name.clone())
        .variant(
            "dictionary",
            vec![
                ("keys", DatatypeAccessor::Sort(Z3Sort::seq(&key_sort))),
                (
                    "values",
                    DatatypeAccessor::Sort(Z3Sort::array(&key_sort, &value_sort)),
                ),
            ],
        )
        .finish();
    DICTIONARY_ENCODINGS.with(|encodings| {
        encodings
            .borrow_mut()
            .entry(name.clone())
            .or_insert(encoding);
    });
    Ok(name)
}

fn dictionary_sort(key: &Sort, value: &Sort) -> Result<Z3Sort, String> {
    let name = ensure_dictionary_encoding(key, value)?;
    DICTIONARY_ENCODINGS.with(|encodings| {
        Ok(encodings
            .borrow()
            .get(&name)
            .expect("dictionary encoding was installed before sort lookup")
            .sort
            .clone())
    })
}

fn into_predicate_argument(term: Z3Term, expected: &Sort) -> Result<Dynamic, String> {
    match (term, expected) {
        (Z3Term::Bool(value), Sort::Bool) => Ok(value.into()),
        (Z3Term::Int(value), Sort::Int) => Ok(value.into()),
        (Z3Term::String(value), Sort::String) => Ok(value.into()),
        (Z3Term::Reference(value), Sort::Reference) => Ok(value),
        (Z3Term::Class(value), Sort::Class) => Ok(value.into()),
        _ => Err(format!(
            "predicate argument did not lower to its declared sort {expected:?}"
        )),
    }
}

fn predicate_instance_symbol(predicate: &str, argument_sorts: &[Sort]) -> String {
    format!("predicate-instance::{predicate}::{argument_sorts:?}")
}

fn assert_predicate_instance_axioms(solver: &Solver, term: &Term) -> Result<(), String> {
    assert_comprehension_axioms(solver, term)?;
    assert_set_uniqueness_axiom(solver, term)?;
    assert_list_slice_axioms(solver, term)?;
    assert_variadic_tuple_slice_axioms(solver, term)?;
    assert_list_builtin_axioms(solver, term)?;
    if let Term::PredicateInstance {
        predicate,
        arguments,
    } = term
    {
        let argument_sorts = arguments
            .iter()
            .map(Term::sort)
            .collect::<Result<Vec<_>, _>>()?;
        let instance = as_reference(lower(term)?)?;
        for (index, (argument, sort)) in arguments.iter().zip(&argument_sorts).enumerate() {
            let projection = FuncDecl::new(
                format!("predicate-instance-projection::{predicate}::{argument_sorts:?}::{index}"),
                &[&reference_sort()],
                &z3_sort(sort.clone())?,
            );
            let projected = projection.apply(&[&instance]);
            let actual = into_predicate_argument(lower(argument)?, sort)?;
            solver.assert(projected.eq(actual));
        }
    }
    match term {
        Term::PredicateInstance { arguments, .. }
        | Term::And { values: arguments }
        | Term::Or { values: arguments }
        | Term::StringConcat { values: arguments }
        | Term::BytesConcat { values: arguments }
        | Term::Tuple { values: arguments }
        | Term::VariadicTuple {
            values: arguments, ..
        }
        | Term::List {
            values: arguments, ..
        }
        | Term::DictKeys {
            values: arguments, ..
        } => {
            for argument in arguments {
                assert_predicate_instance_axioms(solver, argument)?;
            }
        }
        Term::RuntimeClass { value }
        | Term::IntEnumValue { value, .. }
        | Term::IntEnumProjection { value }
        | Term::IntEnumDomain { value }
        | Term::FieldRead {
            receiver: value, ..
        }
        | Term::PermissionAtLeast {
            receiver: value, ..
        }
        | Term::PermissionAtMost {
            receiver: value, ..
        }
        | Term::PermissionPositive {
            receiver: value, ..
        }
        | Term::Not { value }
        | Term::FloorDivideByPositive { value, .. }
        | Term::Negate { value }
        | Term::StringLength { value }
        | Term::BytesLength { value }
        | Term::TupleGet { tuple: value, .. }
        | Term::VariadicTupleLength { value }
        | Term::VariadicTupleSlice { source: value, .. }
        | Term::ListLength { value }
        | Term::ListSlice { source: value, .. }
        | Term::ListSum { source: value }
        | Term::ListSorted { source: value }
        | Term::SetLength { value }
        | Term::DictLength { value }
        | Term::ForAll { body: value, .. } => assert_predicate_instance_axioms(solver, value)?,
        Term::ClassSubtype {
            actual: left,
            expected: right,
        }
        | Term::Implies { left, right }
        | Term::Equal { left, right }
        | Term::Less { left, right }
        | Term::LessEqual { left, right }
        | Term::Greater { left, right }
        | Term::GreaterEqual { left, right }
        | Term::Add { left, right }
        | Term::Subtract { left, right }
        | Term::Multiply { left, right }
        | Term::IntEnumIdentity { left, right }
        | Term::BytesGet {
            bytes: left,
            index: right,
        }
        | Term::VariadicTupleGet {
            tuple: left,
            index: right,
        }
        | Term::ListGet {
            list: left,
            index: right,
        }
        | Term::ListContains {
            list: left,
            value: right,
        }
        | Term::ListConcat { left, right }
        | Term::SetContains {
            set: left,
            value: right,
        }
        | Term::DictContains {
            dict: left,
            key: right,
        }
        | Term::DictGet {
            dict: left,
            key: right,
        } => {
            assert_predicate_instance_axioms(solver, left)?;
            assert_predicate_instance_axioms(solver, right)?;
        }
        Term::IfThenElse {
            condition,
            then_value,
            else_value,
        } => {
            assert_predicate_instance_axioms(solver, condition)?;
            assert_predicate_instance_axioms(solver, then_value)?;
            assert_predicate_instance_axioms(solver, else_value)?;
        }
        Term::PermissionMaskTransition {
            consumed, produced, ..
        } => {
            for amount in consumed.iter().chain(produced) {
                assert_predicate_instance_axioms(solver, &amount.receiver)?;
            }
        }
        Term::FiniteDict { entries, .. } => {
            for (key, value) in entries {
                assert_predicate_instance_axioms(solver, key)?;
                assert_predicate_instance_axioms(solver, value)?;
            }
        }
        Term::ListComprehension {
            source,
            mapped,
            filter,
            ..
        }
        | Term::SetComprehension {
            source,
            mapped,
            filter,
            ..
        } => {
            assert_predicate_instance_axioms(solver, source)?;
            assert_predicate_instance_axioms(solver, mapped)?;
            if let Some(filter) = filter {
                assert_predicate_instance_axioms(solver, filter)?;
            }
        }
        Term::DictComprehension {
            source,
            key,
            value,
            filter,
            ..
        } => {
            assert_predicate_instance_axioms(solver, source)?;
            assert_predicate_instance_axioms(solver, key)?;
            assert_predicate_instance_axioms(solver, value)?;
            if let Some(filter) = filter {
                assert_predicate_instance_axioms(solver, filter)?;
            }
        }
        Term::Bool { .. }
        | Term::Int { .. }
        | Term::String { .. }
        | Term::Bytes { .. }
        | Term::Range { .. }
        | Term::Unit
        | Term::NullReference
        | Term::NominalReference { .. }
        | Term::ClassLiteral { .. }
        | Term::Variable { .. }
        | Term::PermissionMaskValid { .. } => {}
    }
    Ok(())
}

fn assert_set_uniqueness_axiom(solver: &Solver, term: &Term) -> Result<(), String> {
    if !matches!(
        term,
        Term::Variable {
            sort: Sort::Set(_),
            ..
        } | Term::SetComprehension { .. }
    ) {
        return Ok(());
    }
    let Z3Term::Set { value, .. } = lower(term)? else {
        return Err("set uniqueness axiom lowered a non-set term".to_owned());
    };
    let fingerprint = structural_symbol("set-unique", term)?;
    let left = Int::new_const(format!("{fingerprint}::left"));
    let right = Int::new_const(format!("{fingerprint}::right"));
    let in_bounds = Bool::and(&[
        &left.ge(Int::from_i64(0)),
        &left.lt(value.length()),
        &right.ge(Int::from_i64(0)),
        &right.lt(value.length()),
        &left.eq(&right).not(),
    ]);
    let distinct = value.nth(left.clone()).eq(value.nth(right.clone())).not();
    solver.assert(z3::ast::forall_const(
        &[&left, &right],
        &[],
        &in_bounds.implies(distinct),
    ));
    Ok(())
}

fn assert_list_slice_axioms(solver: &Solver, term: &Term) -> Result<(), String> {
    let Term::ListSlice {
        source,
        lower: slice_lower,
        upper,
        step,
    } = term
    else {
        return Ok(());
    };
    let Z3Term::List {
        value: source_value,
        ..
    } = lower(source)?
    else {
        return Err("list slice axiom source lowered to a non-list term".to_owned());
    };
    let Z3Term::List {
        value: result_value,
        ..
    } = lower(term)?
    else {
        return Err("list slice axiom result lowered to a non-list term".to_owned());
    };
    let (start, result_length) =
        normalized_static_slice(&source_value.length(), *slice_lower, *upper, step.get())?;
    solver.assert(result_value.length().eq(&result_length));

    let fingerprint = structural_symbol("list-slice-axiom", &(source, slice_lower, upper, step))?;
    let result_index = Int::new_const(format!("{fingerprint}::result-index"));
    let valid_result_index = Bool::and(&[
        &result_index.ge(Int::from_i64(0)),
        &result_index.lt(result_length),
    ]);
    let source_index = start + result_index.clone() * int_from_i128(step.get())?;
    let same_element = result_value
        .nth(result_index.clone())
        .eq(source_value.nth(source_index));
    solver.assert(z3::ast::forall_const(
        &[&result_index],
        &[],
        &valid_result_index.implies(&same_element),
    ));
    Ok(())
}

fn assert_variadic_tuple_slice_axioms(solver: &Solver, term: &Term) -> Result<(), String> {
    let Term::VariadicTupleSlice {
        source,
        lower: slice_lower,
        upper,
        step,
    } = term
    else {
        return Ok(());
    };
    let Z3Term::VariadicTuple {
        value: source_value,
        ..
    } = lower(source)?
    else {
        return Err("variadic tuple slice axiom source lowered to a non-tuple term".to_owned());
    };
    let Z3Term::VariadicTuple {
        value: result_value,
        ..
    } = lower(term)?
    else {
        return Err("variadic tuple slice axiom result lowered to a non-tuple term".to_owned());
    };
    let (start, result_length) =
        normalized_static_slice(&source_value.length(), *slice_lower, *upper, step.get())?;
    solver.assert(result_value.length().eq(&result_length));

    let fingerprint = structural_symbol(
        "variadic-tuple-slice-axiom",
        &(source, slice_lower, upper, step),
    )?;
    let result_index = Int::new_const(format!("{fingerprint}::result-index"));
    let valid_result_index = Bool::and(&[
        &result_index.ge(Int::from_i64(0)),
        &result_index.lt(result_length),
    ]);
    let source_index = start + result_index.clone() * int_from_i128(step.get())?;
    let same_element = result_value
        .nth(result_index.clone())
        .eq(source_value.nth(source_index));
    solver.assert(z3::ast::forall_const(
        &[&result_index],
        &[],
        &valid_result_index.implies(&same_element),
    ));
    Ok(())
}

fn assert_list_builtin_axioms(solver: &Solver, term: &Term) -> Result<(), String> {
    match term {
        Term::ListSum { source } if concrete_integer_list(source).is_none() => {
            let Z3Term::List {
                value: source_value,
                element_sort: Sort::Int,
            } = lower(source)?
            else {
                return Err("list sum axiom source lowered outside List[Int]".to_owned());
            };
            let result = as_int(lower(term)?)?;
            let fingerprint = structural_symbol("list-sum-definition", source)?;
            let definition = format!(
                "{fingerprint}::{}",
                RECURSIVE_DEFINITION_ID.fetch_add(1, Ordering::Relaxed)
            );
            let sequence_sort = Z3Sort::seq(&Z3Sort::int());
            let sum = RecFuncDecl::new(
                format!("{definition}::prefix-sum"),
                &[&sequence_sort, &Z3Sort::int()],
                &Z3Sort::int(),
            );
            let sequence = Seq::new_const(format!("{definition}::sequence"), &Z3Sort::int());
            let count = Int::new_const(format!("{definition}::count"));
            let previous_count = count.clone() - Int::from_i64(1);
            let previous_sum = sum
                .apply(&[&sequence, &previous_count])
                .as_int()
                .ok_or_else(|| "list sum recursive result is not an integer".to_owned())?;
            let element = sequence
                .nth(previous_count)
                .as_int()
                .ok_or_else(|| "List[Int] sum selected a non-integer element".to_owned())?;
            let body = count
                .le(Int::from_i64(0))
                .ite(&Int::from_i64(0), &(previous_sum + element));
            sum.add_def(&[&sequence, &count], &body);
            let exact = sum
                .apply(&[&source_value, &source_value.length()])
                .as_int()
                .ok_or_else(|| "list sum application is not an integer".to_owned())?;
            solver.assert(result.eq(exact));
            if let Term::ListConcat { left, right } = source.as_ref() {
                let left_sum = as_int(lower(&Term::ListSum {
                    source: left.clone(),
                })?)?;
                let right_sum = as_int(lower(&Term::ListSum {
                    source: right.clone(),
                })?)?;
                solver.assert(result.eq(left_sum + right_sum));
            }
        }
        Term::ListSorted { source } if concrete_integer_list(source).is_none() => {
            let Z3Term::List {
                value: source_value,
                element_sort: Sort::Int,
            } = lower(source)?
            else {
                return Err("list sorted axiom source lowered outside List[Int]".to_owned());
            };
            let Z3Term::List {
                value: result_value,
                element_sort: Sort::Int,
            } = lower(term)?
            else {
                return Err("list sorted axiom result lowered outside List[Int]".to_owned());
            };
            let fingerprint = structural_symbol("list-sorted-definition", source)?;
            let definition = format!(
                "{fingerprint}::{}",
                RECURSIVE_DEFINITION_ID.fetch_add(1, Ordering::Relaxed)
            );
            let sequence_sort = Z3Sort::seq(&Z3Sort::int());

            let take = RecFuncDecl::new(
                format!("{definition}::take"),
                &[&sequence_sort, &Z3Sort::int()],
                &sequence_sort,
            );
            let take_sequence =
                Seq::new_const(format!("{definition}::take-sequence"), &Z3Sort::int());
            let take_count = Int::new_const(format!("{definition}::take-count"));
            let take_previous_count = take_count.clone() - Int::from_i64(1);
            let take_previous = take
                .apply(&[&take_sequence, &take_previous_count])
                .as_seq()
                .ok_or_else(|| "list sorted take recursion did not return a sequence".to_owned())?;
            let take_last = take_sequence
                .nth(take_previous_count)
                .as_int()
                .ok_or_else(|| "list sorted take selected a non-integer element".to_owned())?;
            let take_step = Seq::concat(&[&take_previous, &Seq::unit(&take_last)]);
            let take_body = take_count
                .le(Int::from_i64(0))
                .ite(&Seq::empty(&Z3Sort::int()), &take_step);
            take.add_def(&[&take_sequence, &take_count], &take_body);

            let insert = RecFuncDecl::new(
                format!("{definition}::insert"),
                &[&sequence_sort, &Z3Sort::int(), &Z3Sort::int()],
                &sequence_sort,
            );
            let insert_sequence =
                Seq::new_const(format!("{definition}::insert-sequence"), &Z3Sort::int());
            let insert_value = Int::new_const(format!("{definition}::insert-value"));
            let insert_count = Int::new_const(format!("{definition}::insert-count"));
            let insert_previous_count = insert_count.clone() - Int::from_i64(1);
            let insert_last = insert_sequence
                .nth(insert_previous_count.clone())
                .as_int()
                .ok_or_else(|| "list sorted insert selected a non-integer element".to_owned())?;
            let insert_at_end_prefix = take
                .apply(&[&insert_sequence, &insert_count])
                .as_seq()
                .ok_or_else(|| {
                    "list sorted take application did not return a sequence".to_owned()
                })?;
            let insert_at_end = Seq::concat(&[&insert_at_end_prefix, &Seq::unit(&insert_value)]);
            let insert_before_last_prefix = insert
                .apply(&[&insert_sequence, &insert_value, &insert_previous_count])
                .as_seq()
                .ok_or_else(|| {
                    "list sorted insert recursion did not return a sequence".to_owned()
                })?;
            let insert_before_last =
                Seq::concat(&[&insert_before_last_prefix, &Seq::unit(&insert_last)]);
            let insert_nonempty = insert_last
                .le(&insert_value)
                .ite(&insert_at_end, &insert_before_last);
            let insert_body = insert_count
                .le(Int::from_i64(0))
                .ite(&Seq::unit(&insert_value), &insert_nonempty);
            insert.add_def(
                &[&insert_sequence, &insert_value, &insert_count],
                &insert_body,
            );

            let sort = RecFuncDecl::new(
                format!("{definition}::sort"),
                &[&sequence_sort, &Z3Sort::int()],
                &sequence_sort,
            );
            let sort_source = Seq::new_const(format!("{definition}::sort-source"), &Z3Sort::int());
            let sort_count = Int::new_const(format!("{definition}::sort-count"));
            let sort_previous_count = sort_count.clone() - Int::from_i64(1);
            let sort_previous = sort
                .apply(&[&sort_source, &sort_previous_count])
                .as_seq()
                .ok_or_else(|| "list sorted recursion did not return a sequence".to_owned())?;
            let sort_value = sort_source
                .nth(sort_previous_count.clone())
                .as_int()
                .ok_or_else(|| "list sorted selected a non-integer element".to_owned())?;
            let sort_step = insert
                .apply(&[&sort_previous, &sort_value, &sort_previous_count])
                .as_seq()
                .ok_or_else(|| {
                    "list sorted insert application did not return a sequence".to_owned()
                })?;
            let sort_body = sort_count
                .le(Int::from_i64(0))
                .ite(&Seq::empty(&Z3Sort::int()), &sort_step);
            sort.add_def(&[&sort_source, &sort_count], &sort_body);
            let exact = sort
                .apply(&[&source_value, &source_value.length()])
                .as_seq()
                .ok_or_else(|| "list sorted application did not return a sequence".to_owned())?;
            solver.assert(result_value.eq(exact));
            solver.assert(result_value.length().eq(source_value.length()));
            let adjacent_index = Int::new_const(format!("{definition}::adjacent-index"));
            let has_successor = Bool::and(&[
                &adjacent_index.ge(Int::from_i64(0)),
                &(adjacent_index.clone() + Int::from_i64(1)).lt(result_value.length()),
            ]);
            let current = result_value
                .nth(adjacent_index.clone())
                .as_int()
                .ok_or_else(|| "list sorted output contained a non-integer".to_owned())?;
            let next = result_value
                .nth(adjacent_index.clone() + Int::from_i64(1))
                .as_int()
                .ok_or_else(|| "list sorted output contained a non-integer".to_owned())?;
            solver.assert(z3::ast::forall_const(
                &[&adjacent_index],
                &[],
                &has_successor.implies(current.le(next)),
            ));
        }
        _ => {}
    }
    Ok(())
}

fn assert_comprehension_axioms(solver: &Solver, term: &Term) -> Result<(), String> {
    match term {
        Term::ListComprehension {
            source,
            binder,
            element_sort,
            mapped,
            filter,
            ..
        }
        | Term::SetComprehension {
            source,
            binder,
            element_sort,
            mapped,
            filter,
            ..
        } => {
            let unique = matches!(term, Term::SetComprehension { .. });
            let Z3Term::List {
                value: source_value,
                ..
            } = lower(source)?
            else {
                return Err("comprehension axiom source lowered to a non-list term".to_owned());
            };
            let result_value = match lower(term)? {
                Z3Term::List { value, .. } | Z3Term::Set { value, .. } => value,
                _ => {
                    return Err(
                        "comprehension axiom result lowered to a non-sequence term".to_owned()
                    );
                }
            };
            let fingerprint = structural_symbol("comprehension-axiom", term)?;
            let index_name = format!("{fingerprint}::index");
            let index = Int::new_const(index_name.as_str());
            let replacement = Term::ListGet {
                list: source.clone(),
                index: Box::new(Term::Variable {
                    name: index_name,
                    sort: Sort::Int,
                }),
            };
            let mapped = instantiate_comprehension_term(mapped, binder, &replacement)?;
            let mapped = into_dynamic_element(lower(&mapped)?, element_sort)?;
            let valid = Bool::and(&[
                &index.ge(Int::from_i64(0)),
                &index.lt(source_value.length()),
            ]);
            let selected = match filter {
                Some(filter) => {
                    let filter = instantiate_comprehension_term(filter, binder, &replacement)?;
                    Bool::and(&[&valid, &as_bool(lower(&filter)?)?])
                }
                None => valid,
            };
            let semantic_fact = if !unique && filter.is_none() {
                result_value.nth(index.clone()).eq(&mapped)
            } else {
                result_value.contains(Seq::unit(&mapped))
            };
            solver.assert(z3::ast::forall_const(
                &[&index],
                &[],
                &selected.implies(&semantic_fact),
            ));
            if !unique && filter.is_none() {
                solver.assert(result_value.length().eq(source_value.length()));
            } else {
                solver.assert(result_value.length().ge(Int::from_i64(0)));
                solver.assert(result_value.length().le(source_value.length()));
            }
        }
        Term::DictComprehension {
            source,
            binder,
            key_sort,
            value_sort,
            key,
            value,
            filter,
            ..
        } => {
            let Z3Term::List {
                value: source_value,
                ..
            } = lower(source)?
            else {
                return Err("dictionary axiom source lowered to a non-list term".to_owned());
            };
            let Z3Term::Dict { keys, values, .. } = lower(term)? else {
                return Err("dictionary axiom result lowered to a non-dictionary term".to_owned());
            };
            let fingerprint = structural_symbol("dict-comprehension-axiom", term)?;
            let index_name = format!("{fingerprint}::index");
            let index = Int::new_const(index_name.as_str());
            let replacement = Term::ListGet {
                list: source.clone(),
                index: Box::new(Term::Variable {
                    name: index_name,
                    sort: Sort::Int,
                }),
            };
            let mapped_key = instantiate_comprehension_term(key, binder, &replacement)?;
            let mapped_value = instantiate_comprehension_term(value, binder, &replacement)?;
            let mapped_key = into_dynamic_element(lower(&mapped_key)?, key_sort)?;
            let _mapped_value = into_dynamic_element(lower(&mapped_value)?, value_sort)?;
            let valid = Bool::and(&[
                &index.ge(Int::from_i64(0)),
                &index.lt(source_value.length()),
            ]);
            let selected = match filter {
                Some(filter) => {
                    let filter = instantiate_comprehension_term(filter, binder, &replacement)?;
                    Bool::and(&[&valid, &as_bool(lower(&filter)?)?])
                }
                None => valid,
            };
            solver.assert(z3::ast::forall_const(
                &[&index],
                &[],
                &selected.implies(keys.contains(Seq::unit(&mapped_key))),
            ));
            solver.assert(keys.length().ge(Int::from_i64(0)));
            solver.assert(keys.length().le(source_value.length()));

            let last_index_term = Term::Subtract {
                left: Box::new(Term::ListLength {
                    value: source.clone(),
                }),
                right: Box::new(Term::Int { value: 1 }),
            };
            let last_replacement = Term::ListGet {
                list: source.clone(),
                index: Box::new(last_index_term),
            };
            let last_key = instantiate_comprehension_term(key, binder, &last_replacement)?;
            let last_value = instantiate_comprehension_term(value, binder, &last_replacement)?;
            let last_key = into_dynamic_element(lower(&last_key)?, key_sort)?;
            let last_value = into_dynamic_element(lower(&last_value)?, value_sort)?;
            let mut last_selected = source_value.length().gt(Int::from_i64(0));
            if let Some(filter) = filter {
                let last_filter =
                    instantiate_comprehension_term(filter, binder, &last_replacement)?;
                last_selected = Bool::and(&[&last_selected, &as_bool(lower(&last_filter)?)?]);
            }
            solver.assert(last_selected.implies(values.select(&last_key).eq(last_value)));
        }
        _ => {}
    }
    Ok(())
}

fn dynamic_from_sort(value: Dynamic, sort: &Sort) -> Result<Z3Term, String> {
    match sort {
        Sort::Bool => value
            .as_bool()
            .map(Z3Term::Bool)
            .ok_or_else(|| "list element lowered to a non-boolean Z3 term".to_owned()),
        Sort::Int => value
            .as_int()
            .map(Z3Term::Int)
            .ok_or_else(|| "list element lowered to a non-integer Z3 term".to_owned()),
        Sort::Float => Ok(Z3Term::Float(value)),
        Sort::String => value
            .as_string()
            .map(Z3Term::String)
            .ok_or_else(|| "list element lowered to a non-string Z3 term".to_owned()),
        Sort::Reference => Ok(Z3Term::Reference(value)),
        Sort::Class => value
            .as_string()
            .map(Z3Term::Class)
            .ok_or_else(|| "list element lowered to a non-class Z3 term".to_owned()),
        Sort::Bytes => value
            .as_seq()
            .map(Z3Term::Bytes)
            .ok_or_else(|| "list element lowered to a non-bytes Z3 term".to_owned()),
        Sort::Tuple(elements) => {
            let encoding_name = ensure_tuple_encoding(elements)?;
            let projected = TUPLE_ENCODINGS.with(|encodings| {
                let encodings = encodings.borrow();
                let encoding = encodings
                    .get(&encoding_name)
                    .expect("tuple encoding was installed before accessor application");
                encoding.variants[0]
                    .accessors
                    .iter()
                    .map(|accessor| accessor.apply(&[&value]))
                    .collect::<Vec<_>>()
            });
            Ok(Z3Term::Tuple(
                projected
                    .into_iter()
                    .zip(elements)
                    .map(|(field, sort)| dynamic_from_sort(field, sort))
                    .collect::<Result<Vec<_>, _>>()?,
            ))
        }
        Sort::VariadicTuple(element_sort) => value
            .as_seq()
            .map(|value| Z3Term::VariadicTuple {
                value,
                element_sort: (**element_sort).clone(),
            })
            .ok_or_else(|| "variadic tuple element lowered to a non-sequence Z3 term".to_owned()),
        Sort::List(element_sort) => value
            .as_seq()
            .map(|value| Z3Term::List {
                value,
                element_sort: (**element_sort).clone(),
            })
            .ok_or_else(|| "nested list element lowered to a non-sequence Z3 term".to_owned()),
        Sort::Set(element_sort) => value
            .as_seq()
            .map(|value| Z3Term::Set {
                value,
                element_sort: (**element_sort).clone(),
            })
            .ok_or_else(|| "nested set element lowered to a non-sequence Z3 term".to_owned()),
        Sort::Dict(key_sort, value_sort) | Sort::FiniteDict(key_sort, value_sort) => {
            let encoding_name = ensure_dictionary_encoding(key_sort, value_sort)?;
            let (keys, values) = DICTIONARY_ENCODINGS.with(|encodings| {
                let encodings = encodings.borrow();
                let encoding = encodings
                    .get(&encoding_name)
                    .expect("dictionary encoding was installed before accessor application");
                (
                    encoding.variants[0].accessors[0].apply(&[&value]),
                    encoding.variants[0].accessors[1].apply(&[&value]),
                )
            });
            Ok(Z3Term::Dict {
                keys: keys
                    .as_seq()
                    .ok_or_else(|| "nested dictionary keys lowered to a non-sequence".to_owned())?,
                values: values
                    .as_array()
                    .ok_or_else(|| "nested dictionary values lowered to a non-array".to_owned())?,
                key_sort: (**key_sort).clone(),
                value_sort: (**value_sort).clone(),
            })
        }
        Sort::Unit | Sort::Range | Sort::DictKeys(_) => Err(format!(
            "unsupported collection element sort {sort:?} reached Z3 lowering"
        )),
    }
}

fn is_z3_collection_key_sort(sort: &Sort) -> bool {
    match sort {
        Sort::Bool | Sort::Int | Sort::String | Sort::Bytes => true,
        Sort::Tuple(elements) => {
            let mut valid = true;
            for element in elements {
                if valid {
                    valid = is_z3_collection_key_sort(element);
                }
            }
            valid
        }
        Sort::VariadicTuple(element) => is_z3_collection_key_sort(element),
        _ => false,
    }
}

fn is_z3_collection_value_sort(sort: &Sort) -> bool {
    match sort {
        Sort::Bool | Sort::Int | Sort::String | Sort::Reference | Sort::Bytes => true,
        Sort::Tuple(elements) => {
            let mut valid = true;
            for element in elements {
                if valid {
                    valid = is_z3_collection_value_sort(element);
                }
            }
            valid
        }
        Sort::VariadicTuple(element) | Sort::List(element) => is_z3_collection_value_sort(element),
        Sort::Set(element) => is_z3_collection_key_sort(element),
        Sort::Dict(key, value) | Sort::FiniteDict(key, value) => {
            is_z3_collection_key_sort(key) && is_z3_collection_value_sort(value)
        }
        _ => false,
    }
}

fn is_z3_nested_equality_sort(sort: &Sort) -> bool {
    match sort {
        Sort::Bool | Sort::Int | Sort::String | Sort::Reference | Sort::Class | Sort::Bytes => true,
        Sort::Tuple(elements) => {
            let mut valid = true;
            for element in elements {
                if valid {
                    valid = is_z3_nested_equality_sort(element);
                }
            }
            valid
        }
        Sort::VariadicTuple(element) | Sort::List(element) => is_z3_nested_equality_sort(element),
        _ => false,
    }
}

fn integer_sequence(values: impl IntoIterator<Item = i64>) -> Seq {
    let units = values
        .into_iter()
        .map(|value| Seq::unit(&Int::from_i64(value)))
        .collect::<Vec<_>>();
    match units.as_slice() {
        [] => Seq::empty(&Z3Sort::int()),
        [only] => only.clone(),
        many => Seq::concat(&many.iter().collect::<Vec<_>>()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vc::ObligationExpectation;

    fn iterator_reference_collection_key_sort(sort: &Sort) -> bool {
        matches!(sort, Sort::Bool | Sort::Int | Sort::String | Sort::Bytes)
            || matches!(sort, Sort::Tuple(elements)
                if elements.iter().all(iterator_reference_collection_key_sort))
            || matches!(sort, Sort::VariadicTuple(element)
                if iterator_reference_collection_key_sort(element))
    }

    fn iterator_reference_collection_value_sort(sort: &Sort) -> bool {
        matches!(
            sort,
            Sort::Bool | Sort::Int | Sort::String | Sort::Reference | Sort::Bytes
        ) || matches!(sort, Sort::Tuple(elements)
            if elements.iter().all(iterator_reference_collection_value_sort))
            || matches!(sort, Sort::VariadicTuple(element) | Sort::List(element)
                if iterator_reference_collection_value_sort(element))
            || matches!(sort, Sort::Set(element)
                if iterator_reference_collection_key_sort(element))
            || matches!(sort, Sort::Dict(key, value) | Sort::FiniteDict(key, value)
                if iterator_reference_collection_key_sort(key)
                    && iterator_reference_collection_value_sort(value))
    }

    fn iterator_reference_nested_equality_sort(sort: &Sort) -> bool {
        matches!(
            sort,
            Sort::Bool | Sort::Int | Sort::String | Sort::Reference | Sort::Class | Sort::Bytes
        ) || matches!(sort, Sort::Tuple(elements)
            if elements.iter().all(iterator_reference_nested_equality_sort))
            || matches!(sort, Sort::VariadicTuple(element) | Sort::List(element)
                if iterator_reference_nested_equality_sort(element))
    }

    fn closure_reference_python_index_of(
        term: &Term,
        binder: &str,
        sorted: &Term,
        successor: bool,
    ) -> bool {
        let is_raw = |candidate: &Term| {
            if successor {
                is_bound_successor(candidate, binder)
            } else {
                is_bound_variable(candidate, binder)
            }
        };
        if is_raw(term) {
            return true;
        }
        let Term::IfThenElse {
            condition,
            then_value,
            else_value,
        } = term
        else {
            return false;
        };
        let Term::Less { left, right } = unwrap_singleton_and(condition) else {
            return false;
        };
        if !is_raw(left) || !is_integer_literal(right, 0) || !is_raw(else_value) {
            return false;
        }
        matches!(
            then_value.as_ref(),
            Term::Add { left, right }
                if matches!(
                    left.as_ref(),
                    Term::ListLength { value } if value.as_ref() == sorted
                ) && is_raw(right)
        )
    }

    fn iterator_reference_sorted_adjacent_theorem(term: &Term) -> bool {
        let Term::ForAll {
            binder,
            binder_sort: Sort::Int,
            body,
        } = term
        else {
            return false;
        };
        let Term::Implies { left: guard, right } = unwrap_singleton_and(body) else {
            return false;
        };
        let Term::LessEqual { left, right } = unwrap_singleton_and(right) else {
            return false;
        };
        let Term::ListGet {
            list: current_list,
            index: current_index,
        } = left.as_ref()
        else {
            return false;
        };
        let Term::ListGet {
            list: next_list,
            index: next_index,
        } = right.as_ref()
        else {
            return false;
        };
        if current_list != next_list || !matches!(current_list.as_ref(), Term::ListSorted { .. }) {
            return false;
        }
        if !closure_reference_python_index_of(current_index, binder, current_list, false)
            || !closure_reference_python_index_of(next_index, binder, current_list, true)
        {
            return false;
        }
        if let Term::IfThenElse {
            condition,
            then_value,
            else_value,
        } = unwrap_singleton_and(guard)
        {
            let condition = unwrap_singleton_and(condition);
            let then_value = unwrap_singleton_and(then_value);
            let else_value = unwrap_singleton_and(else_value);
            return condition == else_value
                && is_nonnegative_bound(condition, binder, &[])
                && is_adjacent_upper_bound(then_value, binder, current_list, &[]);
        }
        let conjuncts = match unwrap_singleton_and(guard) {
            Term::And { values } => values.as_slice(),
            guard => std::slice::from_ref(guard),
        };
        conjuncts
            .iter()
            .any(|conjunct| is_nonnegative_bound(conjunct, binder, &[]))
            && conjuncts
                .iter()
                .any(|conjunct| is_adjacent_upper_bound(conjunct, binder, current_list, &[]))
    }

    #[test]
    fn z3_sort_predicate_loops_match_iterator_definitions() {
        let sorts = [
            Sort::Bool,
            Sort::Int,
            Sort::String,
            Sort::Unit,
            Sort::Reference,
            Sort::Class,
            Sort::Bytes,
            Sort::Range,
            Sort::Tuple(vec![]),
            Sort::Tuple(vec![Sort::Int, Sort::Bytes]),
            Sort::Tuple(vec![Sort::Int, Sort::Unit]),
            Sort::Tuple(vec![Sort::Unit, Sort::Int]),
            Sort::Tuple(vec![
                Sort::List(Box::new(Sort::Reference)),
                Sort::VariadicTuple(Box::new(Sort::Class)),
            ]),
            Sort::VariadicTuple(Box::new(Sort::String)),
            Sort::VariadicTuple(Box::new(Sort::Unit)),
            Sort::List(Box::new(Sort::Reference)),
            Sort::List(Box::new(Sort::Unit)),
            Sort::Set(Box::new(Sort::Tuple(vec![Sort::Int, Sort::String]))),
            Sort::Set(Box::new(Sort::Reference)),
            Sort::Dict(Box::new(Sort::String), Box::new(Sort::Reference)),
            Sort::Dict(Box::new(Sort::Reference), Box::new(Sort::Int)),
            Sort::FiniteDict(
                Box::new(Sort::VariadicTuple(Box::new(Sort::Bytes))),
                Box::new(Sort::List(Box::new(Sort::Int))),
            ),
            Sort::DictKeys(Box::new(Sort::Int)),
        ];

        for sort in sorts {
            assert_eq!(
                is_z3_collection_key_sort(&sort),
                iterator_reference_collection_key_sort(&sort),
                "collection-key predicate differs for {sort:?}"
            );
            assert_eq!(
                is_z3_collection_value_sort(&sort),
                iterator_reference_collection_value_sort(&sort),
                "collection-value predicate differs for {sort:?}"
            );
            assert_eq!(
                is_z3_nested_equality_sort(&sort),
                iterator_reference_nested_equality_sort(&sort),
                "nested-equality predicate differs for {sort:?}"
            );
        }
    }

    fn integer(name: &str) -> Term {
        Term::Variable {
            name: name.to_owned(),
            sort: Sort::Int,
        }
    }

    fn string_int_dict(name: &str) -> Term {
        Term::Variable {
            name: name.to_owned(),
            sort: Sort::Dict(Box::new(Sort::String), Box::new(Sort::Int)),
        }
    }

    fn dictionary_contains(dict: &Term, key: &str) -> Term {
        Term::DictContains {
            dict: Box::new(dict.clone()),
            key: Box::new(Term::String {
                value: key.to_owned(),
            }),
        }
    }

    fn dictionary_get(dict: &Term, key: &str) -> Term {
        Term::DictGet {
            dict: Box::new(dict.clone()),
            key: Box::new(Term::String {
                value: key.to_owned(),
            }),
        }
    }

    fn solver_obligation(id: &str, assumptions: Vec<Term>, conclusion: Term) -> Obligation {
        Obligation {
            id: id.to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions,
            conclusion,
            path: "abstract-dictionary.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        }
    }

    #[test]
    fn abstract_dictionary_length_membership_and_lookup_assumptions_are_stable() {
        let dictionary = string_int_dict("named");
        let length_is_two = Term::Equal {
            left: Box::new(Term::DictLength {
                value: Box::new(dictionary.clone()),
            }),
            right: Box::new(Term::Int { value: 2 }),
        };
        let contains_left = dictionary_contains(&dictionary, "left");
        let left_is_seven = Term::Equal {
            left: Box::new(dictionary_get(&dictionary, "left")),
            right: Box::new(Term::Int { value: 7 }),
        };
        let result = discharge(&solver_obligation(
            "abstract-dict-assumptions",
            vec![
                length_is_two.clone(),
                contains_left.clone(),
                left_is_seven.clone(),
            ],
            Term::And {
                values: vec![length_is_two, contains_left, left_is_seven],
            },
        ))
        .unwrap();

        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn abstract_dictionary_lookup_does_not_invent_a_value() {
        let dictionary = string_int_dict("named");
        let value_claim = Term::Equal {
            left: Box::new(dictionary_get(&dictionary, "left")),
            right: Box::new(Term::Int { value: 7 }),
        };
        let without_membership = discharge(&solver_obligation(
            "abstract-dict-unguarded-lookup",
            Vec::new(),
            value_claim.clone(),
        ))
        .unwrap();
        assert_eq!(without_membership.status, ObligationStatus::Refuted);

        let membership_alone = discharge(&solver_obligation(
            "abstract-dict-membership-does-not-invent-value",
            vec![dictionary_contains(&dictionary, "left")],
            value_claim,
        ))
        .unwrap();
        assert_eq!(membership_alone.status, ObligationStatus::Refuted);
    }

    #[test]
    fn abstract_dictionary_variables_have_independent_stable_symbols() {
        let first = string_int_dict("first");
        let second = string_int_dict("second");
        let first_contains = dictionary_contains(&first, "left");
        let same_variable = discharge(&solver_obligation(
            "same-abstract-dict-symbol",
            vec![first_contains.clone()],
            first_contains.clone(),
        ))
        .unwrap();
        assert_eq!(same_variable.status, ObligationStatus::Proved);

        let distinct_variable = discharge(&solver_obligation(
            "distinct-abstract-dict-symbols",
            vec![first_contains],
            dictionary_contains(&second, "left"),
        ))
        .unwrap();
        assert_eq!(distinct_variable.status, ObligationStatus::Refuted);
    }

    #[test]
    fn abstract_sets_nested_dictionary_values_and_bad_keys_are_precise() {
        let abstract_set = Term::SetLength {
            value: Box::new(Term::Variable {
                name: "values".to_owned(),
                sort: Sort::Set(Box::new(Sort::Int)),
            }),
        };
        let zero_length = Term::Equal {
            left: Box::new(abstract_set),
            right: Box::new(Term::Int { value: 0 }),
        };
        let unconstrained = discharge(&solver_obligation(
            "abstract-set-unconstrained",
            Vec::new(),
            zero_length.clone(),
        ))
        .expect("symbolic set variables have exact sequence-backed semantics");
        assert_eq!(unconstrained.status, ObligationStatus::Refuted);
        let assumed = discharge(&solver_obligation(
            "abstract-set-assumption-reused",
            vec![zero_length.clone()],
            zero_length,
        ))
        .expect("an asserted symbolic-set fact must be reusable");
        assert_eq!(assumed.status, ObligationStatus::Proved);

        let nested_dictionary_length = Term::DictLength {
            value: Box::new(Term::Variable {
                name: "nested-values".to_owned(),
                sort: Sort::Dict(
                    Box::new(Sort::String),
                    Box::new(Sort::List(Box::new(Sort::Int))),
                ),
            }),
        };
        let nested_dictionary_is_empty = Term::Equal {
            left: Box::new(nested_dictionary_length),
            right: Box::new(Term::Int { value: 0 }),
        };
        let unconstrained_nested = discharge(&solver_obligation(
            "nested-dictionary-unconstrained",
            Vec::new(),
            nested_dictionary_is_empty.clone(),
        ))
        .expect("nested dictionary values have a first-class product encoding");
        assert_eq!(unconstrained_nested.status, ObligationStatus::Refuted);
        let assumed_nested = discharge(&solver_obligation(
            "nested-dictionary-assumption-reused",
            vec![nested_dictionary_is_empty.clone()],
            nested_dictionary_is_empty,
        ))
        .expect("an asserted nested-dictionary fact must be reusable");
        assert_eq!(assumed_nested.status, ObligationStatus::Proved);

        let bad_key_length = Term::DictLength {
            value: Box::new(Term::Variable {
                name: "bad-key".to_owned(),
                sort: Sort::Dict(
                    Box::new(Sort::List(Box::new(Sort::Int))),
                    Box::new(Sort::Int),
                ),
            }),
        };
        let error = discharge(&solver_obligation(
            "bad-key",
            Vec::new(),
            Term::Equal {
                left: Box::new(bad_key_length),
                right: Box::new(Term::Int { value: 0 }),
            },
        ))
        .expect_err("mutable dictionary keys must remain fail-closed");
        assert!(
            error.contains("symbolic dictionary key sort List(Int) is unsupported"),
            "{error}"
        );
    }

    #[test]
    fn proves_linear_implication() {
        let x = integer("x");
        let result = discharge(&Obligation {
            id: "positive-successor".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![Term::Greater {
                left: Box::new(x.clone()),
                right: Box::new(Term::Int { value: 0 }),
            }],
            conclusion: Term::Greater {
                left: Box::new(Term::Add {
                    left: Box::new(x),
                    right: Box::new(Term::Int { value: 1 }),
                }),
                right: Box::new(Term::Int { value: 0 }),
            },
            path: "proof.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn rejects_non_boolean_or_malformed_assumptions_before_solver_assertion() {
        let non_boolean = discharge(&Obligation {
            id: "non-boolean-assumption".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![Term::Int { value: 1 }],
            conclusion: Term::Bool { value: true },
            path: "malformed-vc.json".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .expect_err("an integer assumption is not a typed predicate");
        assert!(non_boolean.contains("assumption 0 is not boolean"));

        let malformed_binder = discharge(&Obligation {
            id: "malformed-binder-assumption".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![Term::ForAll {
                binder: "index".to_owned(),
                binder_sort: Sort::Int,
                body: Box::new(Term::Variable {
                    name: "index".to_owned(),
                    sort: Sort::Bool,
                }),
            }],
            conclusion: Term::Bool { value: false },
            path: "malformed-vc.json".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .expect_err("a binder occurrence with the wrong sort must not reach Z3");
        assert!(malformed_binder.contains("occurs with sort Bool, expected Int"));
    }

    #[test]
    fn floor_division_by_a_positive_constant_matches_python_for_negative_values() {
        let result = discharge(&Obligation {
            id: "python-floor-division".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![],
            conclusion: Term::And {
                values: vec![
                    Term::Equal {
                        left: Box::new(Term::FloorDivideByPositive {
                            value: Box::new(Term::Int { value: 7 }),
                            divisor: 2,
                        }),
                        right: Box::new(Term::Int { value: 3 }),
                    },
                    Term::Equal {
                        left: Box::new(Term::FloorDivideByPositive {
                            value: Box::new(Term::Int { value: -7 }),
                            divisor: 2,
                        }),
                        right: Box::new(Term::Int { value: -4 }),
                    },
                ],
            },
            path: "floor_division.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn proves_string_concatenation_value_and_length() {
        let concatenated = Term::StringConcat {
            values: vec![
                Term::String {
                    value: "abc".to_owned(),
                },
                Term::String {
                    value: "def".to_owned(),
                },
            ],
        };
        let result = discharge(&Obligation {
            id: "string-concat".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![],
            conclusion: Term::And {
                values: vec![
                    Term::Equal {
                        left: Box::new(concatenated.clone()),
                        right: Box::new(Term::String {
                            value: "abcdef".to_owned(),
                        }),
                    },
                    Term::Equal {
                        left: Box::new(Term::StringLength {
                            value: Box::new(concatenated),
                        }),
                        right: Box::new(Term::Int { value: 6 }),
                    },
                ],
            },
            path: "strings.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn proves_componentwise_tuple_projection_and_equality() {
        let tuple = Term::Variable {
            name: "pair".to_owned(),
            sort: Sort::Tuple(vec![Sort::Int, Sort::String]),
        };
        let first = Term::TupleGet {
            tuple: Box::new(tuple.clone()),
            index: 0,
        };
        let second = Term::TupleGet {
            tuple: Box::new(tuple.clone()),
            index: 1,
        };
        let result = discharge(&Obligation {
            id: "tuple-product".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![Term::Equal {
                left: Box::new(first.clone()),
                right: Box::new(Term::Int { value: 7 }),
            }],
            conclusion: Term::Equal {
                left: Box::new(tuple),
                right: Box::new(Term::Tuple {
                    values: vec![Term::Int { value: 7 }, second],
                }),
            },
            path: "tuples.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn proves_homogeneous_list_length_index_and_sequence_equality() {
        let list = Term::List {
            element_sort: Sort::Int,
            values: vec![Term::Int { value: 4 }, Term::Int { value: 9 }],
        };
        let result = discharge(&Obligation {
            id: "list-sequence".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![],
            conclusion: Term::And {
                values: vec![
                    Term::Equal {
                        left: Box::new(Term::ListLength {
                            value: Box::new(list.clone()),
                        }),
                        right: Box::new(Term::Int { value: 2 }),
                    },
                    Term::Equal {
                        left: Box::new(Term::ListGet {
                            list: Box::new(list.clone()),
                            index: Box::new(Term::Int { value: 1 }),
                        }),
                        right: Box::new(Term::Int { value: 9 }),
                    },
                    Term::Equal {
                        left: Box::new(list.clone()),
                        right: Box::new(list),
                    },
                ],
            },
            path: "lists.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn proves_bytes_and_range_equality_without_collapsing_their_sorts() {
        for (id, left, right) in [
            (
                "bytes-sequence",
                Term::Bytes {
                    values: vec![49, 50, 51],
                },
                Term::Bytes {
                    values: vec![49, 50, 51],
                },
            ),
            (
                "range-sequence",
                Term::Range {
                    values: vec![1, 3, 5],
                },
                Term::Range {
                    values: vec![1, 3, 5],
                },
            ),
        ] {
            let result = discharge(&Obligation {
                id: id.to_owned(),
                expectation: ObligationExpectation::Prove,
                assumptions: vec![],
                conclusion: Term::Equal {
                    left: Box::new(left),
                    right: Box::new(right),
                },
                path: "sequences.py".to_owned(),
                byte_offset: 0,
                line: 1,
                column: 1,
            })
            .unwrap();
            assert_eq!(result.status, ObligationStatus::Proved);
        }
    }

    #[test]
    fn proves_symbolic_bytes_concatenation_length_index_and_list_elements() {
        let tail = Term::Variable {
            name: "tail".to_owned(),
            sort: Sort::Bytes,
        };
        let bytes = Term::BytesConcat {
            values: vec![Term::Bytes { values: vec![7] }, tail.clone()],
        };
        let list = Term::List {
            element_sort: Sort::Bytes,
            values: vec![tail.clone(), bytes.clone()],
        };
        let result = discharge(&Obligation {
            id: "bytes-operations".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![],
            conclusion: Term::And {
                values: vec![
                    Term::Equal {
                        left: Box::new(Term::BytesGet {
                            bytes: Box::new(bytes.clone()),
                            index: Box::new(Term::Int { value: 0 }),
                        }),
                        right: Box::new(Term::Int { value: 7 }),
                    },
                    Term::Equal {
                        left: Box::new(Term::BytesLength {
                            value: Box::new(bytes),
                        }),
                        right: Box::new(Term::Add {
                            left: Box::new(Term::Int { value: 1 }),
                            right: Box::new(Term::BytesLength {
                                value: Box::new(tail.clone()),
                            }),
                        }),
                    },
                    Term::Equal {
                        left: Box::new(Term::ListGet {
                            list: Box::new(list),
                            index: Box::new(Term::Int { value: 0 }),
                        }),
                        right: Box::new(tail),
                    },
                ],
            },
            path: "bytes.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn returns_counterexample_for_false_claim() {
        let x = integer("x");
        let result = discharge(&Obligation {
            id: "not-implied".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![],
            conclusion: Term::Greater {
                left: Box::new(x),
                right: Box::new(Term::Int { value: 0 }),
            },
            path: "proof.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Refuted);
        assert!(result.counterexample.is_some());
    }

    #[test]
    fn proves_versioned_heap_field_facts_for_reference_receivers() {
        let object = Term::Variable {
            name: "object".to_owned(),
            sort: Sort::Reference,
        };
        let field = Term::FieldRead {
            heap: 3,
            receiver: Box::new(object),
            field: "value".to_owned(),
            sort: Sort::Int,
        };
        let result = discharge(&Obligation {
            id: "heap-field".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![Term::Equal {
                left: Box::new(field.clone()),
                right: Box::new(Term::Int { value: 7 }),
            }],
            conclusion: Term::Greater {
                left: Box::new(field),
                right: Box::new(Term::Int { value: 0 }),
            },
            path: "heap.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn distinguishes_fresh_reference_from_null_when_assumed() {
        let object = Term::Variable {
            name: "fresh-object".to_owned(),
            sort: Sort::Reference,
        };
        let not_null = Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(object),
                right: Box::new(Term::NullReference),
            }),
        };
        let result = discharge(&Obligation {
            id: "fresh-not-null".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![not_null.clone()],
            conclusion: not_null,
            path: "heap.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn lowers_exact_fractional_permission_atoms() {
        let permission = Term::PermissionAtLeast {
            mask: 2,
            receiver: Box::new(Term::Variable {
                name: "object".to_owned(),
                sort: Sort::Reference,
            }),
            field: "value".to_owned(),
            numerator: 1,
            denominator: 2,
        };
        let result = discharge(&Obligation {
            id: "permission".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![permission.clone()],
            conclusion: permission,
            path: "heap.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn fractional_permission_implies_read_permission_but_not_full_permission() {
        let receiver = Term::Variable {
            name: "object".to_owned(),
            sort: Sort::Reference,
        };
        let half = Term::PermissionAtLeast {
            mask: 2,
            receiver: Box::new(receiver.clone()),
            field: "value".to_owned(),
            numerator: 1,
            denominator: 2,
        };
        let positive = Term::PermissionPositive {
            mask: 2,
            receiver: Box::new(receiver.clone()),
            field: "value".to_owned(),
        };
        let full = Term::PermissionAtLeast {
            mask: 2,
            receiver: Box::new(receiver),
            field: "value".to_owned(),
            numerator: 1,
            denominator: 1,
        };
        let read = discharge(&Obligation {
            id: "fractional-read".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![half.clone()],
            conclusion: positive,
            path: "heap.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(read.status, ObligationStatus::Proved);
        let write = discharge(&Obligation {
            id: "fractional-write".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![half],
            conclusion: full,
            path: "heap.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(write.status, ObligationStatus::Refuted);
    }

    #[test]
    fn permission_mask_transition_consumes_and_preserves_the_declared_fraction() {
        let receiver = Term::Variable {
            name: "object".to_owned(),
            sort: Sort::Reference,
        };
        let valid_before = Term::PermissionMaskValid {
            mask: 0,
            field: "value".to_owned(),
        };
        let full_before = Term::PermissionAtLeast {
            mask: 0,
            receiver: Box::new(receiver.clone()),
            field: "value".to_owned(),
            numerator: 1,
            denominator: 1,
        };
        let transition = Term::PermissionMaskTransition {
            pre_mask: 0,
            post_mask: 1,
            field: "value".to_owned(),
            consumed: vec![crate::vc::PermissionTransferAmount {
                receiver: Box::new(receiver.clone()),
                numerator: 1,
                denominator: 2,
            }],
            produced: Vec::new(),
        };
        let half_after = Term::PermissionAtLeast {
            mask: 1,
            receiver: Box::new(receiver.clone()),
            field: "value".to_owned(),
            numerator: 1,
            denominator: 2,
        };
        let valid_after = Term::PermissionMaskValid {
            mask: 1,
            field: "value".to_owned(),
        };
        let preserved = discharge(&Obligation {
            id: "permission-transition".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![valid_before, full_before, transition],
            conclusion: Term::And {
                values: vec![valid_after, half_after],
            },
            path: "heap.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(preserved.status, ObligationStatus::Proved);
    }

    #[test]
    fn dynamic_constructor_class_identity_proves_class_receiver_postconditions() {
        let receiver_class = Term::Variable {
            name: "Widget.construct::cls".to_owned(),
            sort: Sort::Class,
        };
        let result = Term::Variable {
            name: "Widget.construct::result".to_owned(),
            sort: Sort::Reference,
        };
        let runtime_class = Term::RuntimeClass {
            value: Box::new(result),
        };
        let proved = discharge(&Obligation {
            id: "classmethod-constructor-result".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![
                Term::Equal {
                    left: Box::new(runtime_class.clone()),
                    right: Box::new(receiver_class.clone()),
                },
                Term::ClassSubtype {
                    actual: Box::new(receiver_class.clone()),
                    expected: Box::new(receiver_class.clone()),
                },
            ],
            conclusion: Term::And {
                values: vec![
                    Term::Equal {
                        left: Box::new(runtime_class.clone()),
                        right: Box::new(receiver_class.clone()),
                    },
                    Term::ClassSubtype {
                        actual: Box::new(runtime_class),
                        expected: Box::new(receiver_class),
                    },
                ],
            },
            path: "classmethod.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(proved.status, ObligationStatus::Proved);
    }

    #[test]
    fn distinct_source_class_literals_cannot_alias() {
        let result = discharge(&Obligation {
            id: "distinct-class-literals".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![],
            conclusion: Term::Not {
                value: Box::new(Term::Equal {
                    left: Box::new(Term::ClassLiteral {
                        name: "Alpha".to_owned(),
                    }),
                    right: Box::new(Term::ClassLiteral {
                        name: "Beta".to_owned(),
                    }),
                }),
            },
            path: "classes.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(result.status, ObligationStatus::Proved);
    }

    #[test]
    fn predicate_permissions_do_not_transfer_between_different_arguments() {
        let receiver = Term::Variable {
            name: "cell".to_owned(),
            sort: Sort::Reference,
        };
        let token_for = |argument| Term::PredicateInstance {
            predicate: "state".to_owned(),
            arguments: vec![receiver.clone(), Term::Int { value: argument }],
        };
        let permission_for = |argument| Term::PermissionAtLeast {
            mask: 0,
            receiver: Box::new(token_for(argument)),
            field: "@predicate:state".to_owned(),
            numerator: 1,
            denominator: 1,
        };
        let same = discharge(&Obligation {
            id: "same-predicate-instance".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![permission_for(12)],
            conclusion: permission_for(12),
            path: "predicate.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(same.status, ObligationStatus::Proved);

        let different = discharge(&Obligation {
            id: "different-predicate-instance".to_owned(),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![permission_for(12)],
            conclusion: permission_for(13),
            path: "predicate.py".to_owned(),
            byte_offset: 0,
            line: 1,
            column: 1,
        })
        .unwrap();
        assert_eq!(different.status, ObligationStatus::Refuted);
    }

    #[test]
    fn exact_sorted_adjacent_rule_rejects_weakened_or_mismatched_shapes() {
        let theorem = |strict: bool, include_lower: bool, matching_upper: bool| {
            let binder = "adjacent-index".to_owned();
            let index = Term::Variable {
                name: binder.clone(),
                sort: Sort::Int,
            };
            let successor = Term::Add {
                left: Box::new(index.clone()),
                right: Box::new(Term::Int { value: 1 }),
            };
            let sorted = Term::ListSorted {
                source: Box::new(Term::Variable {
                    name: "sorted-source".to_owned(),
                    sort: Sort::List(Box::new(Sort::Int)),
                }),
            };
            let upper_collection = if matching_upper {
                sorted.clone()
            } else {
                Term::ListSorted {
                    source: Box::new(Term::Variable {
                        name: "different-source".to_owned(),
                        sort: Sort::List(Box::new(Sort::Int)),
                    }),
                }
            };
            let mut guards = vec![Term::Less {
                left: Box::new(successor.clone()),
                right: Box::new(Term::ListLength {
                    value: Box::new(upper_collection),
                }),
            }];
            if include_lower {
                guards.push(Term::GreaterEqual {
                    left: Box::new(index.clone()),
                    right: Box::new(Term::Int { value: 0 }),
                });
            }
            let current = Term::ListGet {
                list: Box::new(sorted.clone()),
                index: Box::new(index),
            };
            let next = Term::ListGet {
                list: Box::new(sorted),
                index: Box::new(successor),
            };
            let order = if strict {
                Term::Less {
                    left: Box::new(current),
                    right: Box::new(next),
                }
            } else {
                Term::LessEqual {
                    left: Box::new(current),
                    right: Box::new(next),
                }
            };
            Term::ForAll {
                binder,
                binder_sort: Sort::Int,
                body: Box::new(Term::Implies {
                    left: Box::new(Term::And { values: guards }),
                    right: Box::new(order),
                }),
            }
        };

        for strict in [false, true] {
            for include_lower in [false, true] {
                for matching_upper in [false, true] {
                    let candidate = theorem(strict, include_lower, matching_upper);
                    assert_eq!(
                        is_exact_sorted_adjacent_order_theorem(&candidate),
                        iterator_reference_sorted_adjacent_theorem(&candidate)
                    );
                }
            }
        }

        assert!(is_exact_sorted_adjacent_order_theorem(&theorem(
            false, true, true
        )));
        assert!(!is_exact_sorted_adjacent_order_theorem(&theorem(
            true, true, true
        )));
        assert!(!is_exact_sorted_adjacent_order_theorem(&theorem(
            false, false, true
        )));
        assert!(!is_exact_sorted_adjacent_order_theorem(&theorem(
            false, true, false
        )));
    }

    #[test]
    fn python_index_branching_matches_closure_reference() {
        let binder = "index";
        let sorted = Term::ListSorted {
            source: Box::new(Term::Variable {
                name: "source".to_owned(),
                sort: Sort::List(Box::new(Sort::Int)),
            }),
        };
        let raw = Term::Variable {
            name: binder.to_owned(),
            sort: Sort::Int,
        };
        let successor = Term::Add {
            left: Box::new(raw.clone()),
            right: Box::new(Term::Int { value: 1 }),
        };
        let normalized = |candidate: Term| Term::IfThenElse {
            condition: Box::new(Term::Less {
                left: Box::new(candidate.clone()),
                right: Box::new(Term::Int { value: 0 }),
            }),
            then_value: Box::new(Term::Add {
                left: Box::new(Term::ListLength {
                    value: Box::new(sorted.clone()),
                }),
                right: Box::new(candidate.clone()),
            }),
            else_value: Box::new(candidate),
        };
        let candidates = [
            raw.clone(),
            successor.clone(),
            normalized(raw),
            normalized(successor),
            Term::Int { value: 0 },
        ];
        for candidate in &candidates {
            for successor in [false, true] {
                assert_eq!(
                    is_python_index_of(candidate, binder, &sorted, successor),
                    closure_reference_python_index_of(candidate, binder, &sorted, successor)
                );
            }
        }
    }
}
