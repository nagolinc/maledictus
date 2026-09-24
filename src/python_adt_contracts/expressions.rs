use std::collections::BTreeMap;

use rustpython_parser::ast;

use crate::vc::{Sort, Term};

use super::{Catalog, FieldType};

#[derive(Clone, Debug)]
pub(super) enum Value {
    Scalar(Term),
    Adt {
        constructor: String,
        root: String,
        fields: BTreeMap<String, Value>,
    },
    Object {
        class: String,
        fields: BTreeMap<String, Value>,
    },
    RuntimeType(String),
}

pub(super) fn symbolic_value(annotation: &str, prefix: &str, catalog: &Catalog) -> Option<Value> {
    match annotation {
        "int" => Some(Value::Scalar(Term::Variable {
            name: prefix.to_owned(),
            sort: Sort::Int,
        })),
        "bool" => Some(Value::Scalar(Term::Variable {
            name: prefix.to_owned(),
            sort: Sort::Bool,
        })),
        constructor if catalog.constructors.contains_key(constructor) => {
            let descriptor = &catalog.constructors[constructor];
            let mut fields = BTreeMap::new();
            for (field, kind) in &descriptor.fields {
                fields.insert(
                    field.clone(),
                    symbolic_field(kind, &format!("{prefix}.{field}"))?,
                );
            }
            Some(Value::Adt {
                constructor: constructor.to_owned(),
                root: descriptor.root.clone(),
                fields,
            })
        }
        _ => None,
    }
}

fn symbolic_field(kind: &FieldType, name: &str) -> Option<Value> {
    match kind {
        FieldType::Int => Some(Value::Scalar(Term::Variable {
            name: name.to_owned(),
            sort: Sort::Int,
        })),
        FieldType::Bool => Some(Value::Scalar(Term::Variable {
            name: name.to_owned(),
            sort: Sort::Bool,
        })),
        FieldType::Adt(_) | FieldType::Object(_) => None,
    }
}

pub(super) fn lower_expression(
    expression: &ast::Expr,
    environment: &BTreeMap<String, Value>,
    catalog: &Catalog,
) -> Option<Value> {
    match expression {
        ast::Expr::Name(name) => match name.id.as_str() {
            "True" => Some(Value::Scalar(Term::Bool { value: true })),
            "False" => Some(Value::Scalar(Term::Bool { value: false })),
            other => environment.get(other).cloned().or_else(|| {
                (catalog.roots.contains(other)
                    || catalog.constructors.contains_key(other)
                    || catalog.ordinary_classes.contains_key(other))
                .then(|| {
                    Value::Scalar(Term::ClassLiteral {
                        name: other.to_owned(),
                    })
                })
            }),
        },
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Bool(value) => Some(Value::Scalar(Term::Bool { value: *value })),
            ast::Constant::Int(value) => Some(Value::Scalar(Term::Int {
                value: value.to_string().parse().ok()?,
            })),
            ast::Constant::None => Some(Value::Scalar(Term::Unit)),
            _ => None,
        },
        ast::Expr::Attribute(attribute) => {
            let receiver = lower_expression(&attribute.value, environment, catalog)?;
            match receiver {
                Value::Adt { fields, .. } | Value::Object { fields, .. } => {
                    fields.get(attribute.attr.as_str()).cloned()
                }
                _ => None,
            }
        }
        ast::Expr::BinOp(operation) if operation.op == ast::Operator::Add => {
            let left = scalar_term(lower_expression(&operation.left, environment, catalog)?)?;
            let right = scalar_term(lower_expression(&operation.right, environment, catalog)?)?;
            Some(Value::Scalar(Term::Add {
                left: Box::new(left),
                right: Box::new(right),
            }))
        }
        ast::Expr::Compare(comparison) if comparison.ops.len() == 1 => {
            let left = lower_expression(&comparison.left, environment, catalog)?;
            let right = lower_expression(&comparison.comparators[0], environment, catalog)?;
            let equal = equal_term(&left, &right)?;
            match comparison.ops[0] {
                ast::CmpOp::Eq | ast::CmpOp::Is => Some(Value::Scalar(equal)),
                ast::CmpOp::NotEq | ast::CmpOp::IsNot => Some(Value::Scalar(Term::Not {
                    value: Box::new(equal),
                })),
                _ => None,
            }
        }
        ast::Expr::Call(call) => lower_call(call, environment, catalog),
        _ => None,
    }
}

fn lower_call(
    call: &ast::ExprCall,
    environment: &BTreeMap<String, Value>,
    catalog: &Catalog,
) -> Option<Value> {
    if !call.keywords.is_empty() {
        return None;
    }
    let ast::Expr::Name(callee) = call.func.as_ref() else {
        return None;
    };
    let name = callee.id.as_str();
    if let Some(descriptor) = catalog.constructors.get(name) {
        if call.args.len() != descriptor.fields.len() {
            return None;
        }
        let fields = descriptor
            .fields
            .iter()
            .zip(&call.args)
            .map(|((field, kind), argument)| {
                let value = lower_expression(argument, environment, catalog)?;
                value_matches_field_type(&value, kind).then_some((field.clone(), value))
            })
            .collect::<Option<BTreeMap<_, _>>>()?;
        return Some(Value::Adt {
            constructor: name.to_owned(),
            root: descriptor.root.clone(),
            fields,
        });
    }
    if let Some(ordinary) = catalog.ordinary_classes.get(name) {
        if call.args.len() != ordinary.fields.len() {
            return None;
        }
        let fields = ordinary
            .fields
            .iter()
            .zip(&call.args)
            .map(|(field, argument)| {
                Some((
                    field.clone(),
                    lower_expression(argument, environment, catalog)?,
                ))
            })
            .collect::<Option<BTreeMap<_, _>>>()?;
        return Some(Value::Object {
            class: name.to_owned(),
            fields,
        });
    }
    match (name, call.args.as_slice()) {
        ("cast", [_, value]) => lower_expression(value, environment, catalog),
        ("type", [value]) => match lower_expression(value, environment, catalog)? {
            Value::Adt { constructor, .. } => Some(Value::RuntimeType(constructor)),
            Value::Object { class, .. } => Some(Value::RuntimeType(class)),
            _ => None,
        },
        ("isinstance", [value, ast::Expr::Name(expected)]) => {
            let value = lower_expression(value, environment, catalog)?;
            let result = match value {
                Value::Adt {
                    constructor, root, ..
                } => expected.id.as_str() == constructor || expected.id.as_str() == root,
                Value::Object { class, .. } => expected.id.as_str() == class,
                _ => false,
            };
            Some(Value::Scalar(Term::Bool { value: result }))
        }
        _ => None,
    }
}

fn value_matches_field_type(value: &Value, field_type: &FieldType) -> bool {
    match (value, field_type) {
        (Value::Scalar(term), FieldType::Int) => term.sort().ok() == Some(Sort::Int),
        (Value::Scalar(term), FieldType::Bool) => term.sort().ok() == Some(Sort::Bool),
        (Value::Adt { root, .. }, FieldType::Adt(expected)) => root == expected,
        (Value::Object { class, .. }, FieldType::Object(expected)) => class == expected,
        _ => false,
    }
}

fn equal_term(left: &Value, right: &Value) -> Option<Term> {
    match (left, right) {
        (Value::Scalar(left), Value::Scalar(right)) => Some(Term::Equal {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }),
        (
            Value::Adt {
                constructor: left_constructor,
                fields: left_fields,
                ..
            },
            Value::Adt {
                constructor: right_constructor,
                fields: right_fields,
                ..
            },
        ) => {
            if left_constructor != right_constructor || left_fields.len() != right_fields.len() {
                return Some(Term::Bool { value: false });
            }
            let values = left_fields
                .iter()
                .map(|(name, left)| equal_term(left, right_fields.get(name)?))
                .collect::<Option<Vec<_>>>()?;
            Some(if values.is_empty() {
                Term::Bool { value: true }
            } else {
                Term::And { values }
            })
        }
        (Value::RuntimeType(left), Value::RuntimeType(right)) => Some(Term::Bool {
            value: left == right,
        }),
        (Value::RuntimeType(left), Value::Scalar(Term::ClassLiteral { name }))
        | (Value::Scalar(Term::ClassLiteral { name }), Value::RuntimeType(left)) => {
            Some(Term::Bool {
                value: left == name,
            })
        }
        _ => None,
    }
}

fn scalar_term(value: Value) -> Option<Term> {
    match value {
        Value::Scalar(term) => Some(term),
        Value::RuntimeType(name) => Some(Term::ClassLiteral { name }),
        _ => None,
    }
}

pub(super) fn bool_term(value: Value) -> Option<Term> {
    let term = scalar_term(value)?;
    (term.sort().ok()? == Sort::Bool).then_some(term)
}
