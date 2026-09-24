//! Closed semantics for Nagini's immutable persistent collection values.
//!
//! The implementation is deliberately source-general: it evaluates a finite, concrete algebra
//! derived from the Python AST and refuses as soon as source behavior would require dynamic
//! dispatch, mutable aliases, symbolic collection contents, or user-defined equality/hash code.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_ast::Visitor;
use rustpython_parser::{Parse, ast};

use crate::python_contracts::ContractFailure;
use crate::python_heap_contracts::HeapContractVerification;
use crate::solver::discharge;
use crate::vc::{Obligation, ObligationExpectation, ObligationResult, Term};

const CONSTRUCTORS: [&str; 3] = ["PSeq", "PSet", "PMultiset"];
const CONVERSIONS: [&str; 2] = ["ToSeq", "ToMS"];
const PERSISTENT_OWNERSHIP_WITNESSES: [&str; 4] = ["PSeq", "PSet", "PMultiset", "ToMS"];

#[derive(Clone, Debug, Eq, PartialEq)]
enum ElementKind {
    Int,
    Boolean,
    Object(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SequenceFlavor {
    PythonList,
    Persistent,
    UnorderedProjection,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PersistentAlgebraError {
    ElementKindMismatch,
    EqualityOperandsUnsupported,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Elements {
    kind: Option<ElementKind>,
    values: Vec<ElementValue>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ElementValue {
    Int(i128),
    Boolean(bool),
    Object { class: String, identity: u64 },
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Value {
    Int(i128),
    Bool(bool),
    Unit,
    Object {
        class: String,
        identity: u64,
    },
    Sequence {
        flavor: SequenceFlavor,
        elements: Elements,
    },
    PythonSet(Elements),
    PersistentSet(Elements),
    Multiset(Elements),
    Dictionary {
        keys: Elements,
        values: Elements,
    },
}

#[derive(Default)]
struct PersistentCallDetector {
    found: bool,
}

impl Visitor for PersistentCallDetector {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if matches!(node.func.as_ref(), ast::Expr::Name(name)
            if PERSISTENT_OWNERSHIP_WITNESSES.contains(&name.id.as_str()))
        {
            self.found = true;
        }
        self.generic_visit_expr_call(node);
    }
}

struct Evaluator<'a> {
    classes: &'a BTreeSet<String>,
    environment: BTreeMap<String, Value>,
    next_object_identity: u64,
}

pub(super) fn verify_persistent_collection_module(
    source: &str,
    path: &str,
    requested_symbols: &[String],
) -> Result<Option<HeapContractVerification>, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    let mut detector = PersistentCallDetector::default();
    for statement in suite.clone() {
        detector.visit_stmt(statement);
    }
    if !detector.found {
        return Ok(None);
    }
    if suite.iter().any(|statement| {
        matches!(statement, ast::Stmt::ClassDef(class)
            if class.bases.iter().any(|base| matches!(base, ast::Expr::Subscript(subscript)
                if matches!(subscript.value.as_ref(), ast::Expr::Name(name)
                    if name.id.as_str() == "Generic"))))
    }) {
        // Persistent values stored behind source-class fields require permissions, constructor
        // summaries, properties, and closed generic specialization. Those semantics belong to
        // the general heap verifier; the concrete persistent evaluator must not claim them and
        // then reject harmless typing declarations as executable statements.
        return Ok(None);
    }

    let (classes, functions) = validate_module_shape(&suite)?;
    let declared = classes
        .iter()
        .cloned()
        .chain(functions.keys().cloned())
        .collect::<BTreeSet<_>>();
    if let Some(missing) = requested_symbols
        .iter()
        .find(|requested| !declared.contains(requested.as_str()))
    {
        return fail(
            "frontend.python.persistent.requested-symbol-missing",
            format!("requested symbol {missing:?} is not declared by the persistent module"),
        );
    }

    let selected = functions
        .iter()
        .filter(|(name, _)| requested_symbols.is_empty() || requested_symbols.contains(name))
        .collect::<Vec<_>>();
    if selected.is_empty() {
        return fail(
            "frontend.python.persistent.no-selected-functions",
            "persistent collection verification requires at least one selected source function",
        );
    }

    let mut obligations = Vec::new();
    let mut methods = Vec::new();
    for (name, function) in selected {
        let mut evaluator = Evaluator {
            classes: &classes,
            environment: BTreeMap::new(),
            next_object_identity: 0,
        };
        evaluator.verify_function(function, source, path, &mut obligations)?;
        methods.push(name.clone());
        obligations.push(make_obligation(
            format!("{name}:function-totality"),
            true,
            source,
            path,
            function.range.start().into(),
        ));
    }

    let obligations = obligations
        .iter()
        .map(|obligation| {
            discharge(obligation).map_err(|message| ContractFailure {
                code: "solver.translation-failed",
                message,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let passed = obligations.iter().all(ObligationResult::satisfied);
    Ok(Some(HeapContractVerification {
        schema: "maledictus-python-persistent-collections/v1".to_owned(),
        path: path.to_owned(),
        methods,
        obligations,
        passed,
    }))
}

fn validate_module_shape(
    suite: &[ast::Stmt],
) -> Result<(BTreeSet<String>, BTreeMap<String, ast::StmtFunctionDef>), ContractFailure> {
    let mut canonical_contract_import = false;
    let mut classes = BTreeSet::new();
    let mut functions = BTreeMap::new();
    for statement in suite {
        match statement {
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import
                        .module
                        .as_ref()
                        .is_some_and(|module| module.as_str() == "nagini_contracts.contracts")
                    && matches!(import.names.as_slice(), [alias]
                        if alias.name.as_str() == "*" && alias.asname.is_none()) =>
            {
                canonical_contract_import = true;
            }
            ast::Stmt::ClassDef(class) => {
                if CONSTRUCTORS.contains(&class.name.as_str())
                    || CONVERSIONS.contains(&class.name.as_str())
                {
                    return fail(
                        "frontend.python.persistent.canonical-name-shadowed",
                        format!("class {:?} shadows a persistent builtin", class.name),
                    );
                }
                if !class.bases.is_empty()
                    || !class.keywords.is_empty()
                    || !class.decorator_list.is_empty()
                    || !class.type_params.is_empty()
                    || !matches!(class.body.as_slice(), [ast::Stmt::Pass(_)])
                {
                    return fail(
                        "frontend.python.persistent.object-semantics-unsupported",
                        format!(
                            "persistent collection elements require pass-only source classes with inherited object equality; class {:?} is not pass-only",
                            class.name
                        ),
                    );
                }
                if !classes.insert(class.name.to_string()) {
                    return fail(
                        "frontend.python.persistent.duplicate-class",
                        format!("duplicate class binding {:?}", class.name),
                    );
                }
            }
            ast::Stmt::FunctionDef(function) => {
                if CONSTRUCTORS.contains(&function.name.as_str())
                    || CONVERSIONS.contains(&function.name.as_str())
                {
                    return fail(
                        "frontend.python.persistent.canonical-name-shadowed",
                        format!("function {:?} shadows a persistent builtin", function.name),
                    );
                }
                if functions
                    .insert(function.name.to_string(), function.clone())
                    .is_some()
                {
                    return fail(
                        "frontend.python.persistent.duplicate-function",
                        format!("duplicate function binding {:?}", function.name),
                    );
                }
            }
            _ => {
                return fail(
                    "frontend.python.persistent.module-statement-unsupported",
                    format!("unsupported persistent module statement {statement:?}"),
                );
            }
        }
    }
    if !canonical_contract_import {
        return fail(
            "frontend.python.persistent.contract-import-missing",
            "persistent builtins require the canonical nagini_contracts.contracts wildcard import",
        );
    }
    if classes.iter().any(|name| functions.contains_key(name)) {
        return fail(
            "frontend.python.persistent.duplicate-binding",
            "a top-level name is bound as both a class and a function",
        );
    }
    Ok((classes, functions))
}

impl Evaluator<'_> {
    fn verify_function(
        &mut self,
        function: &ast::StmtFunctionDef,
        source: &str,
        path: &str,
        obligations: &mut Vec<Obligation>,
    ) -> Result<(), ContractFailure> {
        if !function.decorator_list.is_empty()
            || !function.type_params.is_empty()
            || !function.args.posonlyargs.is_empty()
            || !function.args.args.is_empty()
            || function.args.vararg.is_some()
            || !function.args.kwonlyargs.is_empty()
            || function.args.kwarg.is_some()
            || !is_none_annotation(function.returns.as_deref())
        {
            return fail(
                "frontend.python.persistent.function-signature-unsupported",
                format!(
                    "persistent collection function {:?} must be a nongeneric, parameterless function returning None",
                    function.name
                ),
            );
        }
        for statement in &function.body {
            match statement {
                ast::Stmt::Assign(assignment) => {
                    let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
                        return fail(
                            "frontend.python.persistent.assignment-target-unsupported",
                            "persistent values may only be assigned to one local name",
                        );
                    };
                    if CONSTRUCTORS.contains(&target.id.as_str())
                        || CONVERSIONS.contains(&target.id.as_str())
                    {
                        return fail(
                            "frontend.python.persistent.canonical-name-shadowed",
                            format!("local {:?} shadows a persistent builtin", target.id),
                        );
                    }
                    let mut value = self.evaluate(&assignment.value)?;
                    if let Some(comment) = assignment.type_comment.as_deref() {
                        apply_type_comment(&mut value, comment)?;
                    }
                    self.environment.insert(target.id.to_string(), value);
                }
                ast::Stmt::Assert(assertion) => {
                    let Value::Bool(conclusion) = self.evaluate(&assertion.test)? else {
                        return fail(
                            "frontend.python.persistent.assertion-not-bool",
                            "persistent collection assertions must have a boolean result",
                        );
                    };
                    if assertion.msg.is_some() {
                        return fail(
                            "frontend.python.persistent.assertion-message-unsupported",
                            "assertion messages are outside the persistent collection fragment",
                        );
                    }
                    obligations.push(make_obligation(
                        format!(
                            "{}:assert:{}",
                            function.name,
                            u32::from(assertion.range.start())
                        ),
                        conclusion,
                        source,
                        path,
                        assertion.range.start().into(),
                    ));
                }
                _ => {
                    return fail(
                        "frontend.python.persistent.function-statement-unsupported",
                        format!(
                            "persistent collection function {:?} contains unsupported statement {statement:?}",
                            function.name
                        ),
                    );
                }
            }
        }
        Ok(())
    }

    fn evaluate(&mut self, expression: &ast::Expr) -> Result<Value, ContractFailure> {
        match expression {
            ast::Expr::Name(name) => match name.id.as_str() {
                "True" => Ok(Value::Bool(true)),
                "False" => Ok(Value::Bool(false)),
                other => self
                    .environment
                    .get(other)
                    .cloned()
                    .ok_or_else(|| ContractFailure {
                        code: "frontend.python.persistent.name-unresolved",
                        message: format!("persistent expression name {other:?} is unresolved"),
                    }),
            },
            ast::Expr::Constant(constant) => match &constant.value {
                ast::Constant::Bool(value) => Ok(Value::Bool(*value)),
                ast::Constant::Int(value) => {
                    Ok(Value::Int(value.to_string().parse().map_err(|_| {
                        ContractFailure {
                            code: "frontend.python.persistent.integer-out-of-range",
                            message: format!(
                                "integer literal {value} exceeds the exact i128 fragment"
                            ),
                        }
                    })?))
                }
                ast::Constant::None => Ok(Value::Unit),
                _ => fail(
                    "frontend.python.persistent.constant-unsupported",
                    format!("unsupported persistent constant {constant:?}"),
                ),
            },
            ast::Expr::List(list) => Ok(Value::Sequence {
                flavor: SequenceFlavor::PythonList,
                elements: self.evaluate_elements(&list.elts)?,
            }),
            ast::Expr::Set(set) => Ok(Value::PythonSet(unique(self.evaluate_elements(&set.elts)?))),
            ast::Expr::Dict(dictionary) => self.evaluate_dictionary(dictionary),
            ast::Expr::Call(call) => self.evaluate_call(call),
            ast::Expr::BinOp(operation) => self.evaluate_binary(operation),
            ast::Expr::Compare(comparison) => self.evaluate_comparison(comparison),
            ast::Expr::BoolOp(boolean) => self.evaluate_boolean(boolean),
            ast::Expr::UnaryOp(unary) if unary.op == ast::UnaryOp::Not => {
                let Value::Bool(value) = self.evaluate(&unary.operand)? else {
                    return fail(
                        "frontend.python.persistent.not-operand-unsupported",
                        "not requires a boolean operand in the persistent fragment",
                    );
                };
                Ok(Value::Bool(!value))
            }
            ast::Expr::Subscript(subscript) => self.evaluate_index(subscript),
            _ => fail(
                "frontend.python.persistent.expression-unsupported",
                format!("unsupported persistent expression {expression:?}"),
            ),
        }
    }

    fn evaluate_elements(
        &mut self,
        expressions: &[ast::Expr],
    ) -> Result<Elements, ContractFailure> {
        let values = expressions
            .iter()
            .map(|expression| self.evaluate(expression))
            .collect::<Result<Vec<_>, _>>()?;
        Elements::new(values)
    }

    fn evaluate_dictionary(
        &mut self,
        dictionary: &ast::ExprDict,
    ) -> Result<Value, ContractFailure> {
        if dictionary.keys.iter().any(Option::is_none) {
            return fail(
                "frontend.python.persistent.dictionary-unpack-unsupported",
                "dictionary unpacking is outside the persistent collection fragment",
            );
        }
        let mut entries = Vec::<(Value, Value)>::new();
        for (key, value) in dictionary.keys.iter().zip(&dictionary.values) {
            // Python evaluates each key immediately followed by its value. A later equal key
            // replaces only the value while retaining the first key's insertion position.
            let key = self.evaluate(key.as_ref().expect("dictionary key guard"))?;
            let value = self.evaluate(value)?;
            if let Some(index) = entries.iter().position(|(existing, _)| *existing == key) {
                entries[index].1 = value;
            } else {
                entries.push((key, value));
            }
        }
        let (keys, values): (Vec<_>, Vec<_>) = entries.into_iter().unzip();
        Ok(Value::Dictionary {
            keys: Elements::new(keys)?,
            values: Elements::new(values)?,
        })
    }

    fn evaluate_call(&mut self, call: &ast::ExprCall) -> Result<Value, ContractFailure> {
        if !call.keywords.is_empty() {
            return fail(
                "frontend.python.persistent.keyword-arguments-unsupported",
                "persistent operations do not accept keyword arguments",
            );
        }
        match call.func.as_ref() {
            ast::Expr::Name(callee) => self.evaluate_named_call(callee.id.as_str(), &call.args),
            ast::Expr::Attribute(method) => self.evaluate_method_call(method, &call.args),
            _ => fail(
                "frontend.python.persistent.dynamic-call-unsupported",
                "persistent operation call targets must be canonical names or direct methods",
            ),
        }
    }

    fn evaluate_named_call(
        &mut self,
        callee: &str,
        arguments: &[ast::Expr],
    ) -> Result<Value, ContractFailure> {
        match callee {
            "PSeq" => Ok(Value::Sequence {
                flavor: SequenceFlavor::Persistent,
                elements: self.evaluate_elements(arguments)?,
            }),
            "PSet" => Ok(Value::PersistentSet(unique(
                self.evaluate_elements(arguments)?,
            ))),
            "PMultiset" => Ok(Value::Multiset(self.evaluate_elements(arguments)?)),
            "ToSeq" if arguments.len() == 1 => match self.evaluate(&arguments[0])? {
                Value::Sequence { elements, .. } => Ok(Value::Sequence {
                    flavor: SequenceFlavor::Persistent,
                    elements,
                }),
                Value::PythonSet(elements) => Ok(Value::Sequence {
                    flavor: SequenceFlavor::UnorderedProjection,
                    elements,
                }),
                Value::Dictionary { keys, .. } => Ok(Value::Sequence {
                    flavor: SequenceFlavor::UnorderedProjection,
                    elements: keys,
                }),
                _ => fail(
                    "frontend.python.persistent.toseq-source-unsupported",
                    "ToSeq requires a list, set, dictionary, or persistent sequence",
                ),
            },
            "ToMS" if arguments.len() == 1 => match self.evaluate(&arguments[0])? {
                Value::Sequence { elements, .. } => Ok(Value::Multiset(elements)),
                _ => fail(
                    "frontend.python.persistent.toms-source-unsupported",
                    "ToMS requires a concrete sequence",
                ),
            },
            "len" if arguments.len() == 1 => {
                let length = match self.evaluate(&arguments[0])? {
                    Value::Sequence { elements, .. }
                    | Value::PythonSet(elements)
                    | Value::PersistentSet(elements)
                    | Value::Multiset(elements) => elements.values.len(),
                    Value::Dictionary { keys, .. } => keys.values.len(),
                    _ => {
                        return fail(
                            "frontend.python.persistent.len-operand-unsupported",
                            "len requires a supported finite collection",
                        );
                    }
                };
                Ok(Value::Int(i128::try_from(length).map_err(|_| {
                    ContractFailure {
                        code: "frontend.python.persistent.length-out-of-range",
                        message: "collection length exceeds i128".to_owned(),
                    }
                })?))
            }
            class if self.classes.contains(class) => {
                if !arguments.is_empty() {
                    return fail(
                        "frontend.python.persistent.constructor-arguments-unsupported",
                        format!("pass-only class {class:?} accepts no constructor arguments"),
                    );
                }
                let identity = self.next_object_identity;
                self.next_object_identity =
                    self.next_object_identity
                        .checked_add(1)
                        .ok_or_else(|| ContractFailure {
                            code: "frontend.python.persistent.object-identity-overflow",
                            message: "object identity counter overflowed".to_owned(),
                        })?;
                Ok(Value::Object {
                    class: class.to_owned(),
                    identity,
                })
            }
            _ if CONSTRUCTORS.contains(&callee)
                || CONVERSIONS.contains(&callee)
                || callee == "len" =>
            {
                fail(
                    "frontend.python.persistent.call-arity",
                    format!(
                        "persistent operation {callee:?} received the wrong number of arguments"
                    ),
                )
            }
            _ => fail(
                "frontend.python.persistent.call-unresolved",
                format!("persistent call target {callee:?} is unresolved"),
            ),
        }
    }

    fn evaluate_method_call(
        &mut self,
        method: &ast::ExprAttribute,
        arguments: &[ast::Expr],
    ) -> Result<Value, ContractFailure> {
        let receiver = self.evaluate(&method.value)?;
        match (receiver, method.attr.as_str(), arguments) {
            (
                Value::Sequence {
                    flavor: SequenceFlavor::Persistent,
                    elements,
                },
                "take",
                [count],
            ) => {
                let count = self.nonnegative_index(count)?;
                let end = count.min(elements.values.len());
                Ok(Value::Sequence {
                    flavor: SequenceFlavor::Persistent,
                    elements: Elements {
                        kind: elements.kind,
                        values: elements.values[..end].to_vec(),
                    },
                })
            }
            (
                Value::Sequence {
                    flavor: SequenceFlavor::Persistent,
                    elements,
                },
                "drop",
                [count],
            ) => {
                let count = self.nonnegative_index(count)?;
                let start = count.min(elements.values.len());
                Ok(Value::Sequence {
                    flavor: SequenceFlavor::Persistent,
                    elements: Elements {
                        kind: elements.kind,
                        values: elements.values[start..].to_vec(),
                    },
                })
            }
            (
                Value::Sequence {
                    flavor: SequenceFlavor::Persistent,
                    mut elements,
                },
                "update",
                [index, replacement],
            ) => {
                let index = self.nonnegative_index(index)?;
                if index >= elements.values.len() {
                    return fail(
                        "frontend.python.persistent.update-index-out-of-range",
                        format!("persistent update index {index} is outside the sequence"),
                    );
                }
                let replacement = self.evaluate(replacement)?;
                let replacement = ElementValue::from_value(replacement)?;
                require_element_kind(&replacement, elements.kind.as_ref())?;
                elements.values[index] = replacement;
                Ok(Value::Sequence {
                    flavor: SequenceFlavor::Persistent,
                    elements,
                })
            }
            (Value::Multiset(elements), "num", [needle]) => {
                let needle = self.evaluate(needle)?;
                let needle = ElementValue::from_value(needle)?;
                require_element_kind(&needle, elements.kind.as_ref())?;
                let count = elements
                    .values
                    .iter()
                    .filter(|value| **value == needle)
                    .count();
                Ok(Value::Int(i128::try_from(count).map_err(|_| {
                    ContractFailure {
                        code: "frontend.python.persistent.multiplicity-out-of-range",
                        message: "multiset multiplicity exceeds i128".to_owned(),
                    }
                })?))
            }
            (_, name, _) => fail(
                "frontend.python.persistent.method-unsupported",
                format!("persistent method {name:?} is unsupported for this receiver and arity"),
            ),
        }
    }

    fn evaluate_binary(&mut self, operation: &ast::ExprBinOp) -> Result<Value, ContractFailure> {
        let left = self.evaluate(&operation.left)?;
        let right = self.evaluate(&operation.right)?;
        match (operation.op, left, right) {
            (
                ast::Operator::Add,
                Value::Sequence {
                    flavor: SequenceFlavor::Persistent,
                    elements: left,
                },
                Value::Sequence {
                    flavor: SequenceFlavor::Persistent,
                    elements: right,
                },
            ) => Ok(Value::Sequence {
                flavor: SequenceFlavor::Persistent,
                elements: concatenate(left, right)?,
            }),
            (ast::Operator::Add, Value::PersistentSet(left), Value::PersistentSet(right)) => {
                Ok(Value::PersistentSet(unique(concatenate(left, right)?)))
            }
            (ast::Operator::Add, Value::Multiset(left), Value::Multiset(right)) => {
                Ok(Value::Multiset(concatenate(left, right)?))
            }
            (ast::Operator::Sub, Value::PersistentSet(left), Value::PersistentSet(right)) => {
                require_compatible_kinds(left.kind.clone(), right.kind.clone())?;
                Ok(Value::PersistentSet(Elements {
                    kind: left.kind.or(right.kind),
                    values: left
                        .values
                        .into_iter()
                        .filter(|value| !right.values.contains(value))
                        .collect(),
                }))
            }
            (ast::Operator::Sub, Value::Multiset(left), Value::Multiset(right)) => {
                require_compatible_kinds(left.kind.clone(), right.kind.clone())?;
                let mut remaining = left.values;
                for value in right.values {
                    if let Some(index) = remaining.iter().position(|candidate| *candidate == value)
                    {
                        remaining.remove(index);
                    }
                }
                Ok(Value::Multiset(Elements {
                    kind: left.kind.or(right.kind),
                    values: remaining,
                }))
            }
            _ => fail(
                "frontend.python.persistent.binary-operation-unsupported",
                format!("unsupported persistent binary operation {operation:?}"),
            ),
        }
    }

    fn evaluate_comparison(
        &mut self,
        comparison: &ast::ExprCompare,
    ) -> Result<Value, ContractFailure> {
        if comparison.ops.len() != 1 || comparison.comparators.len() != 1 {
            return fail(
                "frontend.python.persistent.chained-comparison-unsupported",
                "persistent collection comparisons must contain exactly one operator",
            );
        }
        let left = self.evaluate(&comparison.left)?;
        let right = self.evaluate(&comparison.comparators[0])?;
        let result = match comparison.ops[0] {
            ast::CmpOp::Eq => comparable_equal(&left, &right)?,
            ast::CmpOp::NotEq => !comparable_equal(&left, &right)?,
            ast::CmpOp::Is => object_identical(&left, &right)?,
            ast::CmpOp::IsNot => !object_identical(&left, &right)?,
            ast::CmpOp::In => contains(&right, &left)?,
            ast::CmpOp::NotIn => !contains(&right, &left)?,
            ast::CmpOp::Lt => integer_pair(&left, &right, |a, b| a < b)?,
            ast::CmpOp::LtE => integer_pair(&left, &right, |a, b| a <= b)?,
            ast::CmpOp::Gt => integer_pair(&left, &right, |a, b| a > b)?,
            ast::CmpOp::GtE => integer_pair(&left, &right, |a, b| a >= b)?,
        };
        Ok(Value::Bool(result))
    }

    fn evaluate_boolean(&mut self, boolean: &ast::ExprBoolOp) -> Result<Value, ContractFailure> {
        if boolean.values.is_empty() {
            return fail(
                "frontend.python.persistent.empty-boolop",
                "boolean operation has no operands",
            );
        }
        match boolean.op {
            ast::BoolOp::And => {
                for operand in &boolean.values {
                    let Value::Bool(value) = self.evaluate(operand)? else {
                        return fail(
                            "frontend.python.persistent.boolop-operand-unsupported",
                            "and/or operands must be booleans",
                        );
                    };
                    if !value {
                        return Ok(Value::Bool(false));
                    }
                }
                Ok(Value::Bool(true))
            }
            ast::BoolOp::Or => {
                for operand in &boolean.values {
                    let Value::Bool(value) = self.evaluate(operand)? else {
                        return fail(
                            "frontend.python.persistent.boolop-operand-unsupported",
                            "and/or operands must be booleans",
                        );
                    };
                    if value {
                        return Ok(Value::Bool(true));
                    }
                }
                Ok(Value::Bool(false))
            }
        }
    }

    fn evaluate_index(&mut self, subscript: &ast::ExprSubscript) -> Result<Value, ContractFailure> {
        let receiver = self.evaluate(&subscript.value)?;
        let index = self.nonnegative_index(&subscript.slice)?;
        let Value::Sequence {
            flavor: SequenceFlavor::Persistent,
            elements,
        } = receiver
        else {
            return fail(
                "frontend.python.persistent.index-receiver-unsupported",
                "indexing requires a persistent sequence",
            );
        };
        elements
            .values
            .get(index)
            .cloned()
            .map(ElementValue::into_value)
            .ok_or_else(|| ContractFailure {
                code: "frontend.python.persistent.index-out-of-range",
                message: format!("persistent sequence index {index} is out of range"),
            })
    }

    fn nonnegative_index(&mut self, expression: &ast::Expr) -> Result<usize, ContractFailure> {
        let Value::Int(value) = self.evaluate(expression)? else {
            return fail(
                "frontend.python.persistent.index-not-int",
                "persistent collection index must be a concrete integer",
            );
        };
        usize::try_from(value).map_err(|_| ContractFailure {
            code: "frontend.python.persistent.index-negative-or-large",
            message: format!("persistent collection index {value} is negative or too large"),
        })
    }
}

impl Elements {
    fn new(values: Vec<Value>) -> Result<Self, ContractFailure> {
        let values = values
            .into_iter()
            .map(ElementValue::from_value)
            .collect::<Result<Vec<_>, _>>()?;
        let kind = values.first().map(element_kind);
        for value in values.iter().skip(1) {
            require_element_kind(value, kind.as_ref())?;
        }
        Ok(Self { kind, values })
    }
}

impl ElementValue {
    fn from_value(value: Value) -> Result<Self, ContractFailure> {
        match value {
            Value::Int(value) => Ok(Self::Int(value)),
            Value::Bool(value) => Ok(Self::Boolean(value)),
            Value::Object { class, identity } => Ok(Self::Object { class, identity }),
            _ => fail(
                "frontend.python.persistent.nested-element-unsupported",
                "persistent collections require flat int, bool, or pass-only source-object elements",
            ),
        }
    }

    fn from_value_ref(value: &Value) -> Result<Self, ContractFailure> {
        match value {
            Value::Int(value) => Ok(Self::Int(*value)),
            Value::Bool(value) => Ok(Self::Boolean(*value)),
            Value::Object { class, identity } => Ok(Self::Object {
                class: class.clone(),
                identity: *identity,
            }),
            _ => fail(
                "frontend.python.persistent.nested-element-unsupported",
                "persistent collections require flat int, bool, or pass-only source-object elements",
            ),
        }
    }

    fn into_value(self) -> Value {
        match self {
            Self::Int(value) => Value::Int(value),
            Self::Boolean(value) => Value::Bool(value),
            Self::Object { class, identity } => Value::Object { class, identity },
        }
    }
}

fn element_kind(value: &ElementValue) -> ElementKind {
    match value {
        ElementValue::Int(_) => ElementKind::Int,
        ElementValue::Boolean(_) => ElementKind::Boolean,
        ElementValue::Object { class, .. } => ElementKind::Object(class.clone()),
    }
}

fn require_element_kind(
    value: &ElementValue,
    expected: Option<&ElementKind>,
) -> Result<(), ContractFailure> {
    let actual = element_kind(value);
    if expected.is_none_or(|expected| *expected == actual) {
        Ok(())
    } else {
        fail(
            "frontend.python.persistent.heterogeneous-elements",
            format!("persistent collection element kind {actual:?} differs from {expected:?}"),
        )
    }
}

impl PersistentAlgebraError {
    fn into_contract_failure(self) -> ContractFailure {
        match self {
            Self::ElementKindMismatch => ContractFailure {
                code: "frontend.python.persistent.element-kind-mismatch",
                message: "persistent collection element kinds differ".to_owned(),
            },
            Self::EqualityOperandsUnsupported => ContractFailure {
                code: "frontend.python.persistent.equality-operands-unsupported",
                message:
                    "persistent equality requires operands with the same supported runtime kind"
                        .to_owned(),
            },
        }
    }
}

fn require_compatible_kinds_typed(
    left: Option<ElementKind>,
    right: Option<ElementKind>,
) -> Result<(), PersistentAlgebraError> {
    match (left, right) {
        (Some(ElementKind::Int), Some(ElementKind::Int))
        | (Some(ElementKind::Boolean), Some(ElementKind::Boolean)) => Ok(()),
        (Some(ElementKind::Object(left)), Some(ElementKind::Object(right))) if left == right => {
            Ok(())
        }
        (Some(_), Some(_)) => Err(PersistentAlgebraError::ElementKindMismatch),
        _ => Ok(()),
    }
}

fn require_compatible_kinds(
    left: Option<ElementKind>,
    right: Option<ElementKind>,
) -> Result<(), ContractFailure> {
    require_compatible_kinds_typed(left, right)
        .map_err(PersistentAlgebraError::into_contract_failure)
}

fn concatenate_typed(left: Elements, right: Elements) -> Result<Elements, PersistentAlgebraError> {
    require_compatible_kinds_typed(left.kind.clone(), right.kind.clone())?;
    let mut values = left.values;
    let mut right_values = right.values;
    values.append(&mut right_values);
    Ok(Elements {
        kind: left.kind.or(right.kind),
        values,
    })
}

fn concatenate(left: Elements, right: Elements) -> Result<Elements, ContractFailure> {
    concatenate_typed(left, right).map_err(PersistentAlgebraError::into_contract_failure)
}

fn unique(mut elements: Elements) -> Elements {
    let mut unique = Vec::new();
    for value in elements.values {
        if !unique.contains(&value) {
            unique.push(value);
        }
    }
    elements.values = unique;
    elements
}

fn contains(collection: &Value, needle: &Value) -> Result<bool, ContractFailure> {
    let elements = match collection {
        Value::Sequence { elements, .. }
        | Value::PythonSet(elements)
        | Value::PersistentSet(elements) => elements,
        _ => {
            return fail(
                "frontend.python.persistent.membership-receiver-unsupported",
                "membership requires a sequence or set",
            );
        }
    };
    let needle = ElementValue::from_value_ref(needle)?;
    require_element_kind(&needle, elements.kind.as_ref())?;
    Ok(elements.values.contains(&needle))
}

fn comparable_equal_typed(left: &Value, right: &Value) -> Result<bool, PersistentAlgebraError> {
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => Ok(left == right),
        (Value::Bool(left), Value::Bool(right)) => Ok(left == right),
        (Value::Unit, Value::Unit) => Ok(true),
        (
            Value::Object {
                class: left_class,
                identity: left_identity,
            },
            Value::Object {
                class: right_class,
                identity: right_identity,
            },
        ) => Ok(left_class == right_class && left_identity == right_identity),
        (
            Value::Sequence {
                flavor: SequenceFlavor::Persistent,
                elements: left,
            },
            Value::Sequence {
                flavor: SequenceFlavor::Persistent,
                elements: right,
            },
        ) => {
            require_compatible_kinds_typed(left.kind.clone(), right.kind.clone())?;
            Ok(left.values == right.values)
        }
        (Value::PersistentSet(left), Value::PersistentSet(right)) => {
            require_compatible_kinds_typed(left.kind.clone(), right.kind.clone())?;
            Ok(left.values.len() == right.values.len()
                && left.values.iter().all(|value| right.values.contains(value)))
        }
        (Value::Multiset(left), Value::Multiset(right)) => {
            require_compatible_kinds_typed(left.kind.clone(), right.kind.clone())?;
            let mut unmatched = right.values.clone();
            let mut matched = true;
            for value in &left.values {
                if matched {
                    if let Some(index) = unmatched.iter().position(|candidate| candidate == value) {
                        unmatched.remove(index);
                    } else {
                        matched = false;
                    }
                }
            }
            Ok(matched && unmatched.is_empty())
        }
        _ => Err(PersistentAlgebraError::EqualityOperandsUnsupported),
    }
}

fn comparable_equal(left: &Value, right: &Value) -> Result<bool, ContractFailure> {
    comparable_equal_typed(left, right).map_err(PersistentAlgebraError::into_contract_failure)
}

fn object_identical(left: &Value, right: &Value) -> Result<bool, ContractFailure> {
    match (left, right) {
        (Value::Object { .. }, Value::Object { .. }) => Ok(left == right),
        _ => fail(
            "frontend.python.persistent.identity-operands-unsupported",
            "identity comparison is modeled only for pass-only source objects",
        ),
    }
}

fn integer_pair(
    left: &Value,
    right: &Value,
    compare: impl FnOnce(i128, i128) -> bool,
) -> Result<bool, ContractFailure> {
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => Ok(compare(*left, *right)),
        _ => fail(
            "frontend.python.persistent.order-operands-unsupported",
            "ordered comparison requires two integers",
        ),
    }
}

fn apply_type_comment(value: &mut Value, comment: &str) -> Result<(), ContractFailure> {
    let (constructor, kind) = match comment.trim() {
        "PSeq[int]" => ("PSeq", ElementKind::Int),
        "PSeq[bool]" => ("PSeq", ElementKind::Boolean),
        "PSet[int]" => ("PSet", ElementKind::Int),
        "PSet[bool]" => ("PSet", ElementKind::Boolean),
        "PMultiset[int]" => ("PMultiset", ElementKind::Int),
        "PMultiset[bool]" => ("PMultiset", ElementKind::Boolean),
        _ => {
            return fail(
                "frontend.python.persistent.type-comment-unsupported",
                format!("unsupported persistent collection type comment {comment:?}"),
            );
        }
    };
    let (actual, elements) = match value {
        Value::Sequence {
            flavor: SequenceFlavor::Persistent,
            elements,
        } => ("PSeq", elements),
        Value::PersistentSet(elements) => ("PSet", elements),
        Value::Multiset(elements) => ("PMultiset", elements),
        _ => {
            return fail(
                "frontend.python.persistent.type-comment-value-mismatch",
                format!("type comment {comment:?} does not describe its assigned value"),
            );
        }
    };
    if actual != constructor {
        return fail(
            "frontend.python.persistent.type-comment-constructor-mismatch",
            format!("type comment describes {constructor}, but value is {actual}"),
        );
    }
    require_compatible_kinds(elements.kind.clone(), Some(kind.clone()))?;
    elements.kind = Some(kind);
    Ok(())
}

fn is_none_annotation(annotation: Option<&ast::Expr>) -> bool {
    matches!(annotation,
        Some(ast::Expr::Constant(constant)) if constant.value == ast::Constant::None)
}

fn make_obligation(
    id: String,
    conclusion: bool,
    source: &str,
    path: &str,
    offset: u32,
) -> Obligation {
    let prefix = &source[..usize::try_from(offset)
        .unwrap_or(source.len())
        .min(source.len())];
    let line =
        u32::try_from(prefix.bytes().filter(|byte| *byte == b'\n').count() + 1).unwrap_or(u32::MAX);
    let column = u32::try_from(
        prefix
            .rsplit_once('\n')
            .map_or(prefix.len(), |(_, suffix)| suffix.len())
            + 1,
    )
    .unwrap_or(u32::MAX);
    Obligation {
        id,
        expectation: ObligationExpectation::Prove,
        assumptions: Vec::new(),
        conclusion: Term::Bool { value: conclusion },
        path: path.to_owned(),
        byte_offset: offset,
        line,
        column,
    }
}

fn fail<T>(code: &'static str, message: impl Into<String>) -> Result<T, ContractFailure> {
    Err(ContractFailure {
        code,
        message: message.into(),
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use rustpython_parser::{Parse, ast};

    use super::{
        ElementKind, ElementValue, Elements, Evaluator, Value, comparable_equal,
        verify_persistent_collection_module,
    };

    const PREFIX: &str = "from nagini_contracts.contracts import *\n";

    #[test]
    fn proves_the_concrete_persistent_algebra() {
        let source = format!(
            "{PREFIX}\ndef run() -> None:\n    values = PSeq(1, 2, 1)\n    assert values.take(2) == PSeq(1, 2)\n    assert values.drop(1)[0] == 2\n    assert values.update(0, 3)[0] == 3\n    bag = ToMS(values)\n    assert bag.num(1) == 2\n    assert (bag - PMultiset(1)).num(1) == 1\n    items = PSet(1, 1) + PSet(2)\n    assert len(items) == 2\n"
        );
        let verification = verify_persistent_collection_module(&source, "positive.py", &[])
            .unwrap()
            .expect("persistent verifier should claim the module");
        assert!(verification.passed, "{verification:#?}");
    }

    #[test]
    fn shared_toseq_calls_defer_to_the_general_heap_frontend() {
        for expression in [
            "ToSeq([1, 2, 3])",
            "ToSeq((1, 2, 3))",
            "ToSeq(b'123')",
            "ToSeq(range(1, 4))",
        ] {
            let source = format!("def run() -> None:\n    values = {expression}\n");
            let verification = verify_persistent_collection_module(&source, "to_seq.py", &[])
                .expect("routing shared ToSeq must not produce a persistent frontend error");
            assert!(
                verification.is_none(),
                "shared ToSeq expression {expression} was claimed by the persistent frontend"
            );
        }
    }

    #[test]
    fn shared_toseq_remains_available_inside_persistent_algebra() {
        let source = format!(
            "{PREFIX}\ndef run() -> None:\n    values = PSeq(1, 2, 3)\n    copy = ToSeq(values)\n    assert copy == values\n"
        );
        let verification =
            verify_persistent_collection_module(&source, "persistent_to_seq.py", &[])
                .unwrap()
                .expect("a persistent constructor must claim the module");
        assert!(verification.passed, "{verification:#?}");
    }

    #[test]
    fn rejects_custom_object_equality_before_using_set_semantics() {
        let source = format!(
            "{PREFIX}\nclass Item:\n    def __eq__(self, other: object) -> bool:\n        return True\n\ndef run() -> None:\n    values = PSet(Item())\n    assert len(values) == 1\n"
        );
        let error = verify_persistent_collection_module(&source, "custom_eq.py", &[])
            .expect_err("custom equality must refuse");
        assert_eq!(
            error.code,
            "frontend.python.persistent.object-semantics-unsupported"
        );
    }

    #[test]
    fn rejects_custom_object_hashing_before_using_dictionary_semantics() {
        let source = format!(
            "{PREFIX}\nclass Key:\n    def __hash__(self) -> int:\n        return 1\n\ndef run() -> None:\n    mapping = {{Key(): 1}}\n    marker = PSeq(0)\n    assert len(mapping) == len(marker)\n"
        );
        let error = verify_persistent_collection_module(&source, "custom_hash.py", &[])
            .expect_err("custom hashing must refuse");
        assert_eq!(
            error.code,
            "frontend.python.persistent.object-semantics-unsupported"
        );
    }

    #[test]
    fn rejects_mixed_elements_and_unknown_methods() {
        let mixed = format!(
            "{PREFIX}\ndef run() -> None:\n    values = PSeq(1, True)\n    assert len(values) == 2\n"
        );
        assert_eq!(
            verify_persistent_collection_module(&mixed, "mixed.py", &[])
                .expect_err("heterogeneous values must refuse")
                .code,
            "frontend.python.persistent.heterogeneous-elements"
        );

        let unknown = format!(
            "{PREFIX}\ndef run() -> None:\n    values = PSeq(1)\n    other = values.reverse()\n    assert len(other) == 1\n"
        );
        assert_eq!(
            verify_persistent_collection_module(&unknown, "unknown.py", &[])
                .expect_err("unmodeled method must refuse")
                .code,
            "frontend.python.persistent.method-unsupported"
        );
    }

    #[test]
    fn duplicate_dictionary_keys_keep_the_first_slot_and_last_value() {
        let expression = ast::Expr::parse("{1: 2, 1: 3}", "dictionary.py")
            .expect("dictionary expression should parse");
        let classes = BTreeSet::new();
        let mut evaluator = Evaluator {
            classes: &classes,
            environment: Default::default(),
            next_object_identity: 0,
        };
        let Value::Dictionary { keys, values } = evaluator
            .evaluate(&expression)
            .expect("concrete dictionary should evaluate")
        else {
            panic!("dictionary expression returned a non-dictionary value");
        };
        assert_eq!(keys.values, vec![ElementValue::Int(1)]);
        assert_eq!(values.values, vec![ElementValue::Int(3)]);
    }

    #[test]
    fn multiset_equality_compares_every_multiplicity_without_early_exit() {
        let multiset = |values: &[i128]| {
            Value::Multiset(Elements {
                kind: Some(ElementKind::Int),
                values: values.iter().copied().map(ElementValue::Int).collect(),
            })
        };

        for (left, right, expected) in [
            (&[][..], &[][..], true),
            (&[1][..], &[1][..], true),
            (&[1, 2, 1][..], &[2, 1, 1][..], true),
            (&[1, 1][..], &[1][..], false),
            (&[1][..], &[1, 1][..], false),
            (&[1, 2, 3][..], &[1, 4, 3][..], false),
        ] {
            assert_eq!(
                comparable_equal(&multiset(left), &multiset(right))
                    .expect("integer multisets have compatible element kinds"),
                expected,
                "left={left:?}, right={right:?}",
            );
        }
    }

    #[test]
    fn flat_element_conversion_round_trips_every_supported_variant() {
        for value in [
            Value::Int(-7),
            Value::Bool(true),
            Value::Object {
                class: "Item".to_owned(),
                identity: 42,
            },
        ] {
            let element = ElementValue::from_value(value.clone())
                .expect("every flat value must cross the element boundary");
            assert_eq!(element.into_value(), value);
        }
    }

    #[test]
    fn flat_element_conversion_refuses_every_collection_variant() {
        let empty = || Elements {
            kind: None,
            values: Vec::new(),
        };
        for value in [
            Value::Unit,
            Value::Sequence {
                flavor: super::SequenceFlavor::Persistent,
                elements: empty(),
            },
            Value::PythonSet(empty()),
            Value::PersistentSet(empty()),
            Value::Multiset(empty()),
            Value::Dictionary {
                keys: empty(),
                values: empty(),
            },
        ] {
            assert_eq!(
                ElementValue::from_value(value)
                    .expect_err("nested values must not cross the flat element boundary")
                    .code,
                "frontend.python.persistent.nested-element-unsupported",
            );
        }
    }
}
