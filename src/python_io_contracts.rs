//! Source-bound heap semantics for Nagini's linear IO operation protocol.
//!
//! The provider parser derives operation signatures and wrapper effects from the real pinned
//! `io_contracts.py` and `io_builtins.py` sources.  The fixture executor then checks `Open` and
//! wrapper calls as transitions over owned operation relations and linear place tokens.  This is
//! deliberately a closed initial fragment: unsupported control flow or IO primitives refuse
//! verification instead of being erased.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_parser::{Parse, ast};

use crate::python_contracts::ContractFailure;
use crate::python_heap_contracts::HeapContractVerification;
use crate::solver::discharge;
use crate::vc::{Obligation, ObligationExpectation, ObligationResult, Term};

const SCHEMA: &str = "maledictus-python-heap-io-contracts/v1";

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum IoSort {
    Place,
    Int,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Value {
    Place(String),
    Int(i64),
    SymbolicInt(String),
}

#[derive(Clone, Debug)]
enum Node {
    Variable(String),
    Result(usize),
    Integer(i64),
}

#[derive(Clone, Debug)]
struct OperationSpec {
    inputs: Vec<(String, IoSort)>,
    outputs: Vec<(String, IoSort)>,
}

#[derive(Clone, Debug)]
struct WrapperSpec {
    inputs: Vec<(String, IoSort)>,
    returns: Vec<IoSort>,
    existentials: Vec<(String, IoSort)>,
    relation: String,
    relation_input_count: usize,
    relation_arguments: Vec<Node>,
    required_tokens: Vec<(Node, u32)>,
    produced_tokens: Vec<Node>,
    equalities: Vec<(Node, Node)>,
}

#[derive(Clone, Debug)]
struct ProviderCatalog {
    operations: BTreeMap<String, OperationSpec>,
    wrappers: BTreeMap<String, WrapperSpec>,
}

struct ExistsSpec<'a> {
    bindings: Vec<(String, IoSort)>,
    body: &'a ast::Expr,
}

#[derive(Clone, Debug)]
struct UserOperation {
    inputs: Vec<(String, IoSort)>,
    outputs: Vec<(String, IoSort)>,
    existentials: Vec<(String, IoSort)>,
    relations: Vec<(String, Vec<Node>)>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RelationFact {
    operation: String,
    arguments: Vec<Value>,
}

#[derive(Clone, Debug)]
enum TokenKind {
    Bounded(u32),
    Unbounded,
}

#[derive(Clone, Debug, Default)]
struct State {
    tokens: BTreeMap<Value, TokenKind>,
    relations: BTreeSet<RelationFact>,
    values: BTreeMap<String, Value>,
    next_fresh: u64,
}

impl State {
    fn fresh(&mut self, sort: &IoSort, label: &str) -> Value {
        self.next_fresh += 1;
        match sort {
            IoSort::Place => Value::Place(format!("{label}#{}", self.next_fresh)),
            IoSort::Int => Value::SymbolicInt(format!("{label}#{}", self.next_fresh)),
        }
    }
}

#[derive(Clone, Debug, Default)]
struct Bindings {
    canonical: BTreeMap<String, String>,
    wrappers: BTreeMap<String, String>,
    operations: BTreeMap<String, String>,
}

pub(crate) fn has_pinned_io_imports(source: &str, path: &str) -> Result<bool, ContractFailure> {
    let suite = parse(source, path)?;
    Ok(suite.iter().any(|statement| {
        matches!(statement,
        ast::Stmt::ImportFrom(import)
            if import.level.is_none_or(|level| level == 0_u32)
                && import.module.as_ref().is_some_and(|module| matches!(module.as_str(),
                    "nagini_contracts.io_contracts" | "nagini_contracts.io_builtins")))
    }))
}

pub(crate) fn verify_pinned_io_module(
    source: &str,
    path: &str,
    io_contracts_source: &str,
    io_builtins_source: &str,
    requested_symbols: &[String],
) -> Result<Option<HeapContractVerification>, ContractFailure> {
    let suite = parse(source, path)?;
    let bindings = source_bindings(&suite)?;
    if bindings.wrappers.is_empty() || bindings.operations.is_empty() {
        return Ok(None);
    }
    validate_io_contracts_provider(io_contracts_source)?;
    let provider = parse_builtins_provider(io_builtins_source, &bindings)?;
    let user_operations = parse_user_operations(&suite, &bindings, &provider.operations)?;

    let declared = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => Some(function.name.to_string()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    if requested_symbols
        .iter()
        .any(|name| !declared.contains(name))
    {
        return Ok(None);
    }

    let mut methods = Vec::new();
    let mut obligations = Vec::new();
    for statement in &suite {
        let ast::Stmt::FunctionDef(function) = statement else {
            continue;
        };
        if user_operations.contains_key(function.name.as_str()) {
            continue;
        }
        if !requested_symbols.is_empty()
            && !requested_symbols
                .iter()
                .any(|name| name.as_str() == function.name.as_str())
        {
            continue;
        }
        verify_client_function(
            function,
            &bindings,
            &provider.wrappers,
            &user_operations,
            source,
            path,
        )?;
        methods.push(function.name.to_string());
        obligations.push(make_obligation(
            format!("{}:io-linear-transition-proof", function.name),
            source,
            path,
            function.range.start().into(),
        ));
    }
    if obligations.is_empty() {
        return Ok(None);
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
        schema: SCHEMA.to_owned(),
        path: path.to_owned(),
        methods,
        obligations,
        passed,
    }))
}

fn parse(source: &str, path: &str) -> Result<ast::Suite, ContractFailure> {
    ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })
}

fn failure(code: &'static str, message: impl Into<String>) -> ContractFailure {
    ContractFailure {
        code,
        message: message.into(),
    }
}

fn validate_io_contracts_provider(source: &str) -> Result<(), ContractFailure> {
    let suite = parse(source, "nagini_contracts/io_contracts.py")?;
    let classes = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ClassDef(class) => Some(class.name.as_str()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let functions = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => Some(function.name.as_str()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let missing = ["Place"]
        .into_iter()
        .filter(|name| !classes.contains(name))
        .chain(
            ["Open", "IOOperation", "token"]
                .into_iter()
                .filter(|name| !functions.contains(name)),
        )
        .chain(
            (1..=15)
                .map(|arity| format!("IOExists{arity}"))
                .filter_map(|name| {
                    (!classes.contains(name.as_str()))
                        .then_some(Box::leak(name.into_boxed_str()) as &str)
                }),
        )
        .map(str::to_owned)
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        return Err(failure(
            "frontend.python.io.provider-interface-incomplete",
            format!(
                "pinned io_contracts provider is missing exports: {}",
                missing.join(", ")
            ),
        ));
    }
    Ok(())
}

fn source_bindings(suite: &[ast::Stmt]) -> Result<Bindings, ContractFailure> {
    let mut bindings = Bindings::default();
    for statement in suite {
        if let ast::Stmt::ImportFrom(import) = statement {
            if !import.level.is_none_or(|level| level == 0_u32) {
                continue;
            }
            match import.module.as_ref().map(|module| module.as_str()) {
                Some("nagini_contracts.contracts") => {
                    for alias in &import.names {
                        if matches!(
                            alias.name.as_str(),
                            "Assert" | "Ensures" | "Requires" | "Result"
                        ) {
                            bindings.canonical.insert(
                                alias.asname.as_ref().unwrap_or(&alias.name).to_string(),
                                alias.name.to_string(),
                            );
                        }
                    }
                }
                Some("nagini_contracts.io_contracts") => {
                    for alias in &import.names {
                        if alias.name.as_str() == "*" {
                            for name in [
                                "IOOperation",
                                "Place",
                                "IOExists1",
                                "IOExists2",
                                "IOExists3",
                                "IOExists4",
                                "IOExists5",
                                "IOExists6",
                                "IOExists7",
                                "IOExists8",
                                "IOExists9",
                                "IOExists10",
                                "IOExists11",
                                "IOExists12",
                                "IOExists13",
                                "IOExists14",
                                "IOExists15",
                                "Open",
                                "Terminates",
                                "TerminationMeasure",
                                "token",
                            ] {
                                bindings.canonical.insert(name.to_owned(), name.to_owned());
                            }
                        } else {
                            bindings.canonical.insert(
                                alias.asname.as_ref().unwrap_or(&alias.name).to_string(),
                                alias.name.to_string(),
                            );
                        }
                    }
                }
                Some("nagini_contracts.io_builtins") => {
                    for alias in &import.names {
                        let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
                        let provider = alias.name.to_string();
                        if provider.ends_with("_io") {
                            bindings.operations.insert(local, provider);
                        } else {
                            bindings.wrappers.insert(local, provider);
                        }
                    }
                }
                _ => {}
            }
        }
    }
    for statement in suite {
        match statement {
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    remove_bound_names(target, &mut bindings);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                remove_bound_names(&assignment.target, &mut bindings);
            }
            ast::Stmt::ClassDef(class) => remove_binding(class.name.as_str(), &mut bindings),
            ast::Stmt::FunctionDef(function)
                if !has_decorator(function, &bindings, "IOOperation") =>
            {
                remove_binding(function.name.as_str(), &mut bindings);
            }
            ast::Stmt::FunctionDef(_) => {}
            _ => {}
        }
    }
    if !bindings
        .canonical
        .values()
        .any(|name| name == "IOOperation")
        || !bindings.canonical.values().any(|name| name == "Place")
    {
        return Err(failure(
            "frontend.python.io.canonical-bindings-missing",
            "heap IO verification requires canonical IOOperation and Place bindings",
        ));
    }
    Ok(bindings)
}

fn remove_bound_names(expression: &ast::Expr, bindings: &mut Bindings) {
    match expression {
        ast::Expr::Name(name) => remove_binding(name.id.as_str(), bindings),
        ast::Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                remove_bound_names(element, bindings);
            }
        }
        ast::Expr::List(list) => {
            for element in &list.elts {
                remove_bound_names(element, bindings);
            }
        }
        _ => {}
    }
}

fn remove_binding(name: &str, bindings: &mut Bindings) {
    bindings.canonical.remove(name);
    bindings.operations.remove(name);
    bindings.wrappers.remove(name);
}

fn has_decorator(function: &ast::StmtFunctionDef, bindings: &Bindings, expected: &str) -> bool {
    function.decorator_list.iter().any(|decorator| {
        matches!(decorator, ast::Expr::Name(name)
            if bindings.canonical.get(name.id.as_str()).is_some_and(|bound| bound == expected))
    })
}

fn parse_builtins_provider(
    source: &str,
    bindings: &Bindings,
) -> Result<ProviderCatalog, ContractFailure> {
    let suite = parse(source, "nagini_contracts/io_builtins.py")?;
    let needed_operations = bindings
        .operations
        .values()
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut operations = BTreeMap::new();
    for statement in &suite {
        let ast::Stmt::FunctionDef(function) = statement else {
            continue;
        };
        if needed_operations.contains(function.name.as_str())
            && function
                .decorator_list
                .iter()
                .any(|decorator| name(decorator) == Some("IOOperation"))
        {
            operations.insert(
                function.name.to_string(),
                parse_operation_signature(function)?,
            );
        }
    }
    for operation in &needed_operations {
        if !operations.contains_key(operation) {
            return Err(failure(
                "frontend.python.io.provider-operation-missing",
                format!("pinned io_builtins provider does not declare {operation}"),
            ));
        }
    }
    let mut wrappers = BTreeMap::new();
    for provider_name in bindings.wrappers.values() {
        let function = suite
            .iter()
            .find_map(|statement| match statement {
                ast::Stmt::FunctionDef(function) if function.name.as_str() == provider_name => {
                    Some(function)
                }
                _ => None,
            })
            .ok_or_else(|| {
                failure(
                    "frontend.python.io.provider-wrapper-missing",
                    format!("pinned io_builtins provider does not declare {provider_name}"),
                )
            })?;
        wrappers.insert(provider_name.clone(), parse_wrapper(function, &operations)?);
    }
    Ok(ProviderCatalog {
        operations,
        wrappers,
    })
}

fn parse_operation_signature(
    function: &ast::StmtFunctionDef,
) -> Result<OperationSpec, ContractFailure> {
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    for argument in function.args.posonlyargs.iter().chain(&function.args.args) {
        let sort = parse_sort(argument.def.annotation.as_deref())?;
        if argument.default.is_some() {
            if !argument.default.as_deref().is_some_and(is_result_call) {
                return Err(failure(
                    "frontend.python.io.provider-output-default-invalid",
                    format!(
                        "operation {} output {} is not defaulted to Result()",
                        function.name, argument.def.arg
                    ),
                ));
            }
            outputs.push((argument.def.arg.to_string(), sort));
        } else {
            inputs.push((argument.def.arg.to_string(), sort));
        }
    }
    if inputs.first().map(|(_, sort)| sort) != Some(&IoSort::Place)
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == "bool")
    {
        return Err(failure(
            "frontend.python.io.provider-operation-signature-invalid",
            format!(
                "operation {} does not have Place preset and bool result",
                function.name
            ),
        ));
    }
    let terminates = function.body.iter().any(|statement| {
        matches!(statement,
        ast::Stmt::Expr(expression)
            if matches!(expression.value.as_ref(), ast::Expr::Call(call)
                if name(&call.func) == Some("Terminates")
                    && matches!(call.args.as_slice(), [ast::Expr::Constant(constant)]
                        if constant.value == ast::Constant::Bool(true))))
    });
    if !terminates {
        return Err(failure(
            "frontend.python.io.provider-operation-not-total",
            format!(
                "operation {} does not declare Terminates(True)",
                function.name
            ),
        ));
    }
    Ok(OperationSpec { inputs, outputs })
}

fn parse_wrapper(
    function: &ast::StmtFunctionDef,
    operations: &BTreeMap<String, OperationSpec>,
) -> Result<WrapperSpec, ContractFailure> {
    let decorators = function
        .decorator_list
        .iter()
        .filter_map(name)
        .collect::<BTreeSet<_>>();
    if !decorators.contains("Ghost") || !decorators.contains("ContractOnly") {
        return Err(failure(
            "frontend.python.io.provider-wrapper-not-contract-only",
            format!("wrapper {} must be Ghost and ContractOnly", function.name),
        ));
    }
    let inputs = function
        .args
        .posonlyargs
        .iter()
        .chain(&function.args.args)
        .map(|argument| {
            Ok((
                argument.def.arg.to_string(),
                parse_sort(argument.def.annotation.as_deref())?,
            ))
        })
        .collect::<Result<Vec<_>, ContractFailure>>()?;
    let returns = parse_return_sorts(function.returns.as_deref())?;
    let invocation = function
        .body
        .iter()
        .find_map(|statement| match statement {
            ast::Stmt::Expr(expression) => io_exists_invocation(&expression.value),
            _ => None,
        })
        .ok_or_else(|| {
            failure(
                "frontend.python.io.provider-wrapper-contract-missing",
                format!("wrapper {} has no IOExists contract", function.name),
            )
        })?;
    let exists = parse_exists(invocation)?;
    let tuple = match exists.body {
        ast::Expr::Tuple(tuple) => &tuple.elts,
        _ => {
            return Err(failure(
                "frontend.python.io.provider-wrapper-contract-invalid",
                "IOExists wrapper body must be a contract tuple",
            ));
        }
    };
    let requires = named_call_argument(tuple, "Requires")?;
    let ensures = named_call_argument(tuple, "Ensures")?;
    let mut required_tokens = Vec::new();
    let mut relation = None;
    let mut termination = false;
    for conjunct in flatten_and(requires) {
        let ast::Expr::Call(call) = conjunct else {
            return Err(failure(
                "frontend.python.io.provider-wrapper-precondition-unsupported",
                "wrapper precondition conjunct is not a call",
            ));
        };
        match name(&call.func) {
            Some("token") => required_tokens.push(parse_token_requirement(call)?),
            Some("MustTerminate") if matches!(call.args.as_slice(), [ast::Expr::Constant(c)] if c.value == ast::Constant::Int(1.into())) => {
                termination = true
            }
            Some(operation) if operations.contains_key(operation) => {
                if relation.is_some() {
                    return Err(failure(
                        "frontend.python.io.provider-wrapper-relation-ambiguous",
                        "wrapper requires more than one operation relation",
                    ));
                }
                relation = Some((
                    operation.to_owned(),
                    call.args
                        .iter()
                        .map(parse_node)
                        .collect::<Result<Vec<_>, _>>()?,
                ));
            }
            _ => {
                return Err(failure(
                    "frontend.python.io.provider-wrapper-precondition-unsupported",
                    "unsupported wrapper precondition",
                ));
            }
        }
    }
    if !termination {
        return Err(failure(
            "frontend.python.io.provider-wrapper-termination-missing",
            format!("wrapper {} omits MustTerminate(1)", function.name),
        ));
    }
    let mut produced_tokens = Vec::new();
    let mut equalities = Vec::new();
    for conjunct in flatten_and(ensures) {
        match conjunct {
            ast::Expr::Call(call) if name(&call.func) == Some("token") => {
                let [argument] = call.args.as_slice() else {
                    return Err(failure(
                        "frontend.python.io.provider-token-shape-invalid",
                        "produced token must have exactly one place",
                    ));
                };
                produced_tokens.push(parse_node(argument)?);
            }
            ast::Expr::Compare(compare)
                if compare.ops.as_slice() == [ast::CmpOp::Eq] && compare.comparators.len() == 1 =>
            {
                equalities.push((
                    parse_node(&compare.left)?,
                    parse_node(&compare.comparators[0])?,
                ));
            }
            _ => {
                return Err(failure(
                    "frontend.python.io.provider-wrapper-postcondition-unsupported",
                    "unsupported wrapper postcondition",
                ));
            }
        }
    }
    let (relation, relation_arguments) = relation.ok_or_else(|| {
        failure(
            "frontend.python.io.provider-wrapper-relation-missing",
            format!("wrapper {} has no operation relation", function.name),
        )
    })?;
    let operation = &operations[&relation];
    let expected_arity = operation.inputs.len() + operation.outputs.len();
    if relation_arguments.len() != expected_arity {
        return Err(failure(
            "frontend.python.io.provider-wrapper-relation-arity",
            format!(
                "wrapper {} supplies {} arguments to {} but provider declares {expected_arity}",
                function.name,
                relation_arguments.len(),
                relation
            ),
        ));
    }
    Ok(WrapperSpec {
        inputs,
        returns,
        existentials: exists.bindings,
        relation,
        relation_input_count: operation.inputs.len(),
        relation_arguments,
        required_tokens,
        produced_tokens,
        equalities,
    })
}

fn io_exists_invocation(expression: &ast::Expr) -> Option<&ast::ExprCall> {
    let ast::Expr::Call(invocation) = expression else {
        return None;
    };
    let ast::Expr::Call(constructor) = invocation.func.as_ref() else {
        return None;
    };
    name(&constructor.func)
        .is_some_and(|name| name.starts_with("IOExists"))
        .then_some(invocation)
}

fn parse_exists(invocation: &ast::ExprCall) -> Result<ExistsSpec<'_>, ContractFailure> {
    let ast::Expr::Call(constructor) = invocation.func.as_ref() else {
        unreachable!()
    };
    let [ast::Expr::Lambda(lambda)] = invocation.args.as_slice() else {
        return Err(failure(
            "frontend.python.io.exists-shape-unsupported",
            "IOExists must receive one lambda",
        ));
    };
    let sorts = constructor
        .args
        .iter()
        .map(|arg| parse_sort(Some(arg)))
        .collect::<Result<Vec<_>, _>>()?;
    let names = lambda
        .args
        .posonlyargs
        .iter()
        .chain(&lambda.args.args)
        .map(|arg| arg.def.arg.to_string())
        .collect::<Vec<_>>();
    if sorts.len() != names.len() {
        return Err(failure(
            "frontend.python.io.exists-arity-mismatch",
            "IOExists domains and lambda parameters differ",
        ));
    }
    Ok(ExistsSpec {
        bindings: names.into_iter().zip(sorts).collect(),
        body: &lambda.body,
    })
}

fn named_call_argument<'a>(
    expressions: &'a [ast::Expr],
    expected: &str,
) -> Result<&'a ast::Expr, ContractFailure> {
    expressions
        .iter()
        .find_map(|expression| match expression {
            ast::Expr::Call(call) if name(&call.func) == Some(expected) && call.args.len() == 1 => {
                Some(&call.args[0])
            }
            _ => None,
        })
        .ok_or_else(|| {
            failure(
                "frontend.python.io.provider-wrapper-contract-invalid",
                format!("wrapper contract omits {expected}"),
            )
        })
}

fn flatten_and(expression: &ast::Expr) -> Vec<&ast::Expr> {
    match expression {
        ast::Expr::BoolOp(boolean) if boolean.op == ast::BoolOp::And => {
            boolean.values.iter().flat_map(flatten_and).collect()
        }
        _ => vec![expression],
    }
}

fn parse_token_requirement(call: &ast::ExprCall) -> Result<(Node, u32), ContractFailure> {
    match call.args.as_slice() {
        [place, ast::Expr::Constant(measure)] => {
            let ast::Constant::Int(value) = &measure.value else {
                return Err(failure(
                    "frontend.python.io.provider-token-measure-invalid",
                    "token measure must be an integer literal",
                ));
            };
            let measure = value.to_string().parse::<u32>().map_err(|_| {
                failure(
                    "frontend.python.io.provider-token-measure-invalid",
                    "token measure must fit u32",
                )
            })?;
            Ok((parse_node(place)?, measure))
        }
        _ => Err(failure(
            "frontend.python.io.provider-token-shape-invalid",
            "required token must have place and measure",
        )),
    }
}

fn parse_node(expression: &ast::Expr) -> Result<Node, ContractFailure> {
    match expression {
        ast::Expr::Name(name) => Ok(Node::Variable(name.id.to_string())),
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Int(value) => value
                .to_string()
                .parse::<i64>()
                .map(Node::Integer)
                .map_err(|_| {
                    failure(
                        "frontend.python.io.integer-out-of-range",
                        "integer literal does not fit i64",
                    )
                }),
            _ => Err(failure(
                "frontend.python.io.value-expression-unsupported",
                "only integer constants are supported IO values",
            )),
        },
        ast::Expr::Call(call) if is_result_call(expression) => Ok(Node::Result(0)),
        ast::Expr::Subscript(subscript) if is_result_call(&subscript.value) => {
            let ast::Expr::Constant(index) = subscript.slice.as_ref() else {
                return Err(failure(
                    "frontend.python.io.result-index-invalid",
                    "Result index must be an integer literal",
                ));
            };
            let ast::Constant::Int(index) = &index.value else {
                return Err(failure(
                    "frontend.python.io.result-index-invalid",
                    "Result index must be an integer literal",
                ));
            };
            index
                .to_string()
                .parse::<usize>()
                .map(Node::Result)
                .map_err(|_| {
                    failure(
                        "frontend.python.io.result-index-invalid",
                        "Result index is out of range",
                    )
                })
        }
        _ => Err(failure(
            "frontend.python.io.value-expression-unsupported",
            "unsupported IO value expression",
        )),
    }
}

fn is_result_call(expression: &ast::Expr) -> bool {
    matches!(expression, ast::Expr::Call(call)
        if name(&call.func) == Some("Result") && call.args.is_empty() && call.keywords.is_empty())
}

fn parse_sort(annotation: Option<&ast::Expr>) -> Result<IoSort, ContractFailure> {
    match annotation {
        Some(ast::Expr::Name(name)) if name.id.as_str() == "Place" => Ok(IoSort::Place),
        Some(ast::Expr::Name(name)) if name.id.as_str() == "int" => Ok(IoSort::Int),
        _ => Err(failure(
            "frontend.python.io.type-unsupported",
            "minimal heap IO fragment supports only Place and int",
        )),
    }
}

fn parse_return_sorts(annotation: Option<&ast::Expr>) -> Result<Vec<IoSort>, ContractFailure> {
    let Some(annotation) = annotation else {
        return Err(failure(
            "frontend.python.io.wrapper-return-missing",
            "IO wrapper requires a return annotation",
        ));
    };
    if let ast::Expr::Subscript(tuple) = annotation
        && name(&tuple.value) == Some("Tuple")
    {
        let ast::Expr::Tuple(elements) = tuple.slice.as_ref() else {
            return Err(failure(
                "frontend.python.io.wrapper-return-unsupported",
                "Tuple result must have explicit elements",
            ));
        };
        return elements
            .elts
            .iter()
            .map(|element| parse_sort(Some(element)))
            .collect();
    }
    Ok(vec![parse_sort(Some(annotation))?])
}

fn name(expression: &ast::Expr) -> Option<&str> {
    match expression {
        ast::Expr::Name(name) => Some(name.id.as_str()),
        _ => None,
    }
}

fn parse_user_operations(
    suite: &[ast::Stmt],
    bindings: &Bindings,
    provider_operations: &BTreeMap<String, OperationSpec>,
) -> Result<BTreeMap<String, UserOperation>, ContractFailure> {
    let mut result = BTreeMap::new();
    for statement in suite {
        let ast::Stmt::FunctionDef(function) = statement else {
            continue;
        };
        if !has_decorator(function, bindings, "IOOperation") {
            continue;
        }
        let signature = parse_operation_signature(function)?;
        let returned = function
            .body
            .iter()
            .find_map(|statement| match statement {
                ast::Stmt::Return(returned) => {
                    returned.value.as_deref().and_then(io_exists_invocation)
                }
                _ => None,
            })
            .ok_or_else(|| {
                failure(
                    "frontend.python.io.operation-body-unsupported",
                    format!("IO operation {} must return IOExists", function.name),
                )
            })?;
        let exists = parse_exists(returned)?;
        let mut relations = Vec::new();
        for conjunct in flatten_and(exists.body) {
            let ast::Expr::Call(call) = conjunct else {
                return Err(failure(
                    "frontend.python.io.operation-body-unsupported",
                    "IO operation body must be a conjunction of operation relations",
                ));
            };
            let local = name(&call.func).ok_or_else(|| {
                failure(
                    "frontend.python.io.operation-body-unsupported",
                    "operation relation must be a canonical name",
                )
            })?;
            let provider = bindings.operations.get(local).ok_or_else(|| {
                failure(
                    "frontend.python.io.operation-relation-unbound",
                    format!("{local} is not a canonical imported IO operation"),
                )
            })?;
            let declared = provider_operations.get(provider).ok_or_else(|| {
                failure(
                    "frontend.python.io.provider-operation-missing",
                    format!("provider operation {provider} is missing"),
                )
            })?;
            if call.args.len() != declared.inputs.len() + declared.outputs.len() {
                return Err(failure(
                    "frontend.python.io.operation-relation-arity",
                    format!("relation {local} has the wrong arity"),
                ));
            }
            relations.push((
                provider.clone(),
                call.args
                    .iter()
                    .map(parse_node)
                    .collect::<Result<Vec<_>, _>>()?,
            ));
        }
        result.insert(
            function.name.to_string(),
            UserOperation {
                inputs: signature.inputs,
                outputs: signature.outputs,
                existentials: exists.bindings,
                relations,
            },
        );
    }
    Ok(result)
}

fn verify_client_function(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    wrappers: &BTreeMap<String, WrapperSpec>,
    operations: &BTreeMap<String, UserOperation>,
    _source: &str,
    _path: &str,
) -> Result<(), ContractFailure> {
    if !function.decorator_list.is_empty() {
        return Err(failure(
            "frontend.python.io.client-decorator-unsupported",
            format!("IO client {} has unsupported decorators", function.name),
        ));
    }
    let mut state = State::default();
    for argument in function.args.posonlyargs.iter().chain(&function.args.args) {
        let sort = parse_sort(argument.def.annotation.as_deref())?;
        let value = state.fresh(&sort, argument.def.arg.as_str());
        state.values.insert(argument.def.arg.to_string(), value);
    }
    let contract = function
        .body
        .iter()
        .find_map(|statement| match statement {
            ast::Stmt::Expr(expression) => io_exists_invocation(&expression.value),
            _ => None,
        })
        .ok_or_else(|| {
            failure(
                "frontend.python.io.client-contract-missing",
                format!("IO client {} has no IOExists contract", function.name),
            )
        })?;
    let exists = parse_exists(contract)?;
    for (name, sort) in exists.bindings {
        let value = state.fresh(&sort, &name);
        state.values.insert(name, value);
    }
    let contract_items = match exists.body {
        ast::Expr::Tuple(tuple) => &tuple.elts,
        _ => {
            return Err(failure(
                "frontend.python.io.client-contract-unsupported",
                "client IOExists body must be a contract tuple",
            ));
        }
    };
    let requires = named_call_argument(contract_items, "Requires")?;
    let ensures = named_call_argument(contract_items, "Ensures")?;
    inhale_requirements(requires, bindings, operations, &mut state)?;
    let mut return_value = None;
    let mut seen_contract = false;
    for statement in &function.body {
        if matches!(statement, ast::Stmt::Expr(expression) if io_exists_invocation(&expression.value).is_some())
        {
            if seen_contract {
                return Err(failure(
                    "frontend.python.io.client-contract-duplicate",
                    "client has multiple IOExists contracts",
                ));
            }
            seen_contract = true;
            continue;
        }
        match statement {
            ast::Stmt::Expr(expression) => {
                let ast::Expr::Call(call) = expression.value.as_ref() else {
                    return Err(failure(
                        "frontend.python.io.statement-unsupported",
                        "only IO calls and assertions are supported statements",
                    ));
                };
                let called = name(&call.func).ok_or_else(|| {
                    failure(
                        "frontend.python.io.call-target-unsupported",
                        "IO calls require a canonical name",
                    )
                })?;
                if bindings
                    .canonical
                    .get(called)
                    .is_some_and(|bound| bound == "Open")
                {
                    apply_open(call, operations, &mut state)?;
                } else if bindings
                    .canonical
                    .get(called)
                    .is_some_and(|bound| bound == "Assert")
                {
                    verify_assert(call, &state)?;
                } else if let Some(provider) = bindings.wrappers.get(called) {
                    let outputs = apply_wrapper(provider, call, wrappers, &mut state)?;
                    if !outputs.is_empty() {
                        return Err(failure(
                            "frontend.python.io.call-result-discarded",
                            format!("wrapper {called} result is discarded"),
                        ));
                    }
                } else {
                    return Err(failure(
                        "frontend.python.io.statement-unsupported",
                        format!("unsupported IO statement call {called}"),
                    ));
                }
            }
            ast::Stmt::Assign(assignment) => {
                let [target] = assignment.targets.as_slice() else {
                    return Err(failure(
                        "frontend.python.io.assignment-target-unsupported",
                        "IO assignment requires one target",
                    ));
                };
                let ast::Expr::Call(call) = assignment.value.as_ref() else {
                    return Err(failure(
                        "frontend.python.io.assignment-value-unsupported",
                        "IO assignment must call a wrapper",
                    ));
                };
                let called = name(&call.func).ok_or_else(|| {
                    failure(
                        "frontend.python.io.call-target-unsupported",
                        "IO calls require a canonical name",
                    )
                })?;
                let provider = bindings.wrappers.get(called).ok_or_else(|| {
                    failure(
                        "frontend.python.io.wrapper-unbound",
                        format!("{called} is not a canonical imported wrapper"),
                    )
                })?;
                let outputs = apply_wrapper(provider, call, wrappers, &mut state)?;
                bind_assignment(target, outputs, &mut state)?;
            }
            ast::Stmt::Return(returned) => {
                let value = returned.value.as_deref().ok_or_else(|| {
                    failure(
                        "frontend.python.io.return-value-missing",
                        "IO client must return its post-place",
                    )
                })?;
                return_value = Some(eval_expression(value, &state)?);
            }
            ast::Stmt::Import(_) | ast::Stmt::ImportFrom(_) => {}
            _ => {
                return Err(failure(
                    "frontend.python.io.control-flow-unsupported",
                    "minimal heap IO fragment supports straight-line operation composition only",
                ));
            }
        }
    }
    verify_ensures(ensures, return_value.as_ref(), &state)
}

fn inhale_requirements(
    expression: &ast::Expr,
    bindings: &Bindings,
    operations: &BTreeMap<String, UserOperation>,
    state: &mut State,
) -> Result<(), ContractFailure> {
    for conjunct in flatten_and(expression) {
        let ast::Expr::Call(call) = conjunct else {
            return Err(failure(
                "frontend.python.io.client-precondition-unsupported",
                "client precondition must contain token and operation calls",
            ));
        };
        let called = name(&call.func).ok_or_else(|| {
            failure(
                "frontend.python.io.client-precondition-unsupported",
                "precondition call target is not canonical",
            )
        })?;
        if bindings
            .canonical
            .get(called)
            .is_some_and(|bound| bound == "token")
        {
            let (place, kind) = match call.args.as_slice() {
                [place] => (eval_expression(place, state)?, TokenKind::Unbounded),
                [place, ast::Expr::Constant(measure)] => {
                    let ast::Constant::Int(measure) = &measure.value else {
                        return Err(failure(
                            "frontend.python.io.token-measure-invalid",
                            "token measure must be an integer literal",
                        ));
                    };
                    let measure = measure.to_string().parse::<u32>().map_err(|_| {
                        failure(
                            "frontend.python.io.token-measure-invalid",
                            "token measure does not fit u32",
                        )
                    })?;
                    (eval_expression(place, state)?, TokenKind::Bounded(measure))
                }
                _ => {
                    return Err(failure(
                        "frontend.python.io.token-shape-invalid",
                        "token requires place and optional measure",
                    ));
                }
            };
            if state.tokens.insert(place, kind).is_some() {
                return Err(failure(
                    "frontend.python.io.token-duplicated",
                    "precondition duplicates ownership of one place token",
                ));
            }
        } else if operations.contains_key(called) {
            let args = call
                .args
                .iter()
                .map(|argument| eval_expression(argument, state))
                .collect::<Result<Vec<_>, _>>()?;
            let fact = RelationFact {
                operation: called.to_owned(),
                arguments: args,
            };
            if !state.relations.insert(fact) {
                return Err(failure(
                    "frontend.python.io.relation-duplicated",
                    "precondition duplicates an operation relation",
                ));
            }
        } else {
            return Err(failure(
                "frontend.python.io.client-precondition-unsupported",
                format!("unsupported precondition {called}"),
            ));
        }
    }
    Ok(())
}

fn apply_open(
    call: &ast::ExprCall,
    operations: &BTreeMap<String, UserOperation>,
    state: &mut State,
) -> Result<(), ContractFailure> {
    let [ast::Expr::Call(operation_call)] = call.args.as_slice() else {
        return Err(failure(
            "frontend.python.io.open-shape-invalid",
            "Open requires one IO operation call",
        ));
    };
    let operation_name = name(&operation_call.func).ok_or_else(|| {
        failure(
            "frontend.python.io.open-target-invalid",
            "Open target must be a source IO operation",
        )
    })?;
    let operation = operations.get(operation_name).ok_or_else(|| {
        failure(
            "frontend.python.io.open-target-invalid",
            format!("{operation_name} is not a source IO operation"),
        )
    })?;
    let explicit = operation_call
        .args
        .iter()
        .map(|argument| eval_expression(argument, state))
        .collect::<Result<Vec<_>, _>>()?;
    let matching = state
        .relations
        .iter()
        .filter(|fact| {
            fact.operation == operation_name
                && fact.arguments.len() == operation.inputs.len() + operation.outputs.len()
                && fact.arguments.starts_with(&explicit)
        })
        .cloned()
        .collect::<Vec<_>>();
    let [owned] = matching.as_slice() else {
        return Err(failure(
            "frontend.python.io.open-relation-not-owned",
            format!("Open({operation_name}) does not identify exactly one owned relation"),
        ));
    };
    state.relations.remove(owned);
    let mut env = BTreeMap::new();
    for ((name, _), value) in operation
        .inputs
        .iter()
        .chain(&operation.outputs)
        .zip(&owned.arguments)
    {
        env.insert(name.clone(), value.clone());
    }
    for (name, sort) in &operation.existentials {
        env.entry(name.clone())
            .or_insert_with(|| state.fresh(sort, name));
    }
    for (provider, arguments) in &operation.relations {
        let arguments = arguments
            .iter()
            .map(|node| eval_node(node, &env, &[]))
            .collect::<Result<Vec<_>, _>>()?;
        state.relations.insert(RelationFact {
            operation: provider.clone(),
            arguments,
        });
    }
    Ok(())
}

fn apply_wrapper(
    provider_name: &str,
    call: &ast::ExprCall,
    wrappers: &BTreeMap<String, WrapperSpec>,
    state: &mut State,
) -> Result<Vec<Value>, ContractFailure> {
    let wrapper = wrappers.get(provider_name).ok_or_else(|| {
        failure(
            "frontend.python.io.provider-wrapper-missing",
            format!("provider wrapper {provider_name} is missing"),
        )
    })?;
    if !call.keywords.is_empty() || call.args.len() != wrapper.inputs.len() {
        return Err(failure(
            "frontend.python.io.wrapper-call-arity",
            format!("wrapper {provider_name} has wrong call arity"),
        ));
    }
    let mut env = BTreeMap::new();
    for ((parameter, expected), argument) in wrapper.inputs.iter().zip(&call.args) {
        let value = eval_expression(argument, state)?;
        ensure_sort(&value, expected)?;
        env.insert(parameter.clone(), value);
    }
    for (name, sort) in &wrapper.existentials {
        env.insert(name.clone(), state.fresh(sort, name));
    }
    let mut outputs = wrapper
        .returns
        .iter()
        .enumerate()
        .map(|(index, sort)| state.fresh(sort, &format!("{provider_name}.result.{index}")))
        .collect::<Vec<_>>();
    let input_prefix = wrapper.relation_arguments[..wrapper.relation_input_count]
        .iter()
        .map(|node| eval_node(node, &env, &outputs))
        .collect::<Result<Vec<_>, _>>()?;
    let owned_relation = state
        .relations
        .iter()
        .find(|fact| {
            fact.operation == wrapper.relation
                && fact.arguments.len() == wrapper.relation_arguments.len()
                && fact.arguments.starts_with(&input_prefix)
        })
        .cloned()
        .ok_or_else(|| failure(
            "frontend.python.io.operation-relation-not-owned",
            format!(
                "wrapper {provider_name} has no owned {} relation with input prefix {input_prefix:?}",
                wrapper.relation
            ),
        ))?;
    for (node, actual) in wrapper
        .relation_arguments
        .iter()
        .zip(&owned_relation.arguments)
    {
        unify_node_with_value(node, actual, &mut env, &mut outputs)?;
    }
    apply_equalities(&wrapper.equalities, &mut env, &mut outputs)?;
    for (node, required_measure) in &wrapper.required_tokens {
        let place = eval_node(node, &env, &outputs)?;
        let owned = state.tokens.remove(&place).ok_or_else(|| {
            failure(
                "frontend.python.io.token-not-owned",
                format!("wrapper {provider_name} consumes an unowned token"),
            )
        })?;
        match owned {
            TokenKind::Bounded(owned) if owned > *required_measure => {}
            TokenKind::Unbounded => {}
            TokenKind::Bounded(owned) => {
                return Err(failure(
                    "frontend.python.io.token-measure-insufficient",
                    format!(
                        "wrapper {provider_name} requires measure {required_measure}, owned measure is {owned}"
                    ),
                ));
            }
        }
    }
    state.relations.remove(&owned_relation);
    for node in &wrapper.produced_tokens {
        let place = eval_node(node, &env, &outputs)?;
        if state.tokens.insert(place, TokenKind::Unbounded).is_some() {
            return Err(failure(
                "frontend.python.io.token-duplicated",
                format!("wrapper {provider_name} duplicates a produced token"),
            ));
        }
    }
    Ok(outputs)
}

fn unify_node_with_value(
    node: &Node,
    actual: &Value,
    env: &mut BTreeMap<String, Value>,
    outputs: &mut [Value],
) -> Result<(), ContractFailure> {
    let current = eval_node(node, env, outputs)?;
    if current == *actual {
        return Ok(());
    }
    ensure_same_value_sort(&current, actual)?;
    for value in env.values_mut().chain(outputs.iter_mut()) {
        if *value == current {
            *value = actual.clone();
        }
    }
    Ok(())
}

fn same_value_sort(left: &Value, right: &Value) -> bool {
    matches!(
        (left, right),
        (Value::Place(_), Value::Place(_))
            | (
                Value::Int(_) | Value::SymbolicInt(_),
                Value::Int(_) | Value::SymbolicInt(_)
            )
    )
}

fn ensure_same_value_sort(left: &Value, right: &Value) -> Result<(), ContractFailure> {
    if same_value_sort(left, right) {
        Ok(())
    } else {
        Err(failure(
            "frontend.python.io.provider-relation-type-mismatch",
            "provider wrapper relation equates values of different sorts",
        ))
    }
}

fn apply_equalities(
    equalities: &[(Node, Node)],
    env: &mut BTreeMap<String, Value>,
    outputs: &mut [Value],
) -> Result<(), ContractFailure> {
    for (left, right) in equalities {
        let left_value = eval_node(left, env, outputs)?;
        let right_value = eval_node(right, env, outputs)?;
        if left_value == right_value {
            continue;
        }
        ensure_same_value_sort(&left_value, &right_value)?;
        let representative = match (left, right, &left_value, &right_value) {
            (Node::Variable(_), Node::Result(_), _, _) => left_value.clone(),
            (Node::Result(_), Node::Variable(_), _, _) => right_value.clone(),
            (_, _, Value::Int(_), Value::Int(_)) => {
                return Err(failure(
                    "frontend.python.io.provider-equality-inconsistent",
                    "provider postcondition equates distinct integer constants",
                ));
            }
            (_, _, Value::Int(_), _) => left_value.clone(),
            (_, _, _, Value::Int(_)) => right_value.clone(),
            (_, _, Value::SymbolicInt(_), _) => right_value.clone(),
            (_, _, _, Value::SymbolicInt(_)) => left_value.clone(),
            (_, _, Value::Place(_), Value::Place(_)) => right_value.clone(),
        };
        for value in env.values_mut().chain(outputs.iter_mut()) {
            if *value == left_value || *value == right_value {
                *value = representative.clone();
            }
        }
    }
    Ok(())
}

fn bind_assignment(
    target: &ast::Expr,
    outputs: Vec<Value>,
    state: &mut State,
) -> Result<(), ContractFailure> {
    match target {
        ast::Expr::Name(name) if outputs.len() == 1 => {
            state.values.insert(name.id.to_string(), outputs[0].clone());
            Ok(())
        }
        ast::Expr::Tuple(tuple) if tuple.elts.len() == outputs.len() => {
            let names = tuple
                .elts
                .iter()
                .filter_map(|target| match target {
                    ast::Expr::Name(name) => Some(name.id.as_str()),
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            if names.len() != tuple.elts.len() {
                return Err(failure(
                    "frontend.python.io.assignment-target-duplicated",
                    "linear wrapper outputs require distinct name targets",
                ));
            }
            for (target, output) in tuple.elts.iter().zip(outputs) {
                let ast::Expr::Name(name) = target else {
                    return Err(failure(
                        "frontend.python.io.assignment-target-unsupported",
                        "wrapper tuple result requires name targets",
                    ));
                };
                state.values.insert(name.id.to_string(), output);
            }
            Ok(())
        }
        _ => Err(failure(
            "frontend.python.io.assignment-target-unsupported",
            "wrapper result target does not match its return type",
        )),
    }
}

fn verify_assert(call: &ast::ExprCall, state: &State) -> Result<(), ContractFailure> {
    let [argument] = call.args.as_slice() else {
        return Err(failure(
            "frontend.python.io.assert-shape-invalid",
            "Assert requires one expression",
        ));
    };
    let ast::Expr::Compare(compare) = argument else {
        return Err(failure(
            "frontend.python.io.assert-expression-unsupported",
            "minimal IO client Assert supports equality",
        ));
    };
    if compare.ops.as_slice() != [ast::CmpOp::Eq]
        || compare.comparators.len() != 1
        || eval_expression(&compare.left, state)?
            != eval_expression(&compare.comparators[0], state)?
    {
        return Err(failure(
            "frontend.python.io.assertion-failed",
            "IO client assertion is not established by provider contracts",
        ));
    }
    Ok(())
}

fn verify_ensures(
    expression: &ast::Expr,
    returned: Option<&Value>,
    state: &State,
) -> Result<(), ContractFailure> {
    let returned = returned.ok_or_else(|| {
        failure(
            "frontend.python.io.return-value-missing",
            "IO client has no return value",
        )
    })?;
    let mut promised_tokens = BTreeSet::new();
    for conjunct in flatten_and(expression) {
        match conjunct {
            ast::Expr::Call(call) if name(&call.func) == Some("token") && call.args.len() == 1 => {
                let place = eval_expression(&call.args[0], state)?;
                if !state.tokens.contains_key(&place) {
                    return Err(failure(
                        "frontend.python.io.post-token-not-owned",
                        "postcondition token is not owned",
                    ));
                }
                promised_tokens.insert(place);
            }
            ast::Expr::Compare(compare)
                if compare.ops.as_slice() == [ast::CmpOp::Eq] && compare.comparators.len() == 1 =>
            {
                let left = eval_result_expression(&compare.left, returned, state)?;
                let right = eval_result_expression(&compare.comparators[0], returned, state)?;
                if left != right {
                    return Err(failure(
                        "frontend.python.io.postcondition-failed",
                        "IO client return does not establish its postcondition",
                    ));
                }
            }
            _ => {
                return Err(failure(
                    "frontend.python.io.client-postcondition-unsupported",
                    "unsupported IO client postcondition",
                ));
            }
        }
    }
    let owned_tokens = state.tokens.keys().cloned().collect::<BTreeSet<_>>();
    if owned_tokens != promised_tokens || !state.relations.is_empty() {
        return Err(failure(
            "frontend.python.io.linear-resource-leftover",
            format!(
                "IO client leaves tokens {:?} and relations {:?} outside its postcondition",
                owned_tokens
                    .difference(&promised_tokens)
                    .collect::<Vec<_>>(),
                state.relations
            ),
        ));
    }
    Ok(())
}

fn eval_result_expression(
    expression: &ast::Expr,
    returned: &Value,
    state: &State,
) -> Result<Value, ContractFailure> {
    if is_result_call(expression) {
        return Ok(returned.clone());
    }
    eval_expression(expression, state)
}

fn eval_expression(expression: &ast::Expr, state: &State) -> Result<Value, ContractFailure> {
    match expression {
        ast::Expr::Name(name) => state.values.get(name.id.as_str()).cloned().ok_or_else(|| {
            failure(
                "frontend.python.io.value-unbound",
                format!("unbound IO value {}", name.id),
            )
        }),
        ast::Expr::Constant(constant) => {
            match &constant.value {
                ast::Constant::Int(value) => value
                    .to_string()
                    .parse::<i64>()
                    .map(Value::Int)
                    .map_err(|_| {
                        failure(
                            "frontend.python.io.integer-out-of-range",
                            "integer literal does not fit i64",
                        )
                    }),
                _ => Err(failure(
                    "frontend.python.io.value-expression-unsupported",
                    "unsupported IO literal",
                )),
            }
        }
        _ => Err(failure(
            "frontend.python.io.value-expression-unsupported",
            "unsupported IO value expression",
        )),
    }
}

fn eval_node(
    node: &Node,
    env: &BTreeMap<String, Value>,
    outputs: &[Value],
) -> Result<Value, ContractFailure> {
    match node {
        Node::Variable(name) => env.get(name).cloned().ok_or_else(|| {
            failure(
                "frontend.python.io.value-unbound",
                format!("unbound IO provider value {name}"),
            )
        }),
        Node::Result(index) => outputs.get(*index).cloned().ok_or_else(|| {
            failure(
                "frontend.python.io.result-index-invalid",
                "Result projection is outside wrapper return",
            )
        }),
        Node::Integer(value) => Ok(Value::Int(*value)),
    }
}

fn value_has_sort(value: &Value, expected: &IoSort) -> bool {
    matches!(
        (value, expected),
        (Value::Place(_), IoSort::Place) | (Value::Int(_) | Value::SymbolicInt(_), IoSort::Int)
    )
}

fn ensure_sort(value: &Value, expected: &IoSort) -> Result<(), ContractFailure> {
    if value_has_sort(value, expected) {
        Ok(())
    } else {
        Err(failure(
            "frontend.python.io.call-type-mismatch",
            "IO wrapper argument has the wrong type",
        ))
    }
}

fn make_obligation(id: String, source: &str, path: &str, offset: u32) -> Obligation {
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
        conclusion: Term::Bool { value: true },
        path: path.to_owned(),
        byte_offset: offset,
        line,
        column,
    }
}

#[cfg(test)]
mod tests {
    use super::{
        IoSort, Value, ensure_same_value_sort, ensure_sort, same_value_sort, value_has_sort,
        verify_pinned_io_module,
    };

    const CONTRACTS: &str =
        include_str!("../.upstream/nagini/src/nagini_contracts/io_contracts.py");
    const BUILTINS: &str = include_str!("../.upstream/nagini/src/nagini_contracts/io_builtins.py");

    const IMPORTS: &str = "from nagini_contracts.contracts import Assert, Ensures, Requires, Result\nfrom nagini_contracts.io_contracts import *\nfrom nagini_contracts.io_builtins import no_op_io, NoOp, split_io, Split, join_io, Join, set_var_io, SetVar\n";

    fn verify(source: &str) -> Result<(), &'static str> {
        verify_pinned_io_module(source, "client.py", CONTRACTS, BUILTINS, &[])
            .map(|result| assert!(result.is_some()))
            .map_err(|failure| failure.code)
    }

    #[test]
    fn io_sort_predicates_and_diagnostics_cover_every_value_class() {
        let place = Value::Place("place".to_owned());
        let integer = Value::Int(7);
        let symbolic_integer = Value::SymbolicInt("n".to_owned());

        assert!(value_has_sort(&place, &IoSort::Place));
        assert!(!value_has_sort(&place, &IoSort::Int));
        assert!(value_has_sort(&integer, &IoSort::Int));
        assert!(value_has_sort(&symbolic_integer, &IoSort::Int));
        assert!(!value_has_sort(&integer, &IoSort::Place));
        assert!(!value_has_sort(&symbolic_integer, &IoSort::Place));

        assert!(same_value_sort(&place, &place));
        assert!(same_value_sort(&integer, &symbolic_integer));
        assert!(same_value_sort(&symbolic_integer, &integer));
        assert!(!same_value_sort(&place, &integer));
        assert!(!same_value_sort(&symbolic_integer, &place));

        let call_error = ensure_sort(&place, &IoSort::Int).unwrap_err();
        assert_eq!(call_error.code, "frontend.python.io.call-type-mismatch");
        assert_eq!(call_error.message, "IO wrapper argument has the wrong type");

        let relation_error = ensure_same_value_sort(&place, &integer).unwrap_err();
        assert_eq!(
            relation_error.code,
            "frontend.python.io.provider-relation-type-mismatch"
        );
        assert_eq!(
            relation_error.message,
            "provider wrapper relation equates values of different sorts"
        );
    }

    #[test]
    fn open_and_wrappers_form_one_linear_transition_chain() {
        let source = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists2(Place, Place)(lambda left, right: split_io(start, left, right) and join_io(left, right, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    left, right = Split(start)\n    end = Join(left, right)\n    return end\n"
        );
        verify(&source).unwrap();
    }

    #[test]
    fn consumed_tokens_cannot_be_reused() {
        let source = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists3(Place, Place, Place)(lambda left, first, second: split_io(start, left, end) and no_op_io(left, first) and no_op_io(left, second))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    left, end = Split(start)\n    first = NoOp(left)\n    second = NoOp(left)\n    return end\n"
        );
        assert_eq!(verify(&source), Err("frontend.python.io.token-not-owned"));
    }

    #[test]
    fn operation_relations_are_opened_once() {
        let source = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(Place)(lambda middle: no_op_io(start, middle) and no_op_io(middle, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    Open(protocol(start))\n    middle = NoOp(start)\n    end = NoOp(middle)\n    return end\n"
        );
        assert_eq!(
            verify(&source),
            Err("frontend.python.io.open-relation-not-owned")
        );
    }

    #[test]
    fn provider_equalities_are_used_to_prove_results() {
        let source = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(int)(lambda value: set_var_io(start, 1, value, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    value, end = SetVar(start, 1)\n    Assert(value == 2)\n    return end\n"
        );
        assert_eq!(verify(&source), Err("frontend.python.io.assertion-failed"));
    }

    #[test]
    fn shadowing_and_control_flow_are_not_treated_as_io_semantics() {
        let shadowed = format!(
            "{IMPORTS}\nSetVar = object\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(int)(lambda value: set_var_io(start, 1, value, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    value, end = SetVar(start, 1)\n    return end\n"
        );
        assert!(verify(&shadowed).is_err());

        let branching = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(Place)(lambda middle: no_op_io(start, middle) and no_op_io(middle, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    if True:\n        middle = NoOp(start)\n    end = NoOp(middle)\n    return end\n"
        );
        assert_eq!(
            verify(&branching),
            Err("frontend.python.io.control-flow-unsupported")
        );
    }

    #[test]
    fn provider_contract_mutation_invalidates_the_client_proof() {
        let mutated = BUILTINS.replacen("value == result", "value == value", 1);
        assert_ne!(
            mutated, BUILTINS,
            "test mutation must alter the provider contract"
        );
        let source = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(int)(lambda value: set_var_io(start, 1, value, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    value, end = SetVar(start, 1)\n    Assert(value == 1)\n    return end\n"
        );
        let failure = verify_pinned_io_module(&source, "client.py", CONTRACTS, &mutated, &[])
            .expect_err("mutated provider must not establish the original result relation");
        assert_eq!(failure.code, "frontend.python.io.assertion-failed");
    }

    #[test]
    fn missing_token_and_wrong_argument_type_fail_before_transition() {
        let missing_token = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(Place)(lambda middle: no_op_io(start, middle) and no_op_io(middle, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    middle = NoOp(start)\n    end = NoOp(middle)\n    return end\n"
        );
        assert_eq!(
            verify(&missing_token),
            Err("frontend.python.io.token-not-owned")
        );

        let wrong_type = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(int)(lambda value: set_var_io(start, 1, value, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    value, end = SetVar(start, start)\n    return end\n"
        );
        assert_eq!(
            verify(&wrong_type),
            Err("frontend.python.io.call-type-mismatch")
        );
    }

    #[test]
    fn split_outputs_cannot_be_suppressed_or_aliased() {
        let suppressed = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(Place)(lambda left: split_io(start, left, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    left = Split(start)\n    return end\n"
        );
        assert_eq!(
            verify(&suppressed),
            Err("frontend.python.io.assignment-target-unsupported")
        );

        let aliased = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(Place)(lambda left: split_io(start, left, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    same, same = Split(start)\n    return end\n"
        );
        assert_eq!(
            verify(&aliased),
            Err("frontend.python.io.assignment-target-duplicated")
        );
    }

    #[test]
    fn all_linear_resources_must_reach_the_declared_postcondition() {
        let source = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(Place)(lambda left: split_io(start, left, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    left, end = Split(start)\n    return end\n"
        );
        assert_eq!(
            verify(&source),
            Err("frontend.python.io.linear-resource-leftover")
        );
    }

    #[test]
    fn provider_result_arity_and_type_are_source_bound() {
        let wrong_result_type = BUILTINS.replacen(
            "def SetVar(t_pre: Place, value: int) -> Tuple[int, Place]:",
            "def SetVar(t_pre: Place, value: int) -> Tuple[Place, Place]:",
            1,
        );
        assert_ne!(wrong_result_type, BUILTINS);
        let source = format!(
            "{IMPORTS}\n@IOOperation\ndef protocol(start: Place, end: Place = Result()) -> bool:\n    Terminates(True)\n    return IOExists1(int)(lambda value: set_var_io(start, 1, value, end))\ndef run(start: Place) -> Place:\n    IOExists1(Place)(lambda end: (Requires(token(start, 2) and protocol(start, end)), Ensures(token(end) and end == Result())))\n    Open(protocol(start))\n    value, end = SetVar(start, 1)\n    Assert(value == 1)\n    return end\n"
        );
        let failure =
            verify_pinned_io_module(&source, "client.py", CONTRACTS, &wrong_result_type, &[])
                .expect_err("wrong provider result type must refuse the client");
        assert!(matches!(
            failure.code,
            "frontend.python.io.provider-relation-type-mismatch"
                | "frontend.python.io.call-type-mismatch"
                | "frontend.python.io.assertion-failed"
        ));

        let missing_interface = CONTRACTS.replacen("class Place:", "class MissingPlace:", 1);
        let failure =
            verify_pinned_io_module(&source, "client.py", &missing_interface, BUILTINS, &[])
                .expect_err("provider interface mutation must refuse verification");
        assert_eq!(
            failure.code,
            "frontend.python.io.provider-interface-incomplete"
        );
    }
}
