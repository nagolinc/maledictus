//! Definition-flow validation for source-bound IO existential variables.
//!
//! IO existential lambda parameters are declarations, not initialized Python locals. They become
//! available only when a direct result equality or an IO-operation output position defines them.
//! This pass keeps that state explicit and never treats a conditional occurrence as a definition.

use std::collections::BTreeMap;

use rustpython_ast::Visitor;
use rustpython_parser::ast;

use super::{
    Bindings, EXISTENTIAL_DEFINITION_TYPE_MISMATCH, EXISTENTIAL_USE_UNDEFINED,
    IoWellformednessFailure, OPERATION_RESULT_NOT_EXISTENTIAL, OPERATION_RESULT_NOT_VARIABLE,
    OPERATION_UNDEFINED_EXISTENTIAL, Operation, annotation_key, fail,
};

#[derive(Clone, Debug)]
struct Existential {
    sort: Option<String>,
    availability: DefinitionAvailability,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DefinitionAvailability {
    Undefined,
    Defined,
    Deferred,
}

type DeclaredExistentials = Vec<(String, Option<String>)>;
type ParsedInvocation<'a> = (DeclaredExistentials, &'a ast::Expr);

pub(super) fn validate_function(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    if bindings.operations.contains_key(function.name.as_str()) {
        validate_operation_body(function, bindings, source)
    } else {
        validate_client_contracts(function, bindings, source)
    }
}

fn validate_client_contracts(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let result_sort = function
        .returns
        .as_deref()
        .and_then(|annotation| annotation_key(annotation, &bindings.canonical));
    for statement in &function.body {
        let ast::Stmt::Expr(expression) = statement else {
            continue;
        };
        let Some((declared, body)) = io_exists_invocation(&expression.value, bindings) else {
            continue;
        };
        let mut existentials = declared_existentials(declared);
        validate_client_contract_body(
            body,
            &mut existentials,
            result_sort.as_deref(),
            bindings,
            source,
        )?;
    }
    Ok(())
}

fn validate_client_contract_body(
    expression: &ast::Expr,
    existentials: &mut BTreeMap<String, Existential>,
    result_sort: Option<&str>,
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let items = match expression {
        ast::Expr::Tuple(tuple) => tuple.elts.as_slice(),
        _ => std::slice::from_ref(expression),
    };
    for item in items {
        let ast::Expr::Call(contract) = item else {
            continue;
        };
        let Some(contract_name) = canonical_call_name(contract, bindings) else {
            continue;
        };
        if !matches!(contract_name, "Requires" | "Ensures") {
            continue;
        }
        for argument in &contract.args {
            validate_client_expression(argument, existentials, result_sort, bindings, source)?;
        }
        for keyword in &contract.keywords {
            validate_client_expression(
                &keyword.value,
                existentials,
                result_sort,
                bindings,
                source,
            )?;
        }
    }
    Ok(())
}

fn validate_client_expression(
    expression: &ast::Expr,
    existentials: &mut BTreeMap<String, Existential>,
    result_sort: Option<&str>,
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    if let ast::Expr::BoolOp(boolean) = expression
        && boolean.op == ast::BoolOp::And
    {
        for value in &boolean.values {
            validate_client_expression(value, existentials, result_sort, bindings, source)?;
        }
        return Ok(());
    }

    if let Some((name, defining_expression)) = direct_definition(expression, existentials) {
        reject_undefined_use(defining_expression, existentials, source, false)?;
        let actual_sort = expression_sort(defining_expression, result_sort, bindings);
        define(
            name,
            actual_sort.as_deref(),
            expression,
            existentials,
            source,
        )?;
        return Ok(());
    }

    if let ast::Expr::Call(call) = expression
        && let Some(operation) = direct_operation(call, bindings)
    {
        validate_client_operation_call(call, operation, existentials, source)?;
        return Ok(());
    }
    if let ast::Expr::Call(call) = expression
        && is_deferred_external_operation(call, bindings)
    {
        // The heap IO backend validates this call against the hash-bound io_builtins provider
        // source, including its exact input/output positions and sorts. This source-only pass
        // must not invent that external signature or relabel its outputs as undefined uses.
        defer_referenced_existentials(call, existentials);
        return Ok(());
    }

    reject_undefined_use(expression, existentials, source, false)
}

fn validate_client_operation_call(
    call: &ast::ExprCall,
    operation: &Operation,
    existentials: &mut BTreeMap<String, Existential>,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let output_start = operation.inputs.len() + 1;
    for argument in call.args.iter().take(output_start) {
        reject_undefined_use(argument, existentials, source, false)?;
    }
    for (argument, output) in call.args.iter().skip(output_start).zip(&operation.outputs) {
        let ast::Expr::Name(name) = argument else {
            reject_undefined_use(argument, existentials, source, false)?;
            continue;
        };
        if existentials.contains_key(name.id.as_str()) {
            define(
                name.id.as_str(),
                output.annotation.as_deref(),
                argument,
                existentials,
                source,
            )?;
        }
    }
    for argument in call
        .args
        .iter()
        .skip(output_start + operation.outputs.len())
    {
        reject_undefined_use(argument, existentials, source, false)?;
    }
    Ok(())
}

fn validate_operation_body(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let result_parameters = bindings
        .operations
        .get(function.name.as_str())
        .expect("operation body validation requires a collected source operation")
        .outputs
        .iter()
        .map(|output| (output.name.as_str(), output.annotation.as_deref()))
        .collect::<BTreeMap<_, _>>();
    for statement in &function.body {
        let ast::Stmt::Return(returned) = statement else {
            continue;
        };
        let Some(expression) = returned.value.as_deref() else {
            continue;
        };
        if let Some((declared, body)) = io_exists_invocation(expression, bindings) {
            let mut existentials = declared_existentials(declared);
            validate_operation_expression(
                body,
                &mut existentials,
                &result_parameters,
                bindings,
                source,
            )?;
        } else {
            let mut existentials = BTreeMap::new();
            validate_operation_expression(
                expression,
                &mut existentials,
                &result_parameters,
                bindings,
                source,
            )?;
        }
    }
    Ok(())
}

fn validate_operation_expression(
    expression: &ast::Expr,
    existentials: &mut BTreeMap<String, Existential>,
    result_parameters: &BTreeMap<&str, Option<&str>>,
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    if let ast::Expr::BoolOp(boolean) = expression
        && boolean.op == ast::BoolOp::And
    {
        for value in &boolean.values {
            validate_operation_expression(
                value,
                existentials,
                result_parameters,
                bindings,
                source,
            )?;
        }
        return Ok(());
    }

    if let ast::Expr::IfExp(conditional) = expression {
        reject_undefined_use(&conditional.test, existentials, source, true)?;
        let mut then_existentials = existentials.clone();
        let mut else_existentials = existentials.clone();
        validate_operation_expression(
            &conditional.body,
            &mut then_existentials,
            result_parameters,
            bindings,
            source,
        )?;
        validate_operation_expression(
            &conditional.orelse,
            &mut else_existentials,
            result_parameters,
            bindings,
            source,
        )?;
        for (name, existential) in existentials {
            let then_availability = then_existentials
                .get(name)
                .map(|branch| branch.availability)
                .expect("branches preserve existential declarations");
            let else_availability = else_existentials
                .get(name)
                .map(|branch| branch.availability)
                .expect("branches preserve existential declarations");
            existential.availability =
                join_branch_availability(then_availability, else_availability);
        }
        return Ok(());
    }

    if let Some((name, ast::Expr::Name(result))) = direct_definition(expression, existentials)
        && let Some(actual_sort) = result_parameters.get(result.id.as_str())
    {
        define(name, *actual_sort, expression, existentials, source)?;
        return Ok(());
    }

    if let ast::Expr::Call(call) = expression
        && let Some(operation) = direct_operation(call, bindings)
    {
        validate_operation_relation(call, operation, existentials, result_parameters, source)?;
        return Ok(());
    }
    if let ast::Expr::Call(call) = expression
        && is_deferred_external_operation(call, bindings)
    {
        defer_referenced_existentials(call, existentials);
        return Ok(());
    }

    reject_undefined_use(expression, existentials, source, true)
}

fn validate_operation_relation(
    call: &ast::ExprCall,
    operation: &Operation,
    existentials: &mut BTreeMap<String, Existential>,
    result_parameters: &BTreeMap<&str, Option<&str>>,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let output_start = operation.inputs.len() + 1;
    for argument in call.args.iter().take(output_start) {
        reject_undefined_use(argument, existentials, source, true)?;
    }
    for (argument, output) in call.args.iter().skip(output_start).zip(&operation.outputs) {
        let ast::Expr::Name(name) = argument else {
            return fail(
                argument,
                source,
                OPERATION_RESULT_NOT_VARIABLE,
                "an IO operation result position requires a direct existential variable",
            );
        };
        if let Some(existential) = existentials.get(name.id.as_str()) {
            if let (Some(declared), Some(actual)) =
                (existential.sort.as_deref(), output.annotation.as_deref())
                && declared != actual
            {
                return fail(
                    argument,
                    source,
                    EXISTENTIAL_DEFINITION_TYPE_MISMATCH,
                    format!(
                        "IO existential {:?} has type {declared:?}, but the result position has type {actual:?}",
                        name.id.as_str()
                    ),
                );
            }
            existentials
                .get_mut(name.id.as_str())
                .expect("existential presence checked above")
                .availability = DefinitionAvailability::Defined;
            continue;
        }
        if let Some(result_sort) = result_parameters.get(name.id.as_str()) {
            if let (Some(declared), Some(actual)) = (*result_sort, output.annotation.as_deref())
                && declared != actual
            {
                return fail(
                    argument,
                    source,
                    EXISTENTIAL_DEFINITION_TYPE_MISMATCH,
                    format!(
                        "IO operation result {:?} has type {declared:?}, but the nested result position has type {actual:?}",
                        name.id.as_str()
                    ),
                );
            }
            continue;
        }
        return fail(
            argument,
            source,
            OPERATION_RESULT_NOT_EXISTENTIAL,
            format!(
                "IO operation result variable {:?} is neither declared by IOExists nor an output of the enclosing operation",
                name.id.as_str()
            ),
        );
    }
    Ok(())
}

fn direct_definition<'a>(
    expression: &'a ast::Expr,
    existentials: &BTreeMap<String, Existential>,
) -> Option<(&'a str, &'a ast::Expr)> {
    let ast::Expr::Compare(compare) = expression else {
        return None;
    };
    if compare.ops.as_slice() != [ast::CmpOp::Eq] || compare.comparators.len() != 1 {
        return None;
    }
    let ast::Expr::Name(name) = compare.left.as_ref() else {
        return None;
    };
    existentials
        .get(name.id.as_str())
        .is_some_and(|existential| existential.availability != DefinitionAvailability::Defined)
        .then_some((name.id.as_str(), &compare.comparators[0]))
}

fn define(
    name: &str,
    actual_sort: Option<&str>,
    ranged: &ast::Expr,
    existentials: &mut BTreeMap<String, Existential>,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let existential = existentials
        .get_mut(name)
        .expect("direct definitions are restricted to declared existentials");
    if let (Some(declared), Some(actual)) = (existential.sort.as_deref(), actual_sort)
        && declared != actual
    {
        return fail(
            ranged,
            source,
            EXISTENTIAL_DEFINITION_TYPE_MISMATCH,
            format!(
                "IO existential {name:?} has type {declared:?}, but its defining expression has type {actual:?}"
            ),
        );
    }
    existential.availability = DefinitionAvailability::Defined;
    Ok(())
}

fn expression_sort(
    expression: &ast::Expr,
    result_sort: Option<&str>,
    bindings: &Bindings,
) -> Option<String> {
    match expression {
        ast::Expr::Call(call)
            if canonical_call_name(call, bindings) == Some("Result")
                && call.args.is_empty()
                && call.keywords.is_empty() =>
        {
            result_sort.map(str::to_owned)
        }
        ast::Expr::Constant(constant) => match constant.value {
            ast::Constant::Bool(_) => Some("bool".to_owned()),
            ast::Constant::Int(_) => Some("int".to_owned()),
            ast::Constant::Str(_) => Some("str".to_owned()),
            _ => None,
        },
        _ => None,
    }
}

fn io_exists_invocation<'a>(
    expression: &'a ast::Expr,
    bindings: &Bindings,
) -> Option<ParsedInvocation<'a>> {
    let ast::Expr::Call(invocation) = expression else {
        return None;
    };
    let ast::Expr::Call(constructor) = invocation.func.as_ref() else {
        return None;
    };
    let canonical = canonical_expression_name(&constructor.func, bindings)?;
    if !canonical.starts_with("IOExists")
        || !constructor.keywords.is_empty()
        || !invocation.keywords.is_empty()
    {
        return None;
    }
    let [ast::Expr::Lambda(lambda)] = invocation.args.as_slice() else {
        return None;
    };
    let parameters = lambda
        .args
        .posonlyargs
        .iter()
        .chain(&lambda.args.args)
        .collect::<Vec<_>>();
    if parameters.len() != constructor.args.len() {
        return None;
    }
    let declared = parameters
        .into_iter()
        .zip(&constructor.args)
        .map(|(parameter, annotation)| {
            (
                parameter.def.arg.to_string(),
                annotation_key(annotation, &bindings.canonical),
            )
        })
        .collect();
    Some((declared, &lambda.body))
}

fn declared_existentials(declared: DeclaredExistentials) -> BTreeMap<String, Existential> {
    declared
        .into_iter()
        .map(|(name, sort)| {
            (
                name,
                Existential {
                    sort,
                    availability: DefinitionAvailability::Undefined,
                },
            )
        })
        .collect()
}

fn canonical_call_name<'a>(call: &ast::ExprCall, bindings: &'a Bindings) -> Option<&'a str> {
    canonical_expression_name(&call.func, bindings)
}

fn canonical_expression_name<'a>(
    expression: &ast::Expr,
    bindings: &'a Bindings,
) -> Option<&'a str> {
    let ast::Expr::Name(name) = expression else {
        return None;
    };
    bindings.canonical.get(name.id.as_str()).map(String::as_str)
}

fn direct_operation<'a>(call: &ast::ExprCall, bindings: &'a Bindings) -> Option<&'a Operation> {
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return None;
    };
    bindings.operations.get(name.id.as_str())
}

fn is_deferred_external_operation(call: &ast::ExprCall, bindings: &Bindings) -> bool {
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return false;
    };
    bindings.external_operations.contains(name.id.as_str())
        || bindings.deferred_imports.contains(name.id.as_str())
        || (bindings.star_io_builtins_imported
            && !bindings.locally_shadowed.contains(name.id.as_str())
            && !bindings.canonical.contains_key(name.id.as_str())
            && !bindings.operations.contains_key(name.id.as_str()))
}

fn defer_referenced_existentials(
    call: &ast::ExprCall,
    existentials: &mut BTreeMap<String, Existential>,
) {
    let mut collector = ReferencedNameCollector::default();
    collector.visit_expr(ast::Expr::Call(call.clone()));
    for name in collector.names {
        if let Some(existential) = existentials.get_mut(name.as_str())
            && existential.availability == DefinitionAvailability::Undefined
        {
            existential.availability = DefinitionAvailability::Deferred;
        }
    }
}

fn join_branch_availability(
    then_availability: DefinitionAvailability,
    else_availability: DefinitionAvailability,
) -> DefinitionAvailability {
    match (then_availability, else_availability) {
        (DefinitionAvailability::Defined, DefinitionAvailability::Defined) => {
            DefinitionAvailability::Defined
        }
        (DefinitionAvailability::Undefined, _) | (_, DefinitionAvailability::Undefined) => {
            DefinitionAvailability::Undefined
        }
        _ => DefinitionAvailability::Deferred,
    }
}

#[derive(Default)]
struct ReferencedNameCollector {
    names: std::collections::BTreeSet<String>,
}

impl Visitor for ReferencedNameCollector {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        self.names.insert(node.id.to_string());
    }
}

fn reject_undefined_use(
    expression: &ast::Expr,
    existentials: &BTreeMap<String, Existential>,
    source: &str,
    operation_body: bool,
) -> Result<(), IoWellformednessFailure> {
    let mut collector = UndefinedUseCollector {
        existentials,
        first: None,
    };
    collector.visit_expr(expression.clone());
    let Some(name) = collector.first else {
        return Ok(());
    };
    let code = if operation_body {
        OPERATION_UNDEFINED_EXISTENTIAL
    } else {
        EXISTENTIAL_USE_UNDEFINED
    };
    fail(
        &name,
        source,
        code,
        format!(
            "IO existential {:?} is used before a defining result position",
            name.id.as_str()
        ),
    )
}

struct UndefinedUseCollector<'a> {
    existentials: &'a BTreeMap<String, Existential>,
    first: Option<ast::ExprName>,
}

impl Visitor for UndefinedUseCollector<'_> {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if self.first.is_none()
            && self
                .existentials
                .get(node.id.as_str())
                .is_some_and(|existential| {
                    existential.availability == DefinitionAvailability::Undefined
                })
        {
            self.first = Some(node);
        }
    }
}
