//! Closed totality checking for Dagcert's source-owned Python operation boundary.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_parser::ast::Ranged;
use rustpython_parser::{Parse, ast};

#[derive(Clone, Debug, Eq, PartialEq)]
enum ValueType {
    Int,
    Float,
    Bool,
    Str,
    Record(String),
    Callable(CallableSignature),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CallableSignature {
    parameters: Vec<ValueType>,
    return_type: Box<ValueType>,
}

mod callables;

pub use callables::{
    CallableContract, CallablePrimitiveType, ResolvedCallableBinding, SourceCallableProvider,
    analyze_source_callable,
};

#[derive(Clone, Debug)]
struct RecordShape {
    fields: Vec<(String, ValueType)>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct StatementEffects {
    normal_path_returns: bool,
    raised_exceptions: BTreeSet<String>,
}

#[derive(Clone, Debug)]
struct ImportedMarkers {
    operations: BTreeSet<String>,
    dataclasses: BTreeSet<String>,
    unions: BTreeSet<String>,
    callables: BTreeSet<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OperationVerification {
    pub operations: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OperationFailure {
    pub code: &'static str,
    pub message: String,
    pub byte_offset: Option<u32>,
}

pub fn verify_operation_module(
    source: &str,
    path: &str,
    requested_symbols: &[String],
) -> Result<OperationVerification, OperationFailure> {
    verify_operation_module_with_bindings(source, path, requested_symbols, &[])
}

pub fn verify_operation_module_with_bindings(
    source: &str,
    path: &str,
    requested_symbols: &[String],
    callable_bindings: &[ResolvedCallableBinding],
) -> Result<OperationVerification, OperationFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| OperationFailure {
        code: "frontend.python.dagcert.parse-error",
        message: error.to_string(),
        byte_offset: None,
    })?;
    let markers = imported_markers(&suite)?;
    let protected_markers = markers
        .operations
        .iter()
        .chain(&markers.dataclasses)
        .chain(&markers.unions)
        .chain(&markers.callables)
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if let Some(shadowed) = suite.iter().find_map(|statement| {
        declaration_name(statement).filter(|name| protected_markers.contains(name))
    }) {
        return failure(
            "frontend.python.dagcert.imported-marker-shadowed",
            format!("source declaration shadows imported typing or Dagcert marker {shadowed:?}"),
        );
    }
    if let Some(shadowed) = suite.iter().find_map(|statement| {
        declaration_name(statement).filter(|name| is_modeled_builtin_exception_name(name))
    }) {
        return failure(
            "frontend.python.dagcert.exception-class-shadowed",
            format!("source declaration shadows modeled builtin exception {shadowed:?}"),
        );
    }
    let mut class_names = BTreeSet::new();
    for statement in &suite {
        if let ast::Stmt::ClassDef(class) = statement
            && !class_names.insert(class.name.to_string())
        {
            return failure(
                "frontend.python.dagcert.class-duplicate",
                format!("record class {:?} is declared more than once", class.name),
            );
        }
    }
    let mut records = BTreeMap::new();
    let mut functions = Vec::new();
    let same_file_provider_symbols = callable_bindings
        .iter()
        .filter_map(|binding| binding.source_provider.as_ref())
        .filter(|provider| provider.path == path)
        .map(|provider| provider.symbol.as_str())
        .collect::<BTreeSet<_>>();
    for (index, statement) in suite.iter().enumerate() {
        match statement {
            _ if index == 0 && is_docstring(statement) => {}
            ast::Stmt::ImportFrom(import) if allowed_import(import) => {}
            ast::Stmt::ClassDef(class) => {
                let shape = parse_record(
                    class,
                    &markers.dataclasses,
                    &markers.callables,
                    &class_names,
                )?;
                records.insert(class.name.to_string(), shape);
            }
            ast::Stmt::FunctionDef(function)
                if function.decorator_list.len() == 1
                    && matches!(&function.decorator_list[0], ast::Expr::Name(name) if markers.operations.contains(name.id.as_str())) =>
            {
                functions.push(function)
            }
            ast::Stmt::FunctionDef(function)
                if same_file_provider_symbols.contains(function.name.as_str()) => {}
            _ => {
                return failure(
                    "frontend.python.dagcert.module-statement-unsupported",
                    format!(
                        "Dagcert operation module contains unsupported statement {statement:?}"
                    ),
                );
            }
        }
    }
    if records.is_empty() || functions.is_empty() {
        return failure(
            "frontend.python.dagcert.empty-module",
            "Dagcert operation fragment requires frozen record types and at least one operation",
        );
    }
    let mut operations = Vec::new();
    for function in functions {
        verify_operation(
            function,
            &markers.operations,
            &markers.unions,
            &markers.callables,
            &records,
            callable_bindings,
        )?;
        operations.push(function.name.to_string());
    }
    for requested in requested_symbols {
        if !operations.iter().any(|operation| operation == requested)
            && !same_file_provider_symbols.contains(requested.as_str())
        {
            return failure(
                "frontend.python.symbol.missing",
                format!(
                    "requested symbol {requested:?} is not a verified Dagcert operation or bound source callback"
                ),
            );
        }
    }
    for binding in callable_bindings {
        if !operations
            .iter()
            .any(|operation| operation == &binding.operation)
        {
            return failure(
                "frontend.python.dagcert.callable-binding-operation-unknown",
                format!(
                    "callable binding for {:?}.{} names unknown operation {:?}",
                    binding.input_record, binding.field, binding.operation
                ),
            );
        }
    }
    Ok(OperationVerification { operations })
}

fn imported_markers(suite: &[ast::Stmt]) -> Result<ImportedMarkers, OperationFailure> {
    let mut operations = BTreeSet::new();
    let mut dataclasses = BTreeSet::new();
    let mut unions = BTreeSet::new();
    let mut callables = BTreeSet::new();
    for statement in suite {
        let ast::Stmt::ImportFrom(import) = statement else {
            continue;
        };
        let Some(module) = import.module.as_ref().map(|module| module.as_str()) else {
            continue;
        };
        if module == "dagcert" || module == "dagcert.runtime" {
            for alias in &import.names {
                if alias.name.as_str() == "operation" {
                    operations.insert(
                        alias
                            .asname
                            .as_ref()
                            .map_or(alias.name.as_str(), |name| name.as_str())
                            .to_owned(),
                    );
                }
            }
        } else if module == "dataclasses" {
            for alias in &import.names {
                if alias.name.as_str() == "dataclass" {
                    dataclasses.insert(
                        alias
                            .asname
                            .as_ref()
                            .map_or(alias.name.as_str(), |name| name.as_str())
                            .to_owned(),
                    );
                }
            }
        } else if module == "typing" {
            for alias in &import.names {
                if alias.name.as_str() == "Union" {
                    unions.insert(
                        alias
                            .asname
                            .as_ref()
                            .map_or(alias.name.as_str(), |name| name.as_str())
                            .to_owned(),
                    );
                } else if alias.name.as_str() == "Callable" {
                    callables.insert(
                        alias
                            .asname
                            .as_ref()
                            .map_or(alias.name.as_str(), |name| name.as_str())
                            .to_owned(),
                    );
                }
            }
        }
    }
    if operations.is_empty() || dataclasses.is_empty() {
        return failure(
            "frontend.python.dagcert.marker-import-missing",
            "operation and dataclass decorators must be imported from dagcert(.runtime) and dataclasses",
        );
    }
    Ok(ImportedMarkers {
        operations,
        dataclasses,
        unions,
        callables,
    })
}

fn allowed_import(import: &ast::StmtImportFrom) -> bool {
    if import.level.is_some_and(|level| level != 0_u32) {
        return false;
    }
    let Some(module) = import.module.as_ref().map(|module| module.as_str()) else {
        return false;
    };
    if module == "__future__" {
        return import
            .names
            .iter()
            .all(|alias| alias.name.as_str() == "annotations" && alias.asname.is_none());
    }
    if module == "typing" {
        return import
            .names
            .iter()
            .all(|alias| matches!(alias.name.as_str(), "Union" | "Callable"));
    }
    let allowed = match module {
        "dataclasses" => "dataclass",
        "dagcert" | "dagcert.runtime" => "operation",
        _ => return false,
    };
    import
        .names
        .iter()
        .all(|alias| alias.name.as_str() == allowed)
}

fn parse_record(
    class: &ast::StmtClassDef,
    dataclass_names: &BTreeSet<String>,
    callable_names: &BTreeSet<String>,
    class_names: &BTreeSet<String>,
) -> Result<RecordShape, OperationFailure> {
    if !class.bases.is_empty()
        || !class.keywords.is_empty()
        || !class.type_params.is_empty()
        || class.decorator_list.len() != 1
        || !frozen_dataclass(&class.decorator_list[0], dataclass_names)
    {
        return failure(
            "frontend.python.dagcert.record-shape-unsupported",
            format!(
                "record {:?} must be one non-generic @dataclass(frozen=True) without bases",
                class.name
            ),
        );
    }
    let mut fields = Vec::new();
    let mut names = BTreeSet::new();
    for (index, statement) in class.body.iter().enumerate() {
        match statement {
            _ if index == 0 && is_docstring(statement) => {}
            ast::Stmt::AnnAssign(assignment) => {
                let ast::Expr::Name(name) = assignment.target.as_ref() else {
                    return failure(
                        "frontend.python.dagcert.record-field-unsupported",
                        "record fields require simple annotated names",
                    );
                };
                if assignment.value.is_some() || !names.insert(name.id.to_string()) {
                    return failure(
                        "frontend.python.dagcert.record-field-unsupported",
                        format!("record field {:?} has a default or is duplicated", name.id),
                    );
                }
                fields.push((
                    name.id.to_string(),
                    annotation_type(&assignment.annotation, class_names, callable_names)?,
                ));
            }
            ast::Stmt::Pass(_) => {}
            _ => {
                return failure(
                    "frontend.python.dagcert.record-body-unsupported",
                    format!(
                        "record {:?} contains executable member {statement:?}",
                        class.name
                    ),
                );
            }
        }
    }
    Ok(RecordShape { fields })
}

fn frozen_dataclass(expression: &ast::Expr, names: &BTreeSet<String>) -> bool {
    let ast::Expr::Call(call) = expression else {
        return false;
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return false;
    };
    if !names.contains(name.id.as_str()) || !call.args.is_empty() {
        return false;
    }
    let mut frozen = false;
    for keyword in &call.keywords {
        let Some(argument) = keyword.arg.as_ref().map(|argument| argument.as_str()) else {
            return false;
        };
        let ast::Expr::Constant(value) = &keyword.value else {
            return false;
        };
        let ast::Constant::Bool(enabled) = value.value else {
            return false;
        };
        match argument {
            "frozen" if enabled => frozen = true,
            "slots" if enabled => {}
            _ => return false,
        }
    }
    frozen
}

fn annotation_type(
    annotation: &ast::Expr,
    class_names: &BTreeSet<String>,
    callable_names: &BTreeSet<String>,
) -> Result<ValueType, OperationFailure> {
    if let ast::Expr::Subscript(subscript) = annotation
        && matches!(subscript.value.as_ref(), ast::Expr::Name(name) if callable_names.contains(name.id.as_str()))
    {
        return callable_annotation_type(&subscript.slice, class_names, callable_names);
    }
    let ast::Expr::Name(name) = annotation else {
        return failure(
            "frontend.python.dagcert.type-unsupported",
            "Dagcert operation v1 requires direct primitive or record annotations",
        );
    };
    match name.id.as_str() {
        "int" => Ok(ValueType::Int),
        "float" => Ok(ValueType::Float),
        "bool" => Ok(ValueType::Bool),
        "str" => Ok(ValueType::Str),
        record if class_names.contains(record) => Ok(ValueType::Record(record.to_owned())),
        other => failure(
            "frontend.python.dagcert.type-unsupported",
            format!("unsupported Dagcert operation type {other:?}"),
        ),
    }
}

fn callable_annotation_type(
    slice: &ast::Expr,
    class_names: &BTreeSet<String>,
    callable_names: &BTreeSet<String>,
) -> Result<ValueType, OperationFailure> {
    let ast::Expr::Tuple(parts) = slice else {
        return failure(
            "frontend.python.dagcert.callable-signature-unsupported",
            "Callable requires an explicit parameter list and return type",
        );
    };
    if parts.elts.len() != 2 {
        return failure(
            "frontend.python.dagcert.callable-signature-unsupported",
            "Callable requires exactly one parameter-list component and one return type",
        );
    }
    let ast::Expr::List(parameters) = &parts.elts[0] else {
        return failure(
            "frontend.python.dagcert.callable-signature-unsupported",
            "Callable parameters must be a finite explicit list; ellipsis and parameter specifications are unsupported",
        );
    };
    let mut parameter_types = Vec::new();
    for parameter in &parameters.elts {
        let parameter_type = annotation_type(parameter, class_names, callable_names)?;
        if matches!(parameter_type, ValueType::Callable(_)) {
            return failure(
                "frontend.python.dagcert.callable-higher-order-unsupported",
                "nested callable parameters are outside the closed callback fragment",
            );
        }
        parameter_types.push(parameter_type);
    }
    let return_type = annotation_type(&parts.elts[1], class_names, callable_names)?;
    if matches!(return_type, ValueType::Callable(_)) {
        return failure(
            "frontend.python.dagcert.callable-higher-order-unsupported",
            "callable-valued callback returns are outside the closed callback fragment",
        );
    }
    Ok(ValueType::Callable(CallableSignature {
        parameters: parameter_types,
        return_type: Box::new(return_type),
    }))
}

fn verify_operation(
    function: &ast::StmtFunctionDef,
    operation_names: &BTreeSet<String>,
    union_names: &BTreeSet<String>,
    callable_names: &BTreeSet<String>,
    records: &BTreeMap<String, RecordShape>,
    callable_bindings: &[ResolvedCallableBinding],
) -> Result<(), OperationFailure> {
    if function.decorator_list.len() != 1
        || !matches!(&function.decorator_list[0], ast::Expr::Name(name) if operation_names.contains(name.id.as_str()))
        || !function.type_params.is_empty()
        || function.args.vararg.is_some()
        || function.args.kwarg.is_some()
        || !function.args.posonlyargs.is_empty()
        || !function.args.kwonlyargs.is_empty()
        || function.args.args.len() != 1
        || function.args.args[0].default.is_some()
    {
        return failure(
            "frontend.python.dagcert.operation-signature-unsupported",
            format!(
                "operation {:?} must be @operation with one typed positional input",
                function.name
            ),
        );
    }
    let parameter = &function.args.args[0].def;
    let input_type = parameter
        .annotation
        .as_deref()
        .ok_or_else(|| OperationFailure {
            code: "frontend.python.dagcert.input-type-missing",
            message: format!("operation {:?} input is untyped", function.name),
            byte_offset: Some(function.range.start().into()),
        })?;
    let class_names = records.keys().cloned().collect::<BTreeSet<_>>();
    let ValueType::Record(input_record) =
        annotation_type(input_type, &class_names, callable_names)?
    else {
        return failure(
            "frontend.python.dagcert.input-type-unsupported",
            "operation input must be one frozen source record",
        );
    };
    validate_operation_callable_bindings(
        function.name.as_str(),
        &input_record,
        records,
        callable_bindings,
    )?;
    let return_annotation = function
        .returns
        .as_deref()
        .ok_or_else(|| OperationFailure {
            code: "frontend.python.dagcert.return-type-missing",
            message: format!("operation {:?} return is untyped", function.name),
            byte_offset: Some(function.range.start().into()),
        })?;
    let mut outcomes = Vec::new();
    flatten_union(return_annotation, union_names, &mut outcomes);
    if outcomes.is_empty() {
        return failure(
            "frontend.python.dagcert.outcome-union-empty",
            "operation return union is empty",
        );
    }
    let mut outcome_names = BTreeSet::new();
    for outcome in outcomes {
        let ValueType::Record(name) = annotation_type(outcome, &class_names, callable_names)?
        else {
            return failure(
                "frontend.python.dagcert.outcome-type-unsupported",
                "every operation outcome must be a frozen source record",
            );
        };
        if !outcome_names.insert(name) {
            return failure(
                "frontend.python.dagcert.outcome-type-duplicate",
                "operation return union contains duplicate records",
            );
        }
    }
    let context = OperationBodyContext {
        input_name: parameter.arg.as_str(),
        input_record: &input_record,
        outcomes: &outcome_names,
        records,
        operation_name: function.name.as_str(),
        callable_bindings,
    };
    let effects = verify_statements(&function.body, &context, &mut BTreeMap::new())?;
    if !effects.normal_path_returns || !effects.raised_exceptions.is_empty() {
        let exception_detail = if effects.raised_exceptions.is_empty() {
            String::new()
        } else {
            format!(
                "; uncaught callback outcomes: {}",
                effects
                    .raised_exceptions
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        return failure(
            "frontend.python.dagcert.operation-not-total",
            format!(
                "operation {:?} has a reachable missing-return or exceptional path{}",
                function.name, exception_detail
            ),
        );
    }
    Ok(())
}

fn validate_operation_callable_bindings(
    operation_name: &str,
    input_record: &str,
    records: &BTreeMap<String, RecordShape>,
    callable_bindings: &[ResolvedCallableBinding],
) -> Result<(), OperationFailure> {
    let operation_bindings = callable_bindings
        .iter()
        .filter(|binding| binding.operation == operation_name)
        .collect::<Vec<_>>();
    let callable_fields = records[input_record]
        .fields
        .iter()
        .filter_map(|(name, value_type)| match value_type {
            ValueType::Callable(signature) => Some((name, signature)),
            _ => None,
        })
        .collect::<Vec<_>>();
    for (field, signature) in &callable_fields {
        let matching = operation_bindings
            .iter()
            .filter(|binding| binding.input_record == input_record && binding.field == **field)
            .collect::<Vec<_>>();
        let [binding] = matching.as_slice() else {
            return failure(
                if matching.is_empty() {
                    "frontend.python.dagcert.callable-binding-missing"
                } else {
                    "frontend.python.dagcert.callable-binding-duplicate"
                },
                format!(
                    "callable field {input_record}.{field} requires exactly one concrete source or external-contract binding"
                ),
            );
        };
        let actual = signature_from_contract(&binding.contract);
        if *signature != &actual {
            return failure(
                "frontend.python.dagcert.callable-binding-type-mismatch",
                format!(
                    "provider {} has signature {actual:?}, but {input_record}.{field} is annotated {signature:?}",
                    binding.provider_description
                ),
            );
        }
    }
    for binding in operation_bindings {
        if binding.input_record != input_record {
            return failure(
                "frontend.python.dagcert.callable-binding-input-mismatch",
                format!(
                    "binding for operation {operation_name:?} names input record {:?}, but source declares {input_record:?}",
                    binding.input_record
                ),
            );
        }
        if !callable_fields
            .iter()
            .any(|(field, _)| *field == &binding.field)
        {
            return failure(
                "frontend.python.dagcert.callable-binding-field-mismatch",
                format!(
                    "binding for operation {operation_name:?} names non-callable or unknown field {:?}",
                    binding.field
                ),
            );
        }
    }
    Ok(())
}

fn flatten_union<'a>(
    annotation: &'a ast::Expr,
    union_names: &BTreeSet<String>,
    output: &mut Vec<&'a ast::Expr>,
) {
    if let ast::Expr::BinOp(operation) = annotation
        && operation.op == ast::Operator::BitOr
    {
        flatten_union(&operation.left, union_names, output);
        flatten_union(&operation.right, union_names, output);
    } else if let ast::Expr::Subscript(union) = annotation
        && matches!(union.value.as_ref(), ast::Expr::Name(name) if union_names.contains(name.id.as_str()))
    {
        match union.slice.as_ref() {
            ast::Expr::Tuple(items) => {
                for item in &items.elts {
                    flatten_union(item, union_names, output);
                }
            }
            item => flatten_union(item, union_names, output),
        }
    } else {
        output.push(annotation);
    }
}

struct OperationBodyContext<'a> {
    input_name: &'a str,
    input_record: &'a str,
    outcomes: &'a BTreeSet<String>,
    records: &'a BTreeMap<String, RecordShape>,
    operation_name: &'a str,
    callable_bindings: &'a [ResolvedCallableBinding],
}

fn verify_statements(
    statements: &[ast::Stmt],
    context: &OperationBodyContext<'_>,
    locals: &mut BTreeMap<String, ValueType>,
) -> Result<StatementEffects, OperationFailure> {
    let mut returned = false;
    let mut raised_exceptions = BTreeSet::new();
    for (index, statement) in statements.iter().enumerate() {
        if returned {
            return failure(
                "frontend.python.dagcert.unreachable-statement-unsupported",
                "operation contains a statement after every path has returned",
            );
        }
        match statement {
            _ if index == 0 && is_docstring(statement) => {}
            ast::Stmt::Return(returned_value) => {
                let Some(value) = returned_value.value.as_deref() else {
                    return failure(
                        "frontend.python.dagcert.outcome-missing",
                        "operation must return one declared outcome record",
                    );
                };
                raised_exceptions.extend(verify_outcome_constructor(value, context, locals)?);
                returned = true;
            }
            ast::Stmt::Assign(assignment) => {
                let [target] = assignment.targets.as_slice() else {
                    return failure(
                        "frontend.python.dagcert.local-assignment-target-unsupported",
                        "operation local assignment requires exactly one target",
                    );
                };
                let ast::Expr::Name(target) = target else {
                    return located_failure(
                        "frontend.python.dagcert.local-assignment-target-unsupported",
                        "operation callback results may be stored only in a fresh local name",
                        target,
                    );
                };
                let (value_type, exceptions) = infer_operation_expression(
                    &assignment.value,
                    context.input_name,
                    context.input_record,
                    context.records,
                    context.operation_name,
                    context.callable_bindings,
                    locals,
                )?;
                raised_exceptions.extend(exceptions);
                bind_operation_local(
                    target.id.as_str(),
                    value_type,
                    context.input_name,
                    context.records,
                    locals,
                )?;
            }
            ast::Stmt::AnnAssign(assignment) => {
                let ast::Expr::Name(target) = assignment.target.as_ref() else {
                    return located_failure(
                        "frontend.python.dagcert.local-assignment-target-unsupported",
                        "annotated operation callback results require a fresh local name",
                        &assignment.target,
                    );
                };
                let Some(value) = assignment.value.as_deref() else {
                    return failure(
                        "frontend.python.dagcert.local-assignment-value-missing",
                        "operation locals cannot be declared before they receive a proved value",
                    );
                };
                let expected = operation_local_annotation(&assignment.annotation)?;
                let (actual, exceptions) = infer_operation_expression(
                    value,
                    context.input_name,
                    context.input_record,
                    context.records,
                    context.operation_name,
                    context.callable_bindings,
                    locals,
                )?;
                raised_exceptions.extend(exceptions);
                if actual != expected {
                    return located_failure(
                        "frontend.python.dagcert.local-assignment-type-mismatch",
                        format!(
                            "annotated operation local {:?} expects {expected:?}, received {actual:?}",
                            target.id
                        ),
                        value,
                    );
                }
                bind_operation_local(
                    target.id.as_str(),
                    actual,
                    context.input_name,
                    context.records,
                    locals,
                )?;
            }
            ast::Stmt::If(branch) => {
                let (condition, condition_exceptions) = infer_operation_expression(
                    &branch.test,
                    context.input_name,
                    context.input_record,
                    context.records,
                    context.operation_name,
                    context.callable_bindings,
                    locals,
                )?;
                raised_exceptions.extend(condition_exceptions);
                if condition != ValueType::Bool {
                    return failure(
                        "frontend.python.dagcert.condition-type-mismatch",
                        "operation branch condition must be bool",
                    );
                }
                let mut then_locals = locals.clone();
                let then_returns = verify_statements(&branch.body, context, &mut then_locals)?;
                let mut else_locals = locals.clone();
                let else_returns = if branch.orelse.is_empty() {
                    StatementEffects::default()
                } else {
                    verify_statements(&branch.orelse, context, &mut else_locals)?
                };
                raised_exceptions.extend(then_returns.raised_exceptions);
                raised_exceptions.extend(else_returns.raised_exceptions);
                returned = then_returns.normal_path_returns && else_returns.normal_path_returns;
                merge_branch_locals(
                    locals,
                    &then_locals,
                    then_returns.normal_path_returns,
                    &else_locals,
                    else_returns.normal_path_returns,
                )?;
            }
            ast::Stmt::Try(try_statement) => {
                if !try_statement.orelse.is_empty() || !try_statement.finalbody.is_empty() {
                    return failure(
                        "frontend.python.dagcert.try-shape-unsupported",
                        "callback operation try statements do not yet admit else or finally",
                    );
                }
                let entry_locals = locals.clone();
                let mut body_locals = entry_locals.clone();
                let body = verify_statements(&try_statement.body, context, &mut body_locals)?;
                let mut uncaught = body.raised_exceptions;
                let mut handlers_cover_all_normal_paths = true;
                let mut continuing_handler_locals = Vec::new();
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    if handler.name.is_some() {
                        return failure(
                            "frontend.python.dagcert.exception-binding-unsupported",
                            "caught callback exceptions cannot escape through a handler binding",
                        );
                    }
                    let caught = caught_exception_names(handler.type_.as_deref(), &uncaught)?;
                    for exception in caught {
                        uncaught.remove(&exception);
                    }
                    let mut handler_locals = entry_locals.clone();
                    let handler_effects =
                        verify_statements(&handler.body, context, &mut handler_locals)?;
                    handlers_cover_all_normal_paths &= handler_effects.normal_path_returns;
                    if !handler_effects.normal_path_returns {
                        continuing_handler_locals.push(handler_locals);
                    }
                    uncaught.extend(handler_effects.raised_exceptions);
                }
                raised_exceptions.extend(uncaught);
                returned = body.normal_path_returns && handlers_cover_all_normal_paths;
                if !returned {
                    let mut continuing = Vec::new();
                    if !body.normal_path_returns {
                        continuing.push(body_locals);
                    }
                    continuing.extend(continuing_handler_locals);
                    merge_continuing_locals(locals, &entry_locals, &continuing)?;
                }
            }
            _ => {
                return failure(
                    "frontend.python.dagcert.operation-statement-unsupported",
                    format!("operation contains unsupported statement {statement:?}"),
                );
            }
        }
    }
    Ok(StatementEffects {
        normal_path_returns: returned,
        raised_exceptions,
    })
}

fn bind_operation_local(
    name: &str,
    value_type: ValueType,
    input_name: &str,
    records: &BTreeMap<String, RecordShape>,
    locals: &mut BTreeMap<String, ValueType>,
) -> Result<(), OperationFailure> {
    if name == input_name || records.contains_key(name) {
        return failure(
            "frontend.python.dagcert.local-binding-shadowed-or-mutated",
            format!("operation local {name:?} shadows a source binding"),
        );
    }
    if matches!(value_type, ValueType::Callable(_)) {
        return failure(
            "frontend.python.dagcert.callable-alias-unsupported",
            "callable fields cannot be copied, stored, or rebound inside an operation",
        );
    }
    if let Some(existing) = locals.get(name) {
        if existing != &value_type {
            return failure(
                "frontend.python.dagcert.local-reassignment-type-mismatch",
                format!(
                    "operation local {name:?} was {existing:?} and cannot be reassigned {value_type:?}"
                ),
            );
        }
        return Ok(());
    }
    locals.insert(name.to_owned(), value_type);
    Ok(())
}

fn operation_local_annotation(annotation: &ast::Expr) -> Result<ValueType, OperationFailure> {
    let ast::Expr::Name(name) = annotation else {
        return located_failure(
            "frontend.python.dagcert.local-annotation-unsupported",
            "operation locals currently require direct primitive annotations",
            annotation,
        );
    };
    match name.id.as_str() {
        "int" => Ok(ValueType::Int),
        "float" => Ok(ValueType::Float),
        "bool" => Ok(ValueType::Bool),
        "str" => Ok(ValueType::Str),
        _ => located_failure(
            "frontend.python.dagcert.local-annotation-unsupported",
            format!("unsupported operation local annotation {:?}", name.id),
            annotation,
        ),
    }
}

fn merge_branch_locals(
    destination: &mut BTreeMap<String, ValueType>,
    then_locals: &BTreeMap<String, ValueType>,
    then_returns: bool,
    else_locals: &BTreeMap<String, ValueType>,
    else_returns: bool,
) -> Result<(), OperationFailure> {
    match (then_returns, else_returns) {
        (true, true) => Ok(()),
        (true, false) => {
            destination.clone_from(else_locals);
            Ok(())
        }
        (false, true) => {
            destination.clone_from(then_locals);
            Ok(())
        }
        (false, false) if then_locals == else_locals => {
            destination.clone_from(then_locals);
            Ok(())
        }
        (false, false) => failure(
            "frontend.python.dagcert.local-branch-merge-unsupported",
            "continuing operation branches must establish the same immutable local bindings",
        ),
    }
}

fn merge_continuing_locals(
    destination: &mut BTreeMap<String, ValueType>,
    entry: &BTreeMap<String, ValueType>,
    continuing: &[BTreeMap<String, ValueType>],
) -> Result<(), OperationFailure> {
    let Some(first) = continuing.first() else {
        destination.clone_from(entry);
        return Ok(());
    };
    if continuing.iter().all(|candidate| candidate == first) {
        destination.clone_from(first);
        Ok(())
    } else {
        failure(
            "frontend.python.dagcert.local-try-merge-unsupported",
            "continuing try/except paths must establish the same immutable local bindings",
        )
    }
}

fn is_docstring(statement: &ast::Stmt) -> bool {
    matches!(
        statement,
        ast::Stmt::Expr(expression)
            if matches!(expression.value.as_ref(), ast::Expr::Constant(value)
                if matches!(value.value, ast::Constant::Str(_)))
    )
}

fn declaration_name(statement: &ast::Stmt) -> Option<&str> {
    match statement {
        ast::Stmt::ClassDef(class) => Some(class.name.as_str()),
        ast::Stmt::FunctionDef(function) => Some(function.name.as_str()),
        ast::Stmt::AsyncFunctionDef(function) => Some(function.name.as_str()),
        _ => None,
    }
}

fn is_modeled_builtin_exception_name(name: &str) -> bool {
    matches!(
        name,
        "BaseException"
            | "Exception"
            | "ValueError"
            | "TypeError"
            | "LookupError"
            | "IndexError"
            | "KeyError"
            | "ArithmeticError"
            | "ZeroDivisionError"
            | "RuntimeError"
            | "SystemExit"
            | "KeyboardInterrupt"
            | "GeneratorExit"
    )
}

fn verify_outcome_constructor(
    expression: &ast::Expr,
    context: &OperationBodyContext<'_>,
    locals: &BTreeMap<String, ValueType>,
) -> Result<BTreeSet<String>, OperationFailure> {
    let ast::Expr::Call(call) = expression else {
        return failure(
            "frontend.python.dagcert.outcome-constructor-required",
            "operation return must directly construct one declared outcome",
        );
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return failure(
            "frontend.python.dagcert.outcome-constructor-required",
            "operation outcome constructor must be a direct source class name",
        );
    };
    if !context.outcomes.contains(name.id.as_str()) || !call.keywords.is_empty() {
        return failure(
            "frontend.python.dagcert.outcome-constructor-mismatch",
            format!(
                "returned constructor {:?} is not a declared positional outcome",
                name.id
            ),
        );
    }
    let shape = &context.records[name.id.as_str()];
    if call.args.len() != shape.fields.len() {
        return failure(
            "frontend.python.dagcert.outcome-constructor-arity",
            format!(
                "outcome {:?} expects {} fields, received {}",
                name.id,
                shape.fields.len(),
                call.args.len()
            ),
        );
    }
    let mut raised_exceptions = BTreeSet::new();
    for ((field, expected), argument) in shape.fields.iter().zip(&call.args) {
        let (actual, argument_exceptions) = infer_operation_expression(
            argument,
            context.input_name,
            context.input_record,
            context.records,
            context.operation_name,
            context.callable_bindings,
            locals,
        )?;
        raised_exceptions.extend(argument_exceptions);
        if &actual != expected {
            return failure(
                "frontend.python.dagcert.outcome-field-type-mismatch",
                format!("outcome field {field:?} expects {expected:?}, received {actual:?}"),
            );
        }
    }
    Ok(raised_exceptions)
}

fn infer_operation_expression(
    expression: &ast::Expr,
    input_name: &str,
    input_record: &str,
    records: &BTreeMap<String, RecordShape>,
    operation_name: &str,
    callable_bindings: &[ResolvedCallableBinding],
    locals: &BTreeMap<String, ValueType>,
) -> Result<(ValueType, BTreeSet<String>), OperationFailure> {
    let ast::Expr::Call(call) = expression else {
        return infer_expression(expression, input_name, input_record, records, locals)
            .map(|value_type| (value_type, BTreeSet::new()));
    };
    if !call.keywords.is_empty() {
        return located_failure(
            "frontend.python.dagcert.callable-keyword-unsupported",
            "bound callbacks currently require positional arguments",
            expression,
        );
    }
    let ast::Expr::Attribute(attribute) = call.func.as_ref() else {
        return unsupported_expression(expression);
    };
    let ast::Expr::Name(receiver) = attribute.value.as_ref() else {
        return unsupported_expression(expression);
    };
    if receiver.id.as_str() != input_name {
        return located_failure(
            "frontend.python.dagcert.callable-receiver-unsupported",
            "callback invocation must read the callable directly from the typed operation input",
            expression,
        );
    }
    let Some((_, ValueType::Callable(signature))) = records[input_record]
        .fields
        .iter()
        .find(|(field, _)| field == attribute.attr.as_str())
    else {
        return located_failure(
            "frontend.python.dagcert.callable-field-unknown",
            format!(
                "input record {input_record:?} has no callable field {:?}",
                attribute.attr
            ),
            expression,
        );
    };
    let matching = callable_bindings
        .iter()
        .filter(|binding| {
            binding.operation == operation_name
                && binding.input_record == input_record
                && binding.field == attribute.attr.as_str()
        })
        .collect::<Vec<_>>();
    let [binding] = matching.as_slice() else {
        let (code, message) = if matching.is_empty() {
            (
                "frontend.python.dagcert.callable-binding-missing",
                format!(
                    "callable field {input_record}.{} has no concrete source or external-contract provenance",
                    attribute.attr
                ),
            )
        } else {
            (
                "frontend.python.dagcert.callable-binding-duplicate",
                format!(
                    "callable field {input_record}.{} has multiple concrete bindings",
                    attribute.attr
                ),
            )
        };
        return located_failure(code, message, expression);
    };
    let contract_signature = signature_from_contract(&binding.contract);
    if signature != &contract_signature {
        return located_failure(
            "frontend.python.dagcert.callable-binding-type-mismatch",
            format!(
                "provider {} has signature {:?}, but {input_record}.{} is annotated {:?}",
                binding.provider_description, contract_signature, attribute.attr, signature
            ),
            expression,
        );
    }
    if call.args.len() != signature.parameters.len() {
        return located_failure(
            "frontend.python.dagcert.callable-arity-mismatch",
            format!(
                "callable field {} expects {} arguments, received {}",
                attribute.attr,
                signature.parameters.len(),
                call.args.len()
            ),
            expression,
        );
    }
    for (index, (argument, expected)) in call.args.iter().zip(&signature.parameters).enumerate() {
        let actual = infer_expression(argument, input_name, input_record, records, locals)?;
        if &actual != expected {
            return located_failure(
                "frontend.python.dagcert.callable-argument-type-mismatch",
                format!("callable argument {index} expects {expected:?}, received {actual:?}"),
                argument,
            );
        }
    }
    Ok((
        signature.return_type.as_ref().clone(),
        binding.contract.raised_exceptions.clone(),
    ))
}

fn signature_from_contract(contract: &CallableContract) -> CallableSignature {
    CallableSignature {
        parameters: contract
            .parameters
            .iter()
            .map(value_type_from_primitive)
            .collect(),
        return_type: Box::new(value_type_from_primitive(&contract.return_type)),
    }
}

fn value_type_from_primitive(value_type: &CallablePrimitiveType) -> ValueType {
    match value_type {
        CallablePrimitiveType::Int => ValueType::Int,
        CallablePrimitiveType::Float => ValueType::Float,
        CallablePrimitiveType::Bool => ValueType::Bool,
        CallablePrimitiveType::Str => ValueType::Str,
    }
}

fn caught_exception_names(
    handler_type: Option<&ast::Expr>,
    raised: &BTreeSet<String>,
) -> Result<BTreeSet<String>, OperationFailure> {
    let Some(handler_type) = handler_type else {
        return Ok(raised.clone());
    };
    let ast::Expr::Name(name) = handler_type else {
        return located_failure(
            "frontend.python.dagcert.exception-handler-type-unsupported",
            "callback handlers require one direct exception class name or a bare except",
            handler_type,
        );
    };
    Ok(raised
        .iter()
        .filter(|exception| exception_is_subtype_of(exception, name.id.as_str()))
        .cloned()
        .collect())
}

fn exception_is_subtype_of(exception: &str, handler: &str) -> bool {
    if exception == handler || handler == "BaseException" {
        return true;
    }
    match exception {
        "SystemExit" | "KeyboardInterrupt" | "GeneratorExit" => false,
        _ if handler == "Exception" => true,
        "ValueError" | "TypeError" | "LookupError" | "ArithmeticError" | "RuntimeError"
            if handler == "Exception" =>
        {
            true
        }
        "IndexError" | "KeyError" if matches!(handler, "LookupError" | "Exception") => true,
        "ZeroDivisionError" if matches!(handler, "ArithmeticError" | "Exception") => true,
        _ => false,
    }
}

fn infer_expression(
    expression: &ast::Expr,
    input_name: &str,
    input_record: &str,
    records: &BTreeMap<String, RecordShape>,
    locals: &BTreeMap<String, ValueType>,
) -> Result<ValueType, OperationFailure> {
    match expression {
        ast::Expr::Name(name) => {
            locals
                .get(name.id.as_str())
                .cloned()
                .ok_or_else(|| OperationFailure {
                    code: "frontend.python.dagcert.local-name-unbound",
                    message: format!("operation expression reads unbound local {:?}", name.id),
                    byte_offset: Some(name.range.start().into()),
                })
        }
        ast::Expr::Constant(value) => match value.value {
            ast::Constant::Int(_) => Ok(ValueType::Int),
            ast::Constant::Float(_) => Ok(ValueType::Float),
            ast::Constant::Bool(_) => Ok(ValueType::Bool),
            ast::Constant::Str(_) => Ok(ValueType::Str),
            _ => unsupported_expression(expression),
        },
        ast::Expr::Attribute(attribute) => {
            let ast::Expr::Name(receiver) = attribute.value.as_ref() else {
                return unsupported_expression(expression);
            };
            if receiver.id.as_str() != input_name {
                return failure(
                    "frontend.python.dagcert.field-receiver-unsupported",
                    "operation expressions may read fields only from the typed task input",
                );
            }
            records[input_record]
                .fields
                .iter()
                .find(|(field, _)| field == attribute.attr.as_str())
                .map(|(_, field_type)| field_type.clone())
                .ok_or_else(|| OperationFailure {
                    code: "frontend.python.dagcert.field-unknown",
                    message: format!("input record has no field {:?}", attribute.attr),
                    byte_offset: Some(attribute.range.start().into()),
                })
        }
        ast::Expr::UnaryOp(operation) => {
            let operand = infer_expression(
                &operation.operand,
                input_name,
                input_record,
                records,
                locals,
            )?;
            match operation.op {
                ast::UnaryOp::Not if operand == ValueType::Bool => Ok(ValueType::Bool),
                ast::UnaryOp::UAdd | ast::UnaryOp::USub
                    if matches!(operand, ValueType::Int | ValueType::Float) =>
                {
                    Ok(operand)
                }
                _ => unsupported_expression(expression),
            }
        }
        ast::Expr::BinOp(operation) => {
            let left =
                infer_expression(&operation.left, input_name, input_record, records, locals)?;
            let right =
                infer_expression(&operation.right, input_name, input_record, records, locals)?;
            match operation.op {
                ast::Operator::Add
                    if left == right
                        && matches!(left, ValueType::Int | ValueType::Float | ValueType::Str) =>
                {
                    Ok(left)
                }
                ast::Operator::Sub | ast::Operator::Mult
                    if left == right && matches!(left, ValueType::Int | ValueType::Float) =>
                {
                    Ok(left)
                }
                _ => located_failure(
                    "frontend.python.dagcert.partial-or-unsupported-operator",
                    format!(
                        "operator {:?} is partial or unsupported for {left:?} and {right:?}",
                        operation.op
                    ),
                    expression,
                ),
            }
        }
        ast::Expr::Compare(comparison)
            if comparison.ops.len() == 1 && comparison.comparators.len() == 1 =>
        {
            let left =
                infer_expression(&comparison.left, input_name, input_record, records, locals)?;
            let right = infer_expression(
                &comparison.comparators[0],
                input_name,
                input_record,
                records,
                locals,
            )?;
            if left != right {
                return failure(
                    "frontend.python.dagcert.comparison-type-mismatch",
                    "operation comparison operands have different types",
                );
            }
            match comparison.ops[0] {
                ast::CmpOp::Eq | ast::CmpOp::NotEq => Ok(ValueType::Bool),
                ast::CmpOp::Lt | ast::CmpOp::LtE | ast::CmpOp::Gt | ast::CmpOp::GtE
                    if matches!(left, ValueType::Int | ValueType::Float | ValueType::Str) =>
                {
                    Ok(ValueType::Bool)
                }
                _ => unsupported_expression(expression),
            }
        }
        ast::Expr::BoolOp(operation) => {
            for value in &operation.values {
                if infer_expression(value, input_name, input_record, records, locals)?
                    != ValueType::Bool
                {
                    return failure(
                        "frontend.python.dagcert.boolean-type-mismatch",
                        "boolean operation requires bool operands",
                    );
                }
            }
            Ok(ValueType::Bool)
        }
        ast::Expr::IfExp(conditional) => {
            if infer_expression(&conditional.test, input_name, input_record, records, locals)?
                != ValueType::Bool
            {
                return failure(
                    "frontend.python.dagcert.condition-type-mismatch",
                    "conditional expression test must be bool",
                );
            }
            let left =
                infer_expression(&conditional.body, input_name, input_record, records, locals)?;
            let right = infer_expression(
                &conditional.orelse,
                input_name,
                input_record,
                records,
                locals,
            )?;
            if left == right {
                Ok(left)
            } else {
                failure(
                    "frontend.python.dagcert.conditional-type-mismatch",
                    "conditional expression branches have different types",
                )
            }
        }
        ast::Expr::JoinedStr(joined) => {
            for value in &joined.values {
                match value {
                    ast::Expr::Constant(constant)
                        if matches!(constant.value, ast::Constant::Str(_)) => {}
                    ast::Expr::FormattedValue(formatted)
                        if formatted.format_spec.is_none()
                            && formatted.conversion == ast::ConversionFlag::None
                            && matches!(
                                infer_expression(
                                    &formatted.value,
                                    input_name,
                                    input_record,
                                    records,
                                    locals,
                                )?,
                                ValueType::Int
                                    | ValueType::Float
                                    | ValueType::Bool
                                    | ValueType::Str
                            ) => {}
                    _ => return unsupported_expression(value),
                }
            }
            Ok(ValueType::Str)
        }
        _ => unsupported_expression(expression),
    }
}

fn unsupported_expression<T>(expression: &ast::Expr) -> Result<T, OperationFailure> {
    located_failure(
        "frontend.python.dagcert.expression-unsupported",
        format!("operation expression is not proved total: {expression:?}"),
        expression,
    )
}

fn located_failure<T>(
    code: &'static str,
    message: impl Into<String>,
    expression: &ast::Expr,
) -> Result<T, OperationFailure> {
    Err(OperationFailure {
        code,
        message: message.into(),
        byte_offset: Some(expression.range().start().into()),
    })
}

fn failure<T>(code: &'static str, message: impl Into<String>) -> Result<T, OperationFailure> {
    Err(OperationFailure {
        code,
        message: message.into(),
        byte_offset: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const APP: &str = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass WorkInput:\n    value: int\n\n@dataclass(frozen=True)\nclass WorkCompleted:\n    value: int\n\n@operation\ndef work(request: WorkInput) -> WorkCompleted:\n    return WorkCompleted(request.value + 1)\n";

    #[test]
    fn proves_real_dagcert_operation_shape() {
        let result = verify_operation_module(APP, "app.py", &["work".to_owned()]).unwrap();
        assert_eq!(result.operations, ["work"]);
    }

    #[test]
    fn proves_total_probability_float_operations() {
        let source = "from dataclasses import dataclass\nfrom typing import Union\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass ChanceRequest:\n    combine: float\n    mutation: float\n    automatic: bool\n    new: float\n\n@dataclass(frozen=True)\nclass Chances:\n    combine: float\n    mutation: float\n    new: float\n\n@dataclass(frozen=True)\nclass Invalid:\n    reason: str\n\n@operation\ndef validate(request: ChanceRequest) -> Union[Chances, Invalid]:\n    combine = request.combine\n    mutation = request.mutation\n    new = request.new\n    if request.automatic:\n        mutation = 1.0 - combine - new\n    if combine != combine or mutation != mutation or new != new:\n        return Invalid('chance must not be NaN')\n    if combine < 0.0 or mutation < 0.0 or new < 0.0:\n        return Invalid('chance must be nonnegative')\n    total = combine + mutation + new\n    difference = total - 1.0\n    if difference < -0.000000001 or difference > 0.000000001:\n        return Invalid('chances must sum to one')\n    return Chances(combine, mutation, new)\n";
        let result =
            verify_operation_module(source, "probabilities.py", &["validate".to_owned()]).unwrap();
        assert_eq!(result.operations, ["validate"]);
    }

    #[test]
    fn refuses_partial_float_division() {
        let source = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Request:\n    numerator: float\n    denominator: float\n\n@dataclass(frozen=True)\nclass Completed:\n    value: float\n\n@operation\ndef divide(request: Request) -> Completed:\n    return Completed(request.numerator / request.denominator)\n";
        let error =
            verify_operation_module(source, "division.py", &["divide".to_owned()]).unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.dagcert.partial-or-unsupported-operator"
        );
    }

    #[test]
    fn refuses_type_changing_primitive_reassignment() {
        let source = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Request:\n    value: float\n\n@dataclass(frozen=True)\nclass Completed:\n    value: float\n\n@operation\ndef change_type(request: Request) -> Completed:\n    value = request.value\n    value = 1\n    return Completed(value)\n";
        let error = verify_operation_module(source, "reassignment.py", &["change_type".to_owned()])
            .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.dagcert.local-reassignment-type-mismatch"
        );
    }

    #[test]
    fn proves_total_float_source_callback() {
        let provider = "def clamp(value: float) -> float:\n    if value < 0.0:\n        return 0.0\n    return value\n";
        let contract = analyze_source_callable(provider, "provider.py", "clamp").unwrap();
        assert_eq!(contract.parameters, [CallablePrimitiveType::Float]);
        assert_eq!(contract.return_type, CallablePrimitiveType::Float);
        assert!(contract.raised_exceptions.is_empty());
    }

    #[test]
    fn refuses_mypy_clean_partial_integer_division() {
        let source = APP.replace("request.value + 1", "10 // request.value");
        let error = verify_operation_module(&source, "app.py", &["work".to_owned()]).unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.dagcert.partial-or-unsupported-operator"
        );
    }

    #[test]
    fn proves_total_typed_outcome_branches() {
        let source = "from dataclasses import dataclass\nfrom dagcert import operation\n\n@dataclass(frozen=True, slots=True)\nclass Request:\n    ready: bool\n    value: int\n\n@dataclass(frozen=True)\nclass Completed:\n    value: int\n\n@dataclass(frozen=True)\nclass Deferred:\n    value: int\n\n@operation\ndef choose(request: Request) -> Completed | Deferred:\n    if request.ready:\n        return Completed(request.value)\n    return Deferred(request.value)\n";
        let result = verify_operation_module(source, "branch.py", &["choose".to_owned()]).unwrap();
        assert_eq!(result.operations, ["choose"]);
    }

    #[test]
    fn proves_imported_typing_union_outcomes() {
        let source = "from dataclasses import dataclass\nfrom typing import Union as Outcome\nfrom dagcert import operation\n\n@dataclass(frozen=True)\nclass Request:\n    ready: bool\n\n@dataclass(frozen=True)\nclass Completed:\n    ready: bool\n\n@dataclass(frozen=True)\nclass Deferred:\n    ready: bool\n\n@operation\ndef choose(request: Request) -> Outcome[Completed, Deferred]:\n    if request.ready:\n        return Completed(True)\n    return Deferred(False)\n";
        let result = verify_operation_module(source, "union.py", &["choose".to_owned()]).unwrap();
        assert_eq!(result.operations, ["choose"]);
    }

    #[test]
    fn proves_primitive_field_formatting_without_user_dispatch() {
        let source = "from dataclasses import dataclass\nfrom dagcert import operation\n\n@dataclass(frozen=True)\nclass Request:\n    value: int\n\n@dataclass(frozen=True)\nclass Completed:\n    text: str\n\n@operation\ndef render(request: Request) -> Completed:\n    return Completed(f\"value:{request.value}\")\n";
        let result = verify_operation_module(source, "format.py", &["render".to_owned()]).unwrap();
        assert_eq!(result.operations, ["render"]);
    }

    #[test]
    fn refuses_reachable_missing_outcome() {
        let source = "from dataclasses import dataclass\nfrom dagcert import operation\n\n@dataclass(frozen=True)\nclass Request:\n    ready: bool\n\n@dataclass(frozen=True)\nclass Completed:\n    ready: bool\n\n@operation\ndef choose(request: Request) -> Completed:\n    if request.ready:\n        return Completed(True)\n";
        let error =
            verify_operation_module(source, "missing.py", &["choose".to_owned()]).unwrap_err();
        assert_eq!(error.code, "frontend.python.dagcert.operation-not-total");
    }

    #[test]
    fn permits_non_executable_module_record_and_operation_docstrings() {
        let source = "\"\"\"Module docs.\"\"\"\nfrom dataclasses import dataclass\nfrom dagcert import operation\n\n@dataclass(frozen=True)\nclass Request:\n    \"\"\"Input docs.\"\"\"\n    value: int\n\n@dataclass(frozen=True)\nclass Completed:\n    \"\"\"Outcome docs.\"\"\"\n    value: int\n\n@operation\ndef work(request: Request) -> Completed:\n    \"\"\"Operation docs.\"\"\"\n    return Completed(request.value)\n";
        let result =
            verify_operation_module(source, "documented.py", &["work".to_owned()]).unwrap();
        assert_eq!(result.operations, ["work"]);
    }

    #[test]
    fn composes_a_concrete_source_callback_and_closes_its_exception_outcome() {
        let provider = "def enhance(value: str) -> str:\n    if value == 'bad':\n        raise ValueError('rejected')\n    return value + '!'\n";
        let contract = analyze_source_callable(provider, "provider.py", "enhance").unwrap();
        assert_eq!(
            contract.raised_exceptions,
            BTreeSet::from(["ValueError".to_owned()])
        );
        let source = "from dataclasses import dataclass\nfrom typing import Callable\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Request:\n    value: str\n    enhance: Callable[[str], str]\n\n@dataclass(frozen=True)\nclass Completed:\n    value: str\n\n@dataclass(frozen=True)\nclass Rejected:\n    value: str\n\n@operation\ndef prepare(request: Request) -> Completed | Rejected:\n    try:\n        return Completed(request.enhance(request.value))\n    except ValueError:\n        return Rejected(request.value)\n";
        let result = verify_operation_module_with_bindings(
            source,
            "consumer.py",
            &["prepare".to_owned()],
            &[ResolvedCallableBinding {
                operation: "prepare".to_owned(),
                input_record: "Request".to_owned(),
                field: "enhance".to_owned(),
                provider_description: "provider.py:enhance".to_owned(),
                source_provider: Some(SourceCallableProvider {
                    path: "provider.py".to_owned(),
                    symbol: "enhance".to_owned(),
                }),
                contract,
            }],
        )
        .unwrap();
        assert_eq!(result.operations, ["prepare"]);
    }

    #[test]
    fn refuses_abstract_or_uncaught_callable_field_effects() {
        let provider = "def enhance(value: str) -> str:\n    raise KeyboardInterrupt()\n";
        let contract = analyze_source_callable(provider, "provider.py", "enhance").unwrap();
        let source = "from dataclasses import dataclass\nfrom typing import Callable\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Request:\n    value: str\n    enhance: Callable[[str], str]\n\n@dataclass(frozen=True)\nclass Completed:\n    value: str\n\n@operation\ndef prepare(request: Request) -> Completed:\n    return Completed(request.enhance(request.value))\n";
        let missing =
            verify_operation_module(source, "consumer.py", &["prepare".to_owned()]).unwrap_err();
        assert_eq!(
            missing.code,
            "frontend.python.dagcert.callable-binding-missing"
        );

        let uncaught = verify_operation_module_with_bindings(
            source,
            "consumer.py",
            &["prepare".to_owned()],
            &[ResolvedCallableBinding {
                operation: "prepare".to_owned(),
                input_record: "Request".to_owned(),
                field: "enhance".to_owned(),
                provider_description: "provider.py:enhance".to_owned(),
                source_provider: Some(SourceCallableProvider {
                    path: "provider.py".to_owned(),
                    symbol: "enhance".to_owned(),
                }),
                contract,
            }],
        )
        .unwrap_err();
        assert_eq!(uncaught.code, "frontend.python.dagcert.operation-not-total");
        assert!(uncaught.message.contains("KeyboardInterrupt"));
    }

    #[test]
    fn source_callback_analysis_rejects_unmodeled_indirection_and_variadics() {
        for source in [
            "def callback(value: str) -> str:\n    alias = value\n    return alias\n",
            "def callback(*values: str) -> str:\n    return 'x'\n",
            "async def callback(value: str) -> str:\n    return value\n",
        ] {
            assert!(
                analyze_source_callable(source, "provider.py", "callback").is_err(),
                "unsupported provider unexpectedly verified:\n{source}"
            );
        }
    }
}
