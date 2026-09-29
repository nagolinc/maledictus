//! Closed totality checking for Dagcert's source-owned Python operation boundary.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_ast::Visitor;
use rustpython_parser::ast::Ranged;
use rustpython_parser::{Parse, ast};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ValueType {
    Int,
    Float,
    Bool,
    Str,
    Bytes,
    /// The result of `str.split`. It is kept distinct from an arbitrary list because index zero
    /// is total for every split result, while general list indexing is partial.
    StringSplitResult,
    VariadicTuple(Box<ValueType>),
    Record(String),
    RecordUnion(BTreeSet<String>),
    ExternalResult {
        success_type: Box<ValueType>,
        variants: BTreeSet<String>,
    },
    Callable(CallableSignature),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CallableSignature {
    parameters: Vec<ValueType>,
    return_type: Box<ValueType>,
}

mod callables;

pub use callables::{
    CallableContract, CallablePrimitiveType, ResolvedCallableBinding, SourceCallableProvider,
    analyze_source_callable,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RecordShape {
    pub(crate) fields: Vec<(String, ValueType)>,
    pub(crate) constructible: bool,
}

/// A source-owned operation module whose frozen record definitions were checked by this
/// frontend. `records` contains the module's complete checked record closure so nested imported
/// fields retain their shapes. `exports` contains only records actually declared by the module;
/// consumers may not manufacture exports merely because a provider imported them.
#[derive(Clone, Debug)]
pub(crate) struct ImportedOperationModule {
    pub module: String,
    records: BTreeMap<String, RecordShape>,
    record_exports: BTreeSet<String>,
    operations: BTreeMap<String, OperationShape>,
    external_boundaries: BTreeMap<String, ExternalBoundaryShape>,
}

impl ImportedOperationModule {
    pub(crate) fn module_name(&self) -> &str {
        &self.module
    }

    pub(crate) fn records(&self) -> &BTreeMap<String, RecordShape> {
        &self.records
    }

    pub(crate) fn record_exports(&self) -> &BTreeSet<String> {
        &self.record_exports
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct OperationShape {
    input_record: String,
    outcomes: BTreeSet<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ExternalBoundaryShape {
    boundary_id: String,
    parameters: Vec<ValueType>,
    success_type: ValueType,
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
    external_boundaries: BTreeSet<String>,
    external_result_types: BTreeMap<String, String>,
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
    verify_and_export_operation_module_with_imports(
        source,
        path,
        path,
        requested_symbols,
        callable_bindings,
        &[],
    )
    .map(|(verification, _)| verification)
}

pub(crate) fn is_operation_module_candidate(source: &str, path: &str) -> bool {
    let Ok(suite) = ast::Suite::parse(source, path) else {
        return false;
    };
    let Ok(markers) = imported_markers(&suite) else {
        return false;
    };
    suite.iter().any(|statement| {
        let ast::Stmt::FunctionDef(function) = statement else {
            return false;
        };
        function.decorator_list.iter().any(|decorator| {
            matches!(decorator, ast::Expr::Name(name) if markers.operations.contains(name.id.as_str()))
        })
    })
}

pub(crate) fn export_external_boundary_module(
    source: &str,
    path: &str,
    module: &str,
    requested_symbols: &[String],
) -> Result<ImportedOperationModule, OperationFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| OperationFailure {
        code: "frontend.python.dagcert.parse-error",
        message: error.to_string(),
        byte_offset: None,
    })?;
    let markers = imported_markers(&suite)?;
    if markers.external_boundaries.is_empty() {
        return failure(
            "frontend.python.dagcert.external-boundary-marker-missing",
            "embedded external adapter must import external_boundary from dagcert.runtime",
        );
    }
    let mut external_boundaries = BTreeMap::new();
    for statement in &suite {
        let ast::Stmt::FunctionDef(function) = statement else {
            continue;
        };
        if !requested_symbols
            .iter()
            .any(|symbol| symbol == function.name.as_str())
        {
            continue;
        }
        if function.decorator_list.len() != 1
            || !function.type_params.is_empty()
            || function.args.vararg.is_some()
            || function.args.kwarg.is_some()
            || !function.args.kwonlyargs.is_empty()
        {
            return failure(
                "frontend.python.dagcert.external-boundary-signature-unsupported",
                "embedded external adapter must be one nongeneric synchronous typed function",
            );
        }
        let ast::Expr::Call(decorator) = &function.decorator_list[0] else {
            return located_failure(
                "frontend.python.dagcert.external-boundary-decorator-invalid",
                "embedded external adapter requires @external_boundary(\"literal-id\")",
                &function.decorator_list[0],
            );
        };
        let ast::Expr::Name(decorator_name) = decorator.func.as_ref() else {
            return located_failure(
                "frontend.python.dagcert.external-boundary-decorator-invalid",
                "embedded external adapter decorator must be the trusted imported marker",
                &function.decorator_list[0],
            );
        };
        if !markers
            .external_boundaries
            .contains(decorator_name.id.as_str())
            || decorator.args.len() != 1
            || !decorator.keywords.is_empty()
        {
            return located_failure(
                "frontend.python.dagcert.external-boundary-decorator-invalid",
                "embedded external adapter requires @external_boundary(\"literal-id\")",
                &function.decorator_list[0],
            );
        }
        let ast::Expr::Constant(identifier) = &decorator.args[0] else {
            return located_failure(
                "frontend.python.dagcert.external-boundary-id-not-literal",
                "external boundary ID must be a nonempty string literal",
                &decorator.args[0],
            );
        };
        let ast::Constant::Str(boundary_id) = &identifier.value else {
            return located_failure(
                "frontend.python.dagcert.external-boundary-id-not-literal",
                "external boundary ID must be a nonempty string literal",
                &decorator.args[0],
            );
        };
        if boundary_id.trim().is_empty() {
            return located_failure(
                "frontend.python.dagcert.external-boundary-id-empty",
                "external boundary ID must be nonempty",
                &decorator.args[0],
            );
        }
        let mut parameters = Vec::new();
        for parameter in function.args.posonlyargs.iter().chain(&function.args.args) {
            if parameter.default.is_some() {
                return failure(
                    "frontend.python.dagcert.external-boundary-default-unsupported",
                    "embedded external adapter parameters may not have defaults",
                );
            }
            let Some(annotation) = parameter.def.annotation.as_deref() else {
                return failure(
                    "frontend.python.dagcert.external-boundary-type-missing",
                    "embedded external adapter parameters require source annotations",
                );
            };
            parameters.push(external_annotation_type(annotation)?);
        }
        let Some(return_annotation) = function.returns.as_deref() else {
            return failure(
                "frontend.python.dagcert.external-boundary-type-missing",
                "embedded external adapter requires a source return annotation",
            );
        };
        let shape = ExternalBoundaryShape {
            boundary_id: boundary_id.to_string(),
            parameters,
            success_type: external_annotation_type(return_annotation)?,
        };
        if external_boundaries
            .insert(function.name.to_string(), shape)
            .is_some()
        {
            return failure(
                "frontend.python.dagcert.external-boundary-symbol-duplicate",
                format!("external boundary symbol {:?} is duplicated", function.name),
            );
        }
    }
    let missing = requested_symbols
        .iter()
        .filter(|symbol| !external_boundaries.contains_key(symbol.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        return failure(
            "frontend.python.dagcert.external-boundary-symbol-missing",
            format!("requested embedded external boundary symbols are missing: {missing:?}"),
        );
    }
    Ok(ImportedOperationModule {
        module: module.to_owned(),
        records: BTreeMap::new(),
        record_exports: BTreeSet::new(),
        operations: BTreeMap::new(),
        external_boundaries,
    })
}

pub(crate) fn validate_embedded_external_call(
    consumer_source: &str,
    consumer_path: &str,
    operation_symbol: &str,
    adapter_module: &str,
    adapter_symbol: &str,
    boundary_id: &str,
    adapter: &ImportedOperationModule,
) -> Result<(), OperationFailure> {
    let Some(shape) = adapter.external_boundaries.get(adapter_symbol) else {
        return failure(
            "frontend.python.dagcert.embedded-external-adapter-symbol-missing",
            format!("adapter does not export boundary symbol {adapter_symbol:?}"),
        );
    };
    if shape.boundary_id != boundary_id {
        return failure(
            "frontend.python.dagcert.embedded-external-boundary-id-mismatch",
            format!(
                "adapter symbol {adapter_symbol:?} declares boundary {:?}, expected {boundary_id:?}",
                shape.boundary_id
            ),
        );
    }
    let suite =
        ast::Suite::parse(consumer_source, consumer_path).map_err(|error| OperationFailure {
            code: "frontend.python.dagcert.parse-error",
            message: error.to_string(),
            byte_offset: None,
        })?;
    let imported_names = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import
                        .module
                        .as_ref()
                        .is_some_and(|module| module.as_str() == adapter_module) =>
            {
                Some(import)
            }
            _ => None,
        })
        .flat_map(|import| &import.names)
        .filter(|alias| alias.name.as_str() == adapter_symbol)
        .map(|alias| {
            alias
                .asname
                .as_ref()
                .map_or(alias.name.as_str(), |name| name.as_str())
                .to_owned()
        })
        .collect::<BTreeSet<_>>();
    if imported_names.len() != 1 {
        return failure(
            "frontend.python.dagcert.embedded-external-import-missing",
            format!(
                "operation module must import {adapter_symbol:?} exactly once from {adapter_module:?}"
            ),
        );
    }
    let Some(function) = suite.iter().find_map(|statement| match statement {
        ast::Stmt::FunctionDef(function) if function.name.as_str() == operation_symbol => {
            Some(function)
        }
        _ => None,
    }) else {
        return failure(
            "frontend.python.dagcert.embedded-external-operation-missing",
            format!("operation symbol {operation_symbol:?} is missing"),
        );
    };
    let imported_name = imported_names
        .first()
        .expect("one imported boundary name")
        .clone();
    let mut collector = DirectCallCollector {
        callee: imported_name.as_str(),
        count: 0,
    };
    for statement in &function.body {
        collector.visit_stmt(statement.clone());
    }
    if collector.count == 0 {
        return failure(
            "frontend.python.dagcert.embedded-external-call-missing",
            format!(
                "operation {operation_symbol:?} does not directly call imported boundary {adapter_symbol:?}"
            ),
        );
    }
    Ok(())
}

struct DirectCallCollector<'a> {
    callee: &'a str,
    count: usize,
}

impl Visitor for DirectCallCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if matches!(node.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == self.callee) {
            self.count += 1;
        }
        self.generic_visit_expr_call(node);
    }
}

fn external_annotation_type(annotation: &ast::Expr) -> Result<ValueType, OperationFailure> {
    let ast::Expr::Name(name) = annotation else {
        return located_failure(
            "frontend.python.dagcert.external-boundary-type-unsupported",
            "embedded external adapter annotations must be direct primitive or nominal names",
            annotation,
        );
    };
    Ok(match name.id.as_str() {
        "int" => ValueType::Int,
        "float" => ValueType::Float,
        "bool" => ValueType::Bool,
        "str" => ValueType::Str,
        "bytes" => ValueType::Bytes,
        nominal => ValueType::Record(nominal.to_owned()),
    })
}

pub(crate) fn verify_and_export_operation_module_with_imports(
    source: &str,
    path: &str,
    module: &str,
    requested_symbols: &[String],
    callable_bindings: &[ResolvedCallableBinding],
    imported_modules: &[ImportedOperationModule],
) -> Result<(OperationVerification, ImportedOperationModule), OperationFailure> {
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
        .chain(&markers.external_boundaries)
        .chain(markers.external_result_types.keys())
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
    let imported_by_module = imported_modules
        .iter()
        .map(|imported| (imported.module.as_str(), imported))
        .collect::<BTreeMap<_, _>>();
    let mut records = BTreeMap::new();
    let mut record_origins = BTreeMap::new();
    let mut imported_record_names = BTreeSet::new();
    let mut imported_operations = BTreeMap::new();
    let mut imported_external_boundaries = BTreeMap::new();
    for statement in &suite {
        let ast::Stmt::ImportFrom(import) = statement else {
            continue;
        };
        let Some(imported_module_name) = import.module.as_ref().map(|name| name.as_str()) else {
            continue;
        };
        let Some(imported_module) = imported_by_module.get(imported_module_name) else {
            continue;
        };
        if import.level.is_some_and(|level| level != 0_u32) {
            return failure(
                "frontend.python.dagcert.source-import-relative",
                "Dagcert operation record imports must use absolute module names",
            );
        }
        for (name, shape) in &imported_module.records {
            if let Some(origin) = record_origins.get(name) {
                if origin != imported_module_name {
                    return failure(
                        "frontend.python.dagcert.source-import-name-collision",
                        format!(
                            "operation record name {name:?} is supplied by both {origin:?} and {imported_module_name:?}"
                        ),
                    );
                }
            } else {
                let mut hidden_shape = shape.clone();
                hidden_shape.constructible = false;
                records.insert(name.clone(), hidden_shape);
                record_origins.insert(name.clone(), imported_module_name.to_owned());
            }
        }
        for alias in &import.names {
            let imported_name = alias.name.as_str();
            if imported_name == "*" {
                return failure(
                    "frontend.python.dagcert.source-import-symbol-unproved",
                    "Dagcert operation source imports must name each proved record or operation",
                );
            }
            let local_name = alias
                .asname
                .as_ref()
                .map_or(imported_name, |name| name.as_str())
                .to_owned();
            if let Some(operation) = imported_module.operations.get(imported_name) {
                if records.contains_key(&local_name)
                    || imported_operations
                        .insert(local_name.clone(), operation.clone())
                        .is_some()
                {
                    return failure(
                        "frontend.python.dagcert.source-import-name-collision",
                        format!("imported operation name {local_name:?} is ambiguous"),
                    );
                }
                continue;
            }
            if let Some(boundary) = imported_module.external_boundaries.get(imported_name) {
                if records.contains_key(&local_name)
                    || imported_operations.contains_key(&local_name)
                    || imported_external_boundaries
                        .insert(local_name.clone(), boundary.clone())
                        .is_some()
                {
                    return failure(
                        "frontend.python.dagcert.source-import-name-collision",
                        format!("imported external boundary name {local_name:?} is ambiguous"),
                    );
                }
                continue;
            }
            if !imported_module.record_exports.contains(imported_name) {
                return failure(
                    "frontend.python.dagcert.source-import-symbol-unproved",
                    format!(
                        "module {imported_module_name:?} does not export proved operation record or function {imported_name:?}"
                    ),
                );
            }
            let mut shape = imported_module.records.get(imported_name).cloned().ok_or_else(|| {
                OperationFailure {
                    code: "frontend.python.dagcert.source-import-symbol-unproved",
                    message: format!(
                        "module {imported_module_name:?} omitted proved record shape {imported_name:?}"
                    ),
                    byte_offset: None,
                }
            })?;
            if record_origins
                .get(&local_name)
                .is_some_and(|origin| origin != imported_module_name)
                || imported_operations.contains_key(&local_name)
                || imported_external_boundaries.contains_key(&local_name)
                || !imported_record_names.insert(local_name.clone())
            {
                return failure(
                    "frontend.python.dagcert.source-import-name-collision",
                    format!("imported operation record name {local_name:?} is ambiguous"),
                );
            }
            shape.constructible = true;
            records.insert(local_name.clone(), shape);
            record_origins.insert(local_name, imported_module_name.to_owned());
        }
    }
    let mut class_names = imported_record_names.clone();
    let mut local_class_names = BTreeSet::new();
    for statement in &suite {
        if let ast::Stmt::ClassDef(class) = statement
            && (!local_class_names.insert(class.name.to_string())
                || !class_names.insert(class.name.to_string()))
        {
            return failure(
                "frontend.python.dagcert.class-duplicate",
                format!("record class {:?} is declared more than once", class.name),
            );
        }
    }
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
            ast::Stmt::ImportFrom(import)
                if allowed_import(import)
                    || import
                        .module
                        .as_ref()
                        .is_some_and(|name| imported_by_module.contains_key(name.as_str())) => {}
            ast::Stmt::ClassDef(class) => {
                if records.contains_key(class.name.as_str()) {
                    return failure(
                        "frontend.python.dagcert.source-import-name-collision",
                        format!(
                            "local operation record {:?} collides with an imported record closure",
                            class.name
                        ),
                    );
                }
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
    if local_class_names.is_empty() || functions.is_empty() {
        return failure(
            "frontend.python.dagcert.empty-module",
            "Dagcert operation fragment requires frozen record types and at least one operation",
        );
    }
    let mut local_operation_shapes = BTreeMap::new();
    for function in &functions {
        if imported_operations.contains_key(function.name.as_str())
            || local_operation_shapes
                .insert(
                    function.name.to_string(),
                    operation_shape(
                        function,
                        &markers.operations,
                        &markers.unions,
                        &markers.callables,
                        &records,
                    )?,
                )
                .is_some()
        {
            return failure(
                "frontend.python.dagcert.operation-name-collision",
                format!(
                    "operation name {:?} is declared or imported more than once",
                    function.name
                ),
            );
        }
    }
    // Only already-proved operations from acyclic provider modules are callable here. Local
    // operation calls would require a separate termination/call-graph proof and remain refused.
    let available_operations = imported_operations;
    let mut operations = Vec::new();
    for function in functions {
        verify_operation(
            function,
            &markers.operations,
            &markers.unions,
            &markers.callables,
            &records,
            &available_operations,
            &imported_external_boundaries,
            &markers.external_result_types,
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
    let verification = OperationVerification { operations };
    Ok((
        verification,
        ImportedOperationModule {
            module: module.to_owned(),
            records,
            record_exports: local_class_names,
            operations: local_operation_shapes,
            external_boundaries: BTreeMap::new(),
        },
    ))
}

fn imported_markers(suite: &[ast::Stmt]) -> Result<ImportedMarkers, OperationFailure> {
    let mut operations = BTreeSet::new();
    let mut dataclasses = BTreeSet::new();
    let mut unions = BTreeSet::new();
    let mut callables = BTreeSet::new();
    let mut external_boundaries = BTreeSet::new();
    let mut external_result_types = BTreeMap::new();
    for statement in suite {
        let ast::Stmt::ImportFrom(import) = statement else {
            continue;
        };
        let Some(module) = import.module.as_ref().map(|module| module.as_str()) else {
            continue;
        };
        if module == "dagcert" || module == "dagcert.runtime" {
            for alias in &import.names {
                let imported = alias.name.as_str();
                let local = alias
                    .asname
                    .as_ref()
                    .map_or(imported, |name| name.as_str())
                    .to_owned();
                match imported {
                    "operation" => {
                        operations.insert(local);
                    }
                    "external_boundary" => {
                        external_boundaries.insert(local);
                    }
                    "ExternalSuccess" | "ExternalRaised" | "ExternalTypeViolation" => {
                        external_result_types.insert(local, imported.to_owned());
                    }
                    _ => {}
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
    if (operations.is_empty() && external_boundaries.is_empty())
        || (!operations.is_empty() && dataclasses.is_empty())
    {
        return failure(
            "frontend.python.dagcert.marker-import-missing",
            "operation modules require operation and dataclass imports; external adapters require external_boundary",
        );
    }
    Ok(ImportedMarkers {
        operations,
        dataclasses,
        unions,
        callables,
        external_boundaries,
        external_result_types,
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
    if module == "dagcert" || module == "dagcert.runtime" {
        return import.names.iter().all(|alias| {
            matches!(
                alias.name.as_str(),
                "operation" | "ExternalSuccess" | "ExternalRaised" | "ExternalTypeViolation"
            )
        });
    }
    let allowed = match module {
        "dataclasses" => "dataclass",
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
    Ok(RecordShape {
        fields,
        constructible: true,
    })
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
    if let ast::Expr::Subscript(subscript) = annotation {
        if matches!(subscript.value.as_ref(), ast::Expr::Name(name) if callable_names.contains(name.id.as_str()))
        {
            return callable_annotation_type(&subscript.slice, class_names, callable_names);
        }
        if matches!(subscript.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "tuple")
        {
            return variadic_tuple_annotation_type(&subscript.slice, class_names, callable_names);
        }
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
        "bytes" => Ok(ValueType::Bytes),
        record if class_names.contains(record) => Ok(ValueType::Record(record.to_owned())),
        other => failure(
            "frontend.python.dagcert.type-unsupported",
            format!("unsupported Dagcert operation type {other:?}"),
        ),
    }
}

fn variadic_tuple_annotation_type(
    slice: &ast::Expr,
    class_names: &BTreeSet<String>,
    callable_names: &BTreeSet<String>,
) -> Result<ValueType, OperationFailure> {
    let ast::Expr::Tuple(parts) = slice else {
        return failure(
            "frontend.python.dagcert.tuple-type-unsupported",
            "tuple annotations require one homogeneous element type followed by ellipsis",
        );
    };
    if parts.elts.len() != 2
        || !matches!(
            &parts.elts[1],
            ast::Expr::Constant(value) if matches!(value.value, ast::Constant::Ellipsis)
        )
    {
        return failure(
            "frontend.python.dagcert.tuple-type-unsupported",
            "Dagcert operations currently admit homogeneous variadic tuples such as tuple[str, ...]",
        );
    }
    let element = annotation_type(&parts.elts[0], class_names, callable_names)?;
    if !matches!(
        element,
        ValueType::Int | ValueType::Float | ValueType::Bool | ValueType::Str | ValueType::Bytes
    ) {
        return failure(
            "frontend.python.dagcert.tuple-element-type-unsupported",
            "variadic tuple elements must be primitive immutable values",
        );
    }
    Ok(ValueType::VariadicTuple(Box::new(element)))
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

#[allow(clippy::too_many_arguments)]
fn verify_operation(
    function: &ast::StmtFunctionDef,
    operation_names: &BTreeSet<String>,
    union_names: &BTreeSet<String>,
    callable_names: &BTreeSet<String>,
    records: &BTreeMap<String, RecordShape>,
    operations: &BTreeMap<String, OperationShape>,
    external_boundaries: &BTreeMap<String, ExternalBoundaryShape>,
    external_result_types: &BTreeMap<String, String>,
    callable_bindings: &[ResolvedCallableBinding],
) -> Result<(), OperationFailure> {
    let shape = operation_shape(
        function,
        operation_names,
        union_names,
        callable_names,
        records,
    )?;
    let parameter = &function.args.args[0].def;
    let input_record = shape.input_record;
    let outcome_names = shape.outcomes;
    validate_operation_callable_bindings(
        function.name.as_str(),
        &input_record,
        records,
        callable_bindings,
    )?;
    let context = OperationBodyContext {
        input_name: parameter.arg.as_str(),
        input_record: &input_record,
        outcomes: &outcome_names,
        records,
        operations,
        external_boundaries,
        external_result_types,
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

fn operation_shape(
    function: &ast::StmtFunctionDef,
    operation_names: &BTreeSet<String>,
    union_names: &BTreeSet<String>,
    callable_names: &BTreeSet<String>,
    records: &BTreeMap<String, RecordShape>,
) -> Result<OperationShape, OperationFailure> {
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
    Ok(OperationShape {
        input_record,
        outcomes: outcome_names,
    })
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
    operations: &'a BTreeMap<String, OperationShape>,
    external_boundaries: &'a BTreeMap<String, ExternalBoundaryShape>,
    external_result_types: &'a BTreeMap<String, String>,
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
                    context.operations,
                    context.external_boundaries,
                    context.external_result_types,
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
                    context.operations,
                    context.external_boundaries,
                    context.external_result_types,
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
                    context.operations,
                    context.external_boundaries,
                    context.external_result_types,
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
                let mut else_locals = locals.clone();
                narrow_isinstance_branches(
                    &branch.test,
                    context.records,
                    context.external_result_types,
                    &mut then_locals,
                    &mut else_locals,
                )?;
                let then_returns = verify_statements(&branch.body, context, &mut then_locals)?;
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

fn narrow_isinstance_branches(
    test: &ast::Expr,
    records: &BTreeMap<String, RecordShape>,
    external_result_types: &BTreeMap<String, String>,
    then_locals: &mut BTreeMap<String, ValueType>,
    else_locals: &mut BTreeMap<String, ValueType>,
) -> Result<(), OperationFailure> {
    let ast::Expr::Call(call) = test else {
        return Ok(());
    };
    if !matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "isinstance")
        || call.args.len() != 2
    {
        return Ok(());
    }
    let (ast::Expr::Name(local), ast::Expr::Name(record)) = (&call.args[0], &call.args[1]) else {
        return Ok(());
    };
    if let Some(canonical) = external_result_types.get(record.id.as_str()) {
        let Some(ValueType::ExternalResult {
            success_type,
            variants,
        }) = then_locals.get(local.id.as_str()).cloned()
        else {
            return Ok(());
        };
        if !variants.contains(canonical) {
            return Ok(());
        }
        then_locals.insert(
            local.id.to_string(),
            ValueType::ExternalResult {
                success_type: success_type.clone(),
                variants: BTreeSet::from([canonical.clone()]),
            },
        );
        let mut remaining = variants;
        remaining.remove(canonical);
        if remaining.is_empty() {
            // The source may retain a defensive fallback after exhaustively checking the sealed
            // runtime union. Keep that impossible path conservatively typed instead of requiring
            // users to delete production diagnostics merely to fit the proof frontend.
            return Ok(());
        }
        else_locals.insert(
            local.id.to_string(),
            ValueType::ExternalResult {
                success_type,
                variants: remaining,
            },
        );
        return Ok(());
    }
    if !records.contains_key(record.id.as_str()) {
        return Ok(());
    }
    let Some(ValueType::RecordUnion(outcomes)) = then_locals.get(local.id.as_str()).cloned() else {
        return Ok(());
    };
    if !outcomes.contains(record.id.as_str()) {
        return Ok(());
    }
    then_locals.insert(
        local.id.to_string(),
        ValueType::Record(record.id.to_string()),
    );
    let mut remaining = outcomes;
    remaining.remove(record.id.as_str());
    let remaining_type = match remaining.len() {
        0 => {
            return located_failure(
                "frontend.python.dagcert.isinstance-unreachable-else",
                "isinstance exhausts the only possible record outcome",
                test,
            );
        }
        1 => ValueType::Record(remaining.first().expect("one remaining outcome").clone()),
        _ => ValueType::RecordUnion(remaining),
    };
    else_locals.insert(local.id.to_string(), remaining_type);
    Ok(())
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
        "bytes" => Ok(ValueType::Bytes),
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
            context.operations,
            context.external_boundaries,
            context.external_result_types,
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

#[allow(clippy::too_many_arguments)]
fn infer_operation_expression(
    expression: &ast::Expr,
    input_name: &str,
    input_record: &str,
    records: &BTreeMap<String, RecordShape>,
    operations: &BTreeMap<String, OperationShape>,
    external_boundaries: &BTreeMap<String, ExternalBoundaryShape>,
    external_result_types: &BTreeMap<String, String>,
    operation_name: &str,
    callable_bindings: &[ResolvedCallableBinding],
    locals: &BTreeMap<String, ValueType>,
) -> Result<(ValueType, BTreeSet<String>), OperationFailure> {
    let ast::Expr::Call(call) = expression else {
        return infer_expression(expression, input_name, input_record, records, locals)
            .map(|value_type| (value_type, BTreeSet::new()));
    };
    if matches!(
        call.func.as_ref(),
        ast::Expr::Name(name)
            if records
                .get(name.id.as_str())
                .is_some_and(|shape| shape.constructible)
    ) {
        return infer_expression(expression, input_name, input_record, records, locals)
            .map(|value_type| (value_type, BTreeSet::new()));
    }
    if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "isinstance") {
        if !call.keywords.is_empty() || call.args.len() != 2 {
            return located_failure(
                "frontend.python.dagcert.isinstance-shape-unsupported",
                "isinstance narrowing requires exactly one value and one direct record type",
                expression,
            );
        }
        let tested = infer_expression(&call.args[0], input_name, input_record, records, locals)?;
        let ast::Expr::Name(record_name) = &call.args[1] else {
            return located_failure(
                "frontend.python.dagcert.isinstance-type-unsupported",
                "isinstance narrowing requires a direct source record type",
                &call.args[1],
            );
        };
        if let Some(canonical) = external_result_types.get(record_name.id.as_str()) {
            if !matches!(
                tested,
                ValueType::ExternalResult { ref variants, .. } if variants.contains(canonical)
            ) {
                return located_failure(
                    "frontend.python.dagcert.isinstance-type-mismatch",
                    format!(
                        "isinstance target {:?} is not a possible external-boundary outcome of {tested:?}",
                        record_name.id
                    ),
                    expression,
                );
            }
            return Ok((ValueType::Bool, BTreeSet::new()));
        }
        if !records.contains_key(record_name.id.as_str())
            || !matches!(
                tested,
                ValueType::Record(ref name) if name == record_name.id.as_str()
            ) && !matches!(
                tested,
                ValueType::RecordUnion(ref names) if names.contains(record_name.id.as_str())
            )
        {
            return located_failure(
                "frontend.python.dagcert.isinstance-type-mismatch",
                format!(
                    "isinstance target {:?} is not a possible source-record outcome of {tested:?}",
                    record_name.id
                ),
                expression,
            );
        }
        return Ok((ValueType::Bool, BTreeSet::new()));
    }
    if let ast::Expr::Name(callee) = call.func.as_ref()
        && let Some(shape) = external_boundaries.get(callee.id.as_str())
    {
        if !call.keywords.is_empty() || call.args.len() != shape.parameters.len() {
            return located_failure(
                "frontend.python.dagcert.external-boundary-call-shape-mismatch",
                format!(
                    "external boundary {:?} ({:?}) requires {} positional arguments",
                    callee.id,
                    shape.boundary_id,
                    shape.parameters.len(),
                ),
                expression,
            );
        }
        for (argument, expected) in call.args.iter().zip(&shape.parameters) {
            let (actual, raised) = infer_operation_expression(
                argument,
                input_name,
                input_record,
                records,
                operations,
                external_boundaries,
                external_result_types,
                operation_name,
                callable_bindings,
                locals,
            )?;
            if !raised.is_empty() || &actual != expected {
                return located_failure(
                    "frontend.python.dagcert.external-boundary-call-input-type-mismatch",
                    format!(
                        "external boundary {:?} expects {expected:?}, received {actual:?}",
                        callee.id
                    ),
                    argument,
                );
            }
        }
        return Ok((
            ValueType::ExternalResult {
                success_type: Box::new(shape.success_type.clone()),
                variants: BTreeSet::from([
                    "ExternalSuccess".to_owned(),
                    "ExternalRaised".to_owned(),
                    "ExternalTypeViolation".to_owned(),
                ]),
            },
            BTreeSet::new(),
        ));
    }
    if let ast::Expr::Name(callee) = call.func.as_ref()
        && let Some(shape) = operations.get(callee.id.as_str())
    {
        if callee.id.as_str() == operation_name {
            return located_failure(
                "frontend.python.dagcert.operation-recursion-unsupported",
                "Dagcert operations may not call themselves recursively",
                expression,
            );
        }
        if !call.keywords.is_empty() || call.args.len() != 1 {
            return located_failure(
                "frontend.python.dagcert.operation-call-shape-mismatch",
                format!(
                    "operation {:?} requires exactly one positional input",
                    callee.id
                ),
                expression,
            );
        }
        let (actual, raised) = infer_operation_expression(
            &call.args[0],
            input_name,
            input_record,
            records,
            operations,
            external_boundaries,
            external_result_types,
            operation_name,
            callable_bindings,
            locals,
        )?;
        let expected = ValueType::Record(shape.input_record.clone());
        if actual != expected {
            return located_failure(
                "frontend.python.dagcert.operation-call-input-type-mismatch",
                format!(
                    "operation {:?} expects {expected:?}, received {actual:?}",
                    callee.id
                ),
                &call.args[0],
            );
        }
        let value_type = if shape.outcomes.len() == 1 {
            ValueType::Record(
                shape
                    .outcomes
                    .first()
                    .expect("one-outcome operation")
                    .clone(),
            )
        } else {
            ValueType::RecordUnion(shape.outcomes.clone())
        };
        return Ok((value_type, raised));
    }
    if let Some(value_type) =
        infer_total_string_method_call(call, expression, input_name, input_record, records, locals)?
    {
        return Ok((value_type, BTreeSet::new()));
    }
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

fn infer_total_string_method_call(
    call: &ast::ExprCall,
    expression: &ast::Expr,
    input_name: &str,
    input_record: &str,
    records: &BTreeMap<String, RecordShape>,
    locals: &BTreeMap<String, ValueType>,
) -> Result<Option<ValueType>, OperationFailure> {
    let ast::Expr::Attribute(attribute) = call.func.as_ref() else {
        return Ok(None);
    };
    let receiver = infer_expression(&attribute.value, input_name, input_record, records, locals)?;
    if receiver != ValueType::Str {
        return Ok(None);
    }
    if !call.keywords.is_empty() {
        return located_failure(
            "frontend.python.dagcert.string-method-keyword-unsupported",
            "proved string methods currently require positional arguments",
            expression,
        );
    }
    match attribute.attr.as_str() {
        "strip" | "lower" if call.args.is_empty() => Ok(Some(ValueType::Str)),
        "startswith" if call.args.len() == 1 => {
            let prefix =
                infer_expression(&call.args[0], input_name, input_record, records, locals)?;
            if prefix != ValueType::Str {
                return located_failure(
                    "frontend.python.dagcert.string-method-argument-type-mismatch",
                    "str.startswith requires one str prefix",
                    &call.args[0],
                );
            }
            Ok(Some(ValueType::Bool))
        }
        "split" if call.args.is_empty() => Ok(Some(ValueType::StringSplitResult)),
        "split" if matches!(call.args.len(), 1 | 2) => {
            let separator =
                infer_expression(&call.args[0], input_name, input_record, records, locals)?;
            if separator != ValueType::Str {
                return located_failure(
                    "frontend.python.dagcert.string-method-argument-type-mismatch",
                    "str.split separator must be str",
                    &call.args[0],
                );
            }
            if !matches!(
                &call.args[0],
                ast::Expr::Constant(value)
                    if matches!(&value.value, ast::Constant::Str(text) if !text.is_empty())
            ) {
                return located_failure(
                    "frontend.python.dagcert.string-split-separator-may-be-empty",
                    "str.split with an explicit separator is total only when the separator is a nonempty literal",
                    &call.args[0],
                );
            }
            if call.args.len() == 2
                && infer_expression(&call.args[1], input_name, input_record, records, locals)?
                    != ValueType::Int
            {
                return located_failure(
                    "frontend.python.dagcert.string-method-argument-type-mismatch",
                    "str.split maxsplit must be int",
                    &call.args[1],
                );
            }
            Ok(Some(ValueType::StringSplitResult))
        }
        method => located_failure(
            "frontend.python.dagcert.string-method-unsupported",
            format!("string method {method:?} or its argument shape is not proved total"),
            expression,
        ),
    }
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
            if name.id.as_str() == input_name {
                return Ok(ValueType::Record(input_record.to_owned()));
            }
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
            ast::Constant::Bytes(_) => Ok(ValueType::Bytes),
            _ => unsupported_expression(expression),
        },
        ast::Expr::Attribute(attribute) => {
            let receiver =
                infer_expression(&attribute.value, input_name, input_record, records, locals)?;
            if let ValueType::ExternalResult {
                success_type,
                variants,
            } = receiver
            {
                if variants == BTreeSet::from(["ExternalSuccess".to_owned()])
                    && attribute.attr.as_str() == "value"
                {
                    return Ok(*success_type);
                }
                if variants.len() == 1
                    && variants.iter().all(|variant| {
                        matches!(variant.as_str(), "ExternalRaised" | "ExternalTypeViolation")
                    })
                    && matches!(
                        attribute.attr.as_str(),
                        "boundary_id"
                            | "exception_type"
                            | "message"
                            | "expected_type"
                            | "observed_type"
                    )
                {
                    return Ok(ValueType::Str);
                }
                return located_failure(
                    "frontend.python.dagcert.external-boundary-outcome-not-narrowed",
                    "external-boundary result fields require an exhaustive isinstance branch",
                    expression,
                );
            }
            let ValueType::Record(record) = receiver else {
                return failure(
                    "frontend.python.dagcert.field-receiver-unsupported",
                    "operation field reads require a source-owned frozen record receiver",
                );
            };
            records[&record]
                .fields
                .iter()
                .find(|(field, _)| field == attribute.attr.as_str())
                .map(|(_, field_type)| field_type.clone())
                .ok_or_else(|| OperationFailure {
                    code: "frontend.python.dagcert.field-unknown",
                    message: format!("record {record:?} has no field {:?}", attribute.attr),
                    byte_offset: Some(attribute.range.start().into()),
                })
        }
        ast::Expr::Call(call) => {
            if let Some(value_type) = infer_total_string_method_call(
                call,
                expression,
                input_name,
                input_record,
                records,
                locals,
            )? {
                return Ok(value_type);
            }
            let ast::Expr::Name(constructor) = call.func.as_ref() else {
                return unsupported_expression(expression);
            };
            let Some(shape) = records.get(constructor.id.as_str()) else {
                return unsupported_expression(expression);
            };
            if !shape.constructible {
                return located_failure(
                    "frontend.python.dagcert.source-import-record-not-imported",
                    format!(
                        "record {:?} is present only as a transitive field type and cannot be constructed without importing it",
                        constructor.id
                    ),
                    expression,
                );
            }
            if !call.keywords.is_empty() || call.args.len() != shape.fields.len() {
                return located_failure(
                    "frontend.python.dagcert.record-constructor-shape-mismatch",
                    format!(
                        "frozen record {:?} requires exactly {} positional fields",
                        constructor.id,
                        shape.fields.len()
                    ),
                    expression,
                );
            }
            for ((field, expected), argument) in shape.fields.iter().zip(&call.args) {
                let actual = infer_expression(argument, input_name, input_record, records, locals)?;
                if &actual != expected {
                    return located_failure(
                        "frontend.python.dagcert.record-constructor-field-type-mismatch",
                        format!(
                            "frozen record {:?} field {field:?} expects {expected:?}, received {actual:?}",
                            constructor.id
                        ),
                        argument,
                    );
                }
            }
            Ok(ValueType::Record(constructor.id.to_string()))
        }
        ast::Expr::Subscript(subscript) => {
            let collection =
                infer_expression(&subscript.value, input_name, input_record, records, locals)?;
            if collection == ValueType::StringSplitResult
                && matches!(
                    subscript.slice.as_ref(),
                    ast::Expr::Constant(value)
                        if matches!(&value.value, ast::Constant::Int(index) if index.to_string() == "0")
                )
            {
                Ok(ValueType::Str)
            } else {
                located_failure(
                    "frontend.python.dagcert.partial-or-unsupported-subscript",
                    "only index zero of a proved str.split result is currently total",
                    expression,
                )
            }
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
                ast::UnaryOp::Not
                    if matches!(operand, ValueType::Bool | ValueType::Str | ValueType::Bytes) =>
                {
                    Ok(ValueType::Bool)
                }
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
            if matches!(comparison.ops[0], ast::CmpOp::In | ast::CmpOp::NotIn) {
                return match right {
                    ValueType::Str if left == ValueType::Str => Ok(ValueType::Bool),
                    ValueType::VariadicTuple(element) if left == *element => Ok(ValueType::Bool),
                    ValueType::VariadicTuple(element) => failure(
                        "frontend.python.dagcert.membership-type-mismatch",
                        format!("tuple membership value has type {left:?}, expected {element:?}"),
                    ),
                    _ => unsupported_expression(expression),
                };
            }
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
    fn proves_history_selection_with_variadic_string_tuple_membership() {
        let source = "from dataclasses import dataclass\nfrom typing import Union\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass HistoryImageChoice:\n    ok: bool\n    image_key: str\n    candidate_keys: tuple[str, ...]\n    previous_key: str\n    error_type: str\n    message: str\n\n@dataclass(frozen=True)\nclass SeenImageSelected:\n    image_key: str\n\n@dataclass(frozen=True)\nclass SeenImageSelectionFailed:\n    error_type: str\n    message: str\n\n@operation\ndef classify_seen_image_choice(request: HistoryImageChoice) -> Union[SeenImageSelected, SeenImageSelectionFailed]:\n    if not request.ok:\n        return SeenImageSelectionFailed(request.error_type, request.message)\n    if request.image_key == '':\n        return SeenImageSelectionFailed('ValueError', 'empty')\n    if request.image_key not in request.candidate_keys:\n        return SeenImageSelectionFailed('ValueError', 'outside candidates')\n    if request.previous_key != '' and request.image_key == request.previous_key:\n        return SeenImageSelectionFailed('ValueError', 'repeated')\n    return SeenImageSelected(request.image_key)\n";
        let result = verify_operation_module(
            source,
            "history.py",
            &["classify_seen_image_choice".to_owned()],
        )
        .unwrap();
        assert_eq!(result.operations, ["classify_seen_image_choice"]);
    }

    #[test]
    fn proves_bytes_payload_propagation_and_total_truthiness() {
        let source = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Payload:\n    ok: bool\n    content: bytes\n    label: str\n\n@dataclass(frozen=True)\nclass Ready:\n    content: bytes\n\n@dataclass(frozen=True)\nclass Rejected:\n    reason: str\n\n@operation\ndef classify(request: Payload) -> Ready | Rejected:\n    if not request.ok:\n        return Rejected('provider failed')\n    if not request.content:\n        return Rejected('empty bytes')\n    if not request.label:\n        return Rejected('empty label')\n    return Ready(request.content)\n";
        let result =
            verify_operation_module(source, "payload.py", &["classify".to_owned()]).unwrap();
        assert_eq!(result.operations, ["classify"]);
    }

    #[test]
    fn proves_total_string_normalization_methods_and_safe_split_head() {
        let source = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass RawReference:\n    value: str\n\n@dataclass(frozen=True)\nclass LocalReference:\n    value: str\n\n@dataclass(frozen=True)\nclass Rejected:\n    reason: str\n\n@operation\ndef validate(request: RawReference) -> LocalReference | Rejected:\n    normalized = request.value.strip()\n    if not normalized:\n        return Rejected('empty')\n    lower_value = normalized.lower()\n    if '://' in normalized or lower_value.startswith('data:') or lower_value.startswith('file:') or normalized.startswith('//'):\n        return Rejected('remote')\n    path = normalized.split('#', 1)[0].split('?', 1)[0]\n    if not path:\n        return Rejected('no path')\n    return LocalReference(path)\n";
        let result =
            verify_operation_module(source, "references.py", &["validate".to_owned()]).unwrap();
        assert_eq!(result.operations, ["validate"]);
    }

    #[test]
    fn refuses_possibly_empty_explicit_string_split_separator() {
        let source = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Request:\n    value: str\n    separator: str\n\n@dataclass(frozen=True)\nclass Result:\n    value: str\n\n@operation\ndef split_head(request: Request) -> Result:\n    head = request.value.split(request.separator, 1)[0]\n    return Result(head)\n";
        let error = verify_operation_module(source, "references.py", &["split_head".to_owned()])
            .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.dagcert.string-split-separator-may-be-empty"
        );
    }

    #[test]
    fn proves_nested_projection_from_source_owned_frozen_records() {
        let source = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass ImageRef:\n    value: str\n\n@dataclass(frozen=True)\nclass Request:\n    image_ref: str\n\n@dataclass(frozen=True)\nclass Completed:\n    image_ref: str\n\n@operation\ndef project(request: Request) -> Completed:\n    image = ImageRef(request.image_ref)\n    return Completed(image.value)\n";
        let result =
            verify_operation_module(source, "projection.py", &["project".to_owned()]).unwrap();
        assert_eq!(result.operations, ["project"]);
    }

    #[test]
    fn refuses_variadic_tuple_membership_with_wrong_element_type() {
        let source = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Request:\n    candidate_keys: tuple[str, ...]\n    candidate: int\n\n@dataclass(frozen=True)\nclass Completed:\n    present: bool\n\n@operation\ndef check(request: Request) -> Completed:\n    return Completed(request.candidate in request.candidate_keys)\n";
        let error =
            verify_operation_module(source, "history.py", &["check".to_owned()]).unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.dagcert.membership-type-mismatch"
        );
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

    #[test]
    fn proves_one_operation_with_local_work_around_an_imported_external_boundary() {
        let adapter = "from dagcert.runtime import external_boundary\n\n@external_boundary('stdlib.text.normalize')\ndef normalize_external(value: str) -> str:\n    return value\n";
        let imported = export_external_boundary_module(
            adapter,
            "adapter.py",
            "adapter",
            &["normalize_external".to_owned()],
        )
        .unwrap();
        let source = "from dataclasses import dataclass\nfrom dagcert.runtime import ExternalRaised, ExternalSuccess, ExternalTypeViolation, operation\nfrom adapter import normalize_external\n\n@dataclass(frozen=True)\nclass Request:\n    value: str\n\n@dataclass(frozen=True)\nclass Completed:\n    value: str\n\n@dataclass(frozen=True)\nclass Failed:\n    message: str\n\n@operation\ndef complete(request: Request) -> Completed | Failed:\n    prepared = request.value.strip()\n    result = normalize_external(prepared)\n    if isinstance(result, ExternalSuccess):\n        return Completed(result.value.lower())\n    if isinstance(result, ExternalRaised):\n        return Failed(result.message)\n    return Failed(result.message)\n";
        let (verification, _) = verify_and_export_operation_module_with_imports(
            source,
            "app.py",
            "app",
            &["complete".to_owned()],
            &[],
            &[imported],
        )
        .unwrap();
        assert_eq!(verification.operations, ["complete"]);
    }
}
