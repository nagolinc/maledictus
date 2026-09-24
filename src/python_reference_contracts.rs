//! Closed nominal-reference contracts for source classes, null, identity, and typed calls.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_parser::{Parse, ast};
use serde::{Deserialize, Serialize};

use crate::python_contracts::ContractFailure;
use crate::solver::discharge;
use crate::vc::{Obligation, ObligationExpectation, ObligationResult, Sort, Term};

const PINNED_NOMINAL_TYPES: &[(&str, &str)] = &[
    ("nagini_contracts.adt", "ADT"),
    ("nagini_contracts.lock", "Lock"),
    ("nagini_contracts.thread", "Thread"),
];

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ReferenceContractVerification {
    pub schema: String,
    pub path: String,
    pub functions: Vec<String>,
    pub obligations: Vec<ObligationResult>,
    pub passed: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ReferenceType {
    NonNull(String),
    Optional(String),
    Null,
}

impl ReferenceType {
    fn class(&self) -> Option<&str> {
        match self {
            Self::NonNull(class) | Self::Optional(class) => Some(class),
            Self::Null => None,
        }
    }

    fn is_optional(&self) -> bool {
        matches!(self, Self::Optional(_) | Self::Null)
    }
}

#[derive(Clone, Debug)]
struct FunctionSummary {
    parameters: Vec<(String, ReferenceType)>,
    return_type: Option<ReferenceType>,
    pure_bool_result: Option<ast::Expr>,
}

#[derive(Clone, Debug)]
pub struct ImportedReferenceContractModule {
    module: String,
    classes: BTreeMap<String, String>,
    builtin_identity_equality_classes: BTreeSet<String>,
    functions: BTreeMap<String, FunctionSummary>,
}

impl ImportedReferenceContractModule {
    pub fn module(&self) -> &str {
        &self.module
    }

    pub fn function_names(&self) -> Vec<String> {
        self.functions.keys().cloned().collect()
    }

    pub fn type_names(&self) -> Vec<String> {
        self.classes.values().cloned().collect()
    }
}

#[derive(Clone, Debug)]
struct ReferenceValue {
    term: Term,
    ty: ReferenceType,
}

pub fn verify_reference_module(
    source: &str,
    path: &str,
    requested_symbols: &[String],
) -> Result<ReferenceContractVerification, ContractFailure> {
    verify_reference_module_with_imports(source, path, requested_symbols, &[])
}

pub fn verify_reference_module_with_imports(
    source: &str,
    path: &str,
    requested_symbols: &[String],
    imported_modules: &[ImportedReferenceContractModule],
) -> Result<ReferenceContractVerification, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    validate_reference_module_ownership(&suite)?;
    let mut class_names = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ClassDef(class) => Some((class.name.to_string(), class.name.to_string())),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let mut builtin_identity_equality_classes =
        class_names.values().cloned().collect::<BTreeSet<_>>();
    let imported_by_name = imported_modules
        .iter()
        .map(|module| (module.module.as_str(), module))
        .collect::<BTreeMap<_, _>>();
    let mut imported_functions = BTreeMap::new();
    let mut used_modules = BTreeSet::new();
    let mut declarations = Vec::new();
    for statement in &suite {
        match statement {
            statement if is_inert_string_statement(statement) => {
                // Literal string expression statements are total and have no verification-
                // relevant effect. This covers module docstrings without admitting executable
                // module calls or other arbitrary expression statements.
            }
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import.module.as_ref().is_some_and(|module| {
                        matches!(module.as_str(), "nagini_contracts.contracts" | "typing")
                    }) => {}
            ast::Stmt::ImportFrom(import) if is_pinned_nominal_type_module(import) => {
                import_pinned_nominal_types(import, &mut class_names)?;
            }
            ast::Stmt::ImportFrom(import) if is_unmodeled_effect_wildcard_import(import) => {
                return failure(
                    "frontend.python.references.effect-wildcard-import-unsupported",
                    format!(
                        "nominal-reference verification cannot import effect-bearing module {:?} by wildcard",
                        import.module
                    ),
                );
            }
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import
                        .module
                        .as_ref()
                        .is_some_and(|module| imported_by_name.contains_key(module.as_str())) =>
            {
                let module_name = import
                    .module
                    .as_ref()
                    .expect("import module guard")
                    .as_str();
                let imported = imported_by_name[module_name];
                used_modules.insert(module_name.to_owned());
                builtin_identity_equality_classes
                    .extend(imported.builtin_identity_equality_classes.iter().cloned());
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        return failure(
                            "frontend.python.references.star-import-unsupported",
                            "nominal reference contracts require explicit imports",
                        );
                    }
                    let imported_name = alias.name.as_str();
                    let local_name = alias
                        .asname
                        .as_ref()
                        .map_or(imported_name, |name| name.as_str());
                    if let Some(summary) = imported.functions.get(imported_name) {
                        if imported_functions
                            .insert(local_name.to_owned(), summary.clone())
                            .is_some()
                        {
                            return failure(
                                "frontend.python.references.import-collision",
                                format!("duplicate imported function name {local_name:?}"),
                            );
                        }
                    } else if let Some(identity) = imported.classes.get(imported_name) {
                        if local_name != imported_name {
                            return failure(
                                "frontend.python.references.type-alias-unsupported",
                                "imported nominal type aliases require explicit identity mapping",
                            );
                        }
                        if class_names
                            .insert(local_name.to_owned(), identity.clone())
                            .is_some()
                        {
                            return failure(
                                "frontend.python.references.type-collision",
                                format!("nominal type name {local_name:?} is ambiguous"),
                            );
                        }
                    } else {
                        return failure(
                            "frontend.python.references.import-symbol-missing",
                            format!(
                                "reference contract module {module_name:?} has no symbol {imported_name:?}"
                            ),
                        );
                    }
                }
            }
            ast::Stmt::ClassDef(class) => validate_nominal_class_declaration(class)?,
            ast::Stmt::FunctionDef(function) => declarations.push(function),
            ast::Stmt::Assign(_) | ast::Stmt::AnnAssign(_) | ast::Stmt::AugAssign(_) => {
                return failure(
                    "frontend.python.references.module-runtime-state-unsupported",
                    "nominal-reference verification does not execute or track module assignments",
                );
            }
            _ => {
                return failure(
                    "frontend.python.references.module-statement-unsupported",
                    format!("unsupported nominal-reference module statement {statement:?}"),
                );
            }
        }
    }
    for module in imported_by_name.keys() {
        if !used_modules.contains(*module) {
            return failure(
                "frontend.python.references.module-unused",
                format!("reference contract module {module:?} is not imported by {path:?}"),
            );
        }
    }
    if class_names.is_empty() || declarations.is_empty() {
        return failure(
            "frontend.python.references.empty-module",
            "nominal-reference fragment requires source classes and functions",
        );
    }
    let mut summaries = declarations
        .iter()
        .map(|function| {
            Ok((
                function.name.to_string(),
                build_summary(function, &class_names)?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, ContractFailure>>()?;
    for (name, summary) in imported_functions {
        if summaries.insert(name.clone(), summary).is_some() {
            return failure(
                "frontend.python.references.import-collision",
                format!("imported function shadows source function {name:?}"),
            );
        }
    }
    let mut functions = Vec::new();
    let mut obligations = Vec::new();
    for function in declarations {
        functions.push(function.name.to_string());
        obligations.extend(lower_function(
            function,
            &summaries,
            &builtin_identity_equality_classes,
            source,
            path,
        )?);
    }
    for symbol in requested_symbols {
        if !functions.contains(symbol) {
            return failure(
                "frontend.python.symbol.missing",
                format!("requested symbol {symbol:?} is not a verified reference function"),
            );
        }
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
    Ok(ReferenceContractVerification {
        schema: "maledictus-python-nominal-reference-verification/v1".to_owned(),
        path: path.to_owned(),
        functions,
        obligations,
        passed,
    })
}

pub(crate) fn validate_reference_source_ownership(
    source: &str,
    path: &str,
) -> Result<(), ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    validate_reference_module_ownership(&suite)
}

fn validate_reference_module_ownership(suite: &ast::Suite) -> Result<(), ContractFailure> {
    if suite.iter().any(|statement| {
        matches!(statement,
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import.module.as_ref().is_some_and(|module|
                        module.as_str() == "nagini_contracts.io_builtins"))
    }) {
        return failure(
            "frontend.python.references.io-semantics-unsupported",
            "nominal-reference verification does not own linear IO runtime semantics",
        );
    }
    Ok(())
}

fn validate_nominal_class_declaration(class: &ast::StmtClassDef) -> Result<(), ContractFailure> {
    let executable_body = class
        .body
        .iter()
        .filter(|statement| !is_inert_string_statement(statement))
        .collect::<Vec<_>>();
    let marker = matches!(executable_body.as_slice(), [ast::Stmt::Pass(_)]);
    let passive_record = matches!(
        executable_body.as_slice(),
        [ast::Stmt::FunctionDef(constructor)] if is_passive_record_constructor(constructor)
    );
    if !class.bases.is_empty() || !class.keywords.is_empty() {
        return failure(
            "frontend.python.references.inherited-class-semantics-unsupported",
            format!(
                "reference class {:?} requires unmodeled inheritance or metaclass semantics",
                class.name
            ),
        );
    }
    if !passive_record
        && matches!(
            executable_body.as_slice(),
            [ast::Stmt::FunctionDef(constructor)] if constructor.name.as_str() == "__init__"
        )
    {
        return failure(
            "frontend.python.references.constructor-semantics-unsupported",
            format!(
                "reference class {:?} has constructor behavior beyond passive field initialization",
                class.name
            ),
        );
    }
    if !class.decorator_list.is_empty()
        || !class.type_params.is_empty()
        || (!marker && !passive_record)
    {
        return failure(
            "frontend.python.references.class-unsupported",
            format!(
                "reference class {:?} must be a non-inheriting marker or passive constructor-only record",
                class.name
            ),
        );
    }
    Ok(())
}

fn is_passive_record_constructor(function: &ast::StmtFunctionDef) -> bool {
    if function.name.as_str() != "__init__"
        || !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || function.args.vararg.is_some()
        || function.args.kwarg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || !matches!(
            function.returns.as_deref(),
            Some(ast::Expr::Constant(value)) if value.value == ast::Constant::None
        )
    {
        return false;
    }
    let parameters = function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .collect::<Vec<_>>();
    let Some((receiver, values)) = parameters.split_first() else {
        return false;
    };
    if receiver.def.arg.as_str() != "self"
        || receiver.def.annotation.is_some()
        || receiver.default.is_some()
        || values.is_empty()
        || values.iter().any(|parameter| {
            parameter.default.is_some()
                || !matches!(
                    parameter.def.annotation.as_deref(),
                    Some(ast::Expr::Name(_))
                )
        })
    {
        return false;
    }
    let value_names = values
        .iter()
        .map(|parameter| parameter.def.arg.as_str())
        .collect::<BTreeSet<_>>();
    let body = function
        .body
        .iter()
        .filter(|statement| !is_inert_string_statement(statement))
        .collect::<Vec<_>>();
    if body.len() != values.len() {
        return false;
    }
    let mut fields = BTreeSet::new();
    let mut assigned_values = BTreeSet::new();
    body.into_iter().all(|statement| {
        let ast::Stmt::Assign(assignment) = statement else {
            return false;
        };
        let ([ast::Expr::Attribute(target)], ast::Expr::Name(value)) =
            (assignment.targets.as_slice(), assignment.value.as_ref())
        else {
            return false;
        };
        matches!(target.value.as_ref(), ast::Expr::Name(receiver) if receiver.id.as_str() == "self")
            && value_names.contains(value.id.as_str())
            && fields.insert(target.attr.as_str())
            && assigned_values.insert(value.id.as_str())
    })
}

pub fn parse_external_reference_contract_module(
    source: &str,
    path: &str,
    module: &str,
) -> Result<ImportedReferenceContractModule, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.references.external-parse-error",
        message: error.to_string(),
    })?;
    let classes = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ClassDef(class) => {
                Some((class.name.to_string(), format!("{module}.{}", class.name)))
            }
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let mut functions = BTreeMap::new();
    for statement in &suite {
        match statement {
            statement if is_inert_string_statement(statement) => {
                // Checked external contracts may document the module without changing its
                // exported nominal summaries.
            }
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import.module.as_ref().is_some_and(|module| {
                        matches!(module.as_str(), "nagini_contracts.contracts" | "typing")
                    }) => {}
            ast::Stmt::ClassDef(class) => validate_nominal_class_declaration(class)?,
            ast::Stmt::FunctionDef(function) => {
                if !matches!(
                    function.decorator_list.as_slice(),
                    [ast::Expr::Name(name)] if name.id.as_str() == "ContractOnly"
                ) {
                    return failure(
                        "frontend.python.references.external-decorator-required",
                        format!(
                            "external reference function {:?} requires exactly @ContractOnly",
                            function.name
                        ),
                    );
                }
                let executable_body = function
                    .body
                    .iter()
                    .filter(|statement| !is_inert_string_statement(statement))
                    .collect::<Vec<_>>();
                let contract_only_body = matches!(executable_body.as_slice(), [ast::Stmt::Pass(_)])
                    || matches!(
                        executable_body.as_slice(),
                        [ast::Stmt::Expr(statement)]
                            if matches!(statement.value.as_ref(), ast::Expr::Constant(constant) if constant.value == ast::Constant::Ellipsis)
                    );
                if !contract_only_body {
                    return failure(
                        "frontend.python.references.external-body-not-contract-only",
                        format!(
                            "external reference function {:?} must end in exactly pass or ellipsis",
                            function.name
                        ),
                    );
                }
                let summary = build_external_summary(function, &classes)?;
                if functions
                    .insert(function.name.to_string(), summary)
                    .is_some()
                {
                    return failure(
                        "frontend.python.references.external-duplicate-function",
                        format!("duplicate external reference function {:?}", function.name),
                    );
                }
            }
            _ => {
                return failure(
                    "frontend.python.references.external-module-statement-unsupported",
                    format!("unsupported external reference contract statement {statement:?}"),
                );
            }
        }
    }
    if classes.is_empty() || functions.is_empty() {
        return failure(
            "frontend.python.references.external-empty-module",
            "external reference contract requires at least one nominal class and function",
        );
    }
    Ok(ImportedReferenceContractModule {
        module: module.to_owned(),
        classes,
        builtin_identity_equality_classes: BTreeSet::new(),
        functions,
    })
}

pub fn verify_and_export_source_reference_module(
    source: &str,
    path: &str,
    module: &str,
    imported_modules: &[ImportedReferenceContractModule],
) -> Result<
    (
        ReferenceContractVerification,
        ImportedReferenceContractModule,
    ),
    ContractFailure,
> {
    let verification = verify_reference_module_with_imports(source, path, &[], imported_modules)?;
    if !verification.passed {
        return failure(
            "frontend.python.references.source-module-refuted",
            format!(
                "source reference module {module:?} cannot export summaries because an obligation was refuted"
            ),
        );
    }
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    let imported_by_name = imported_modules
        .iter()
        .map(|imported| (imported.module.as_str(), imported))
        .collect::<BTreeMap<_, _>>();
    let mut visible_classes = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ClassDef(class) => {
                Some((class.name.to_string(), format!("{module}.{}", class.name)))
            }
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    for statement in &suite {
        let ast::Stmt::ImportFrom(import) = statement else {
            continue;
        };
        if is_pinned_nominal_type_module(import) {
            import_pinned_nominal_types(import, &mut visible_classes)?;
            continue;
        }
        let Some(module_name) = import.module.as_ref() else {
            continue;
        };
        let Some(imported) = imported_by_name.get(module_name.as_str()) else {
            continue;
        };
        for alias in &import.names {
            let imported_name = alias.name.as_str();
            if let Some(identity) = imported.classes.get(imported_name) {
                if alias.asname.is_some() {
                    return failure(
                        "frontend.python.references.type-alias-unsupported",
                        "imported nominal type aliases require explicit identity mapping",
                    );
                }
                if visible_classes
                    .insert(imported_name.to_owned(), identity.clone())
                    .is_some()
                {
                    return failure(
                        "frontend.python.references.type-collision",
                        format!("nominal type name {imported_name:?} is ambiguous"),
                    );
                }
            }
        }
    }
    let local_classes = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ClassDef(class) => {
                Some((class.name.to_string(), format!("{module}.{}", class.name)))
            }
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let functions = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => Some(function),
            _ => None,
        })
        .map(|function| {
            Ok((
                function.name.to_string(),
                build_summary(function, &visible_classes)?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, ContractFailure>>()?;
    if functions.is_empty() {
        return failure(
            "frontend.python.references.source-module-empty",
            format!("source reference module {module:?} exports no verified functions"),
        );
    }
    let mut exported_builtin_identity_equality_classes =
        local_classes.values().cloned().collect::<BTreeSet<_>>();
    for imported in imported_modules {
        exported_builtin_identity_equality_classes
            .extend(imported.builtin_identity_equality_classes.iter().cloned());
    }
    Ok((
        verification,
        ImportedReferenceContractModule {
            module: module.to_owned(),
            builtin_identity_equality_classes: exported_builtin_identity_equality_classes,
            classes: local_classes,
            functions,
        },
    ))
}

fn is_pinned_nominal_type_module(import: &ast::StmtImportFrom) -> bool {
    import.level.is_none_or(|level| level == 0_u32)
        && import.module.as_ref().is_some_and(|module| {
            PINNED_NOMINAL_TYPES
                .iter()
                .any(|(known_module, _)| module.as_str() == *known_module)
        })
}

fn is_unmodeled_effect_wildcard_import(import: &ast::StmtImportFrom) -> bool {
    import.level.is_none_or(|level| level == 0_u32)
        && import.module.as_ref().is_some_and(|module| {
            matches!(
                module.as_str(),
                "nagini_contracts.io_contracts" | "nagini_contracts.obligations"
            )
        })
        && import.names.iter().any(|alias| alias.name.as_str() == "*")
}

fn import_pinned_nominal_types(
    import: &ast::StmtImportFrom,
    classes: &mut BTreeMap<String, String>,
) -> Result<(), ContractFailure> {
    let module = import
        .module
        .as_ref()
        .expect("pinned nominal import guard provides a module")
        .as_str();
    for alias in &import.names {
        let imported_name = alias.name.as_str();
        if imported_name == "*" {
            return failure(
                "frontend.python.references.pinned-nominal-star-import-unsupported",
                format!("nominal types from {module:?} require explicit imports"),
            );
        }
        if !PINNED_NOMINAL_TYPES
            .iter()
            .any(|(known_module, known_type)| {
                module == *known_module && imported_name == *known_type
            })
        {
            return failure(
                "frontend.python.references.pinned-nominal-symbol-unsupported",
                format!(
                    "module {module:?} does not provide modeled nominal type {imported_name:?}"
                ),
            );
        }
        let local_name = alias
            .asname
            .as_ref()
            .map_or(imported_name, |name| name.as_str());
        let identity = format!("{module}.{imported_name}");
        if classes.insert(local_name.to_owned(), identity).is_some() {
            return failure(
                "frontend.python.references.type-collision",
                format!("nominal type name {local_name:?} is ambiguous"),
            );
        }
    }
    Ok(())
}

fn build_external_summary(
    function: &ast::StmtFunctionDef,
    classes: &BTreeMap<String, String>,
) -> Result<FunctionSummary, ContractFailure> {
    if !function.type_params.is_empty()
        || function.args.vararg.is_some()
        || function.args.kwarg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function
            .args
            .posonlyargs
            .iter()
            .chain(function.args.args.iter())
            .any(|argument| argument.default.is_some())
    {
        return failure(
            "frontend.python.references.external-signature-unsupported",
            format!(
                "external reference function {:?} has an unsupported signature",
                function.name
            ),
        );
    }
    let parameters = function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .map(|argument| {
            Ok((
                argument.def.arg.to_string(),
                reference_annotation(argument.def.annotation.as_deref(), classes)?,
            ))
        })
        .collect::<Result<Vec<_>, ContractFailure>>()?;
    let return_type = match function.returns.as_deref() {
        Some(ast::Expr::Constant(value)) if value.value == ast::Constant::None => None,
        annotation => Some(reference_annotation(annotation, classes)?),
    };
    Ok(FunctionSummary {
        parameters,
        return_type,
        pure_bool_result: None,
    })
}

fn build_summary(
    function: &ast::StmtFunctionDef,
    classes: &BTreeMap<String, String>,
) -> Result<FunctionSummary, ContractFailure> {
    let pure_bool = matches!(
        function.decorator_list.as_slice(),
        [ast::Expr::Name(name)] if name.id.as_str() == "Pure"
    ) && matches!(
        function.returns.as_deref(),
        Some(ast::Expr::Name(name)) if name.id.as_str() == "bool"
    );
    if (!function.decorator_list.is_empty() && !pure_bool)
        || !function.type_params.is_empty()
        || function.args.vararg.is_some()
        || function.args.kwarg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function
            .args
            .posonlyargs
            .iter()
            .chain(function.args.args.iter())
            .any(|argument| argument.default.is_some())
    {
        return failure(
            "frontend.python.references.signature-unsupported",
            format!("function {:?} has an unsupported signature", function.name),
        );
    }
    let return_type = match function.returns.as_deref() {
        Some(ast::Expr::Name(name)) if pure_bool && name.id.as_str() == "bool" => None,
        Some(ast::Expr::Constant(value)) if value.value == ast::Constant::None => None,
        annotation => Some(reference_annotation(annotation, classes)?),
    };
    let pure_bool_result = if pure_bool {
        let executable_body = function
            .body
            .iter()
            .filter(|statement| !is_inert_string_statement(statement))
            .collect::<Vec<_>>();
        match executable_body.as_slice() {
            [ast::Stmt::Return(statement)] => {
                statement
                    .value
                    .as_deref()
                    .cloned()
                    .ok_or_else(|| ContractFailure {
                        code: "frontend.python.references.pure-bool-return-missing",
                        message: format!(
                            "pure boolean function {:?} requires one value-return statement",
                            function.name
                        ),
                    })?
            }
            _ => {
                return failure(
                    "frontend.python.references.pure-bool-body-unsupported",
                    format!(
                        "pure boolean function {:?} requires one expression return",
                        function.name
                    ),
                );
            }
        }
        .into()
    } else {
        None
    };
    let parameters = function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .map(|argument| {
            Ok((
                argument.def.arg.to_string(),
                reference_annotation(argument.def.annotation.as_deref(), classes)?,
            ))
        })
        .collect::<Result<Vec<_>, ContractFailure>>()?;
    Ok(FunctionSummary {
        parameters,
        return_type,
        pure_bool_result,
    })
}

fn reference_annotation(
    annotation: Option<&ast::Expr>,
    classes: &BTreeMap<String, String>,
) -> Result<ReferenceType, ContractFailure> {
    match annotation {
        Some(ast::Expr::Name(name)) if classes.contains_key(name.id.as_str()) => {
            Ok(ReferenceType::NonNull(classes[name.id.as_str()].clone()))
        }
        Some(ast::Expr::Subscript(subscript)) if matches!(subscript.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Optional") =>
        {
            let ast::Expr::Name(inner) = subscript.slice.as_ref() else {
                return failure(
                    "frontend.python.references.type-unsupported",
                    "Optional must contain one source class",
                );
            };
            if classes.contains_key(inner.id.as_str()) {
                Ok(ReferenceType::Optional(classes[inner.id.as_str()].clone()))
            } else {
                failure(
                    "frontend.python.references.type-unsupported",
                    format!("Optional names unknown source class {:?}", inner.id),
                )
            }
        }
        Some(ast::Expr::Subscript(subscript))
            if matches!(subscript.value.as_ref(), ast::Expr::Name(name)
                if matches!(name.id.as_str(), "List" | "Set" | "Dict" | "Tuple" | "Sequence")) =>
        {
            failure(
                "frontend.python.references.collection-type-unsupported",
                "aggregate collection annotations require scalar or heap verification",
            )
        }
        _ => failure(
            "frontend.python.references.type-unsupported",
            "parameters require a source class or Optional[source class] annotation",
        ),
    }
}

#[derive(Clone, Debug)]
struct LoweredReferenceBool {
    term: Term,
    call_requirements: Vec<Term>,
}

fn lower_reference_bool_expression(
    expression: &ast::Expr,
    environment: &BTreeMap<String, ReferenceValue>,
    summaries: &BTreeMap<String, FunctionSummary>,
    builtin_identity_equality_classes: &BTreeSet<String>,
    active_calls: &mut BTreeSet<String>,
) -> Result<LoweredReferenceBool, ContractFailure> {
    match expression {
        ast::Expr::Constant(constant) => match constant.value {
            ast::Constant::Bool(value) => Ok(LoweredReferenceBool {
                term: Term::Bool { value },
                call_requirements: Vec::new(),
            }),
            _ => failure(
                "frontend.python.references.bool-expression-unsupported",
                "reference boolean expressions require boolean constants",
            ),
        },
        ast::Expr::BoolOp(operation) => {
            let mut terms = Vec::with_capacity(operation.values.len());
            let mut call_requirements = Vec::new();
            for value in &operation.values {
                let lowered = lower_reference_bool_expression(
                    value,
                    environment,
                    summaries,
                    builtin_identity_equality_classes,
                    active_calls,
                )?;
                terms.push(lowered.term);
                call_requirements.extend(lowered.call_requirements);
            }
            let term = match operation.op {
                ast::BoolOp::And => Term::And { values: terms },
                ast::BoolOp::Or => Term::Or { values: terms },
            };
            Ok(LoweredReferenceBool {
                term,
                call_requirements,
            })
        }
        ast::Expr::UnaryOp(operation) if operation.op == ast::UnaryOp::Not => {
            let lowered = lower_reference_bool_expression(
                &operation.operand,
                environment,
                summaries,
                builtin_identity_equality_classes,
                active_calls,
            )?;
            Ok(LoweredReferenceBool {
                term: Term::Not {
                    value: Box::new(lowered.term),
                },
                call_requirements: lowered.call_requirements,
            })
        }
        ast::Expr::Compare(_) => Ok(LoweredReferenceBool {
            term: lower_identity(expression, environment, builtin_identity_equality_classes)?,
            call_requirements: Vec::new(),
        }),
        ast::Expr::Call(call) => {
            let ast::Expr::Name(name) = call.func.as_ref() else {
                return failure(
                    "frontend.python.references.pure-call-target-unsupported",
                    "pure reference predicates require a direct source function name",
                );
            };
            let callee = summaries
                .get(name.id.as_str())
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.references.pure-call-unresolved",
                    message: format!("pure reference predicate {:?} is unresolved", name.id),
                })?;
            let result = callee
                .pure_bool_result
                .as_ref()
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.references.pure-call-result-type",
                    message: format!("reference call {:?} does not return bool", name.id),
                })?;
            if !call.keywords.is_empty() || call.args.len() != callee.parameters.len() {
                return failure(
                    "frontend.python.references.pure-call-arguments",
                    format!(
                        "pure reference predicate {:?} requires {} positional arguments",
                        name.id,
                        callee.parameters.len()
                    ),
                );
            }
            if !active_calls.insert(name.id.to_string()) {
                return failure(
                    "frontend.python.references.pure-call-cycle",
                    format!(
                        "recursive pure reference predicate {:?} is unsupported",
                        name.id
                    ),
                );
            }
            let mut callee_environment = BTreeMap::new();
            let mut call_requirements = Vec::new();
            for ((parameter, expected), argument) in callee.parameters.iter().zip(&call.args) {
                let actual = lower_reference_value(argument, environment)?;
                call_requirements.push(call_type_compatible(expected, &actual));
                callee_environment.insert(parameter.clone(), actual);
            }
            let lowered = lower_reference_bool_expression(
                result,
                &callee_environment,
                summaries,
                builtin_identity_equality_classes,
                active_calls,
            );
            active_calls.remove(name.id.as_str());
            let mut lowered = lowered?;
            call_requirements.append(&mut lowered.call_requirements);
            Ok(LoweredReferenceBool {
                term: lowered.term,
                call_requirements,
            })
        }
        _ => failure(
            "frontend.python.references.bool-expression-unsupported",
            format!("unsupported reference boolean expression {expression:?}"),
        ),
    }
}

fn lower_function(
    function: &ast::StmtFunctionDef,
    summaries: &BTreeMap<String, FunctionSummary>,
    builtin_identity_equality_classes: &BTreeSet<String>,
    source: &str,
    path: &str,
) -> Result<Vec<Obligation>, ContractFailure> {
    let summary = &summaries[function.name.as_str()];
    let mut environment = BTreeMap::new();
    let mut assumptions = Vec::new();
    for (name, ty) in &summary.parameters {
        let term = Term::Variable {
            name: format!("{}::{name}", function.name),
            sort: Sort::Reference,
        };
        if matches!(ty, ReferenceType::NonNull(_)) {
            assumptions.push(not_null(term.clone()));
        }
        environment.insert(
            name.clone(),
            ReferenceValue {
                term,
                ty: ty.clone(),
            },
        );
    }
    let mut obligations = Vec::new();
    let mut returned = false;
    for statement in &function.body {
        if returned {
            return failure(
                "frontend.python.references.unreachable-statement",
                format!("function {:?} has statements after return", function.name),
            );
        }
        match statement {
            statement if is_inert_string_statement(statement) => {
                // Function docstrings and standalone literal strings cannot mutate reference
                // state, introduce calls, or alter control flow.
            }
            ast::Stmt::Assign(assignment) if assignment.targets.len() == 1 => {
                let ast::Expr::Name(target) = &assignment.targets[0] else {
                    return failure(
                        "frontend.python.references.assignment-target-unsupported",
                        "reference assignment requires one local name target",
                    );
                };
                let ast::Expr::Call(call) = assignment.value.as_ref() else {
                    return failure(
                        "frontend.python.references.assignment-value-unsupported",
                        "reference assignment currently requires a contracted call",
                    );
                };
                let offset = u32::from(assignment.range.start());
                let value = lower_reference_call(
                    call,
                    summaries,
                    &environment,
                    &mut assumptions,
                    &mut obligations,
                    function,
                    path,
                    source,
                    offset,
                )?
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.references.assignment-unit-value",
                    message: "a None-returning call cannot initialize a reference".to_owned(),
                })?;
                environment.insert(target.id.to_string(), value);
            }
            ast::Stmt::Expr(statement) => {
                let ast::Expr::Call(call) = statement.value.as_ref() else {
                    return unsupported_statement(function, statement.value.as_ref());
                };
                let ast::Expr::Name(name) = call.func.as_ref() else {
                    return unsupported_statement(function, statement.value.as_ref());
                };
                let offset = u32::from(statement.range.start());
                if matches!(name.id.as_str(), "Requires" | "Ensures")
                    && call.args.len() == 1
                    && call.keywords.is_empty()
                {
                    let mut active_calls = BTreeSet::from([function.name.to_string()]);
                    let lowered = lower_reference_bool_expression(
                        &call.args[0],
                        &environment,
                        summaries,
                        builtin_identity_equality_classes,
                        &mut active_calls,
                    )?;
                    for (index, requirement) in lowered.call_requirements.into_iter().enumerate() {
                        obligations.push(obligation(
                            format!(
                                "{}:{}-call-precondition:{index}:{offset}",
                                function.name,
                                name.id.as_str().to_ascii_lowercase()
                            ),
                            assumptions.clone(),
                            requirement,
                            path,
                            source,
                            offset,
                        ));
                    }
                    if name.id.as_str() == "Requires" {
                        assumptions.push(lowered.term);
                    } else {
                        obligations.push(obligation(
                            format!("{}:postcondition:{offset}", function.name),
                            assumptions.clone(),
                            lowered.term,
                            path,
                            source,
                            offset,
                        ));
                    }
                } else if name.id.as_str() == "Assert"
                    && call.args.len() == 1
                    && call.keywords.is_empty()
                {
                    let assertion = lower_identity(
                        &call.args[0],
                        &environment,
                        builtin_identity_equality_classes,
                    )?;
                    obligations.push(obligation(
                        format!("{}:assert:{offset}", function.name),
                        assumptions.clone(),
                        assertion,
                        path,
                        source,
                        offset,
                    ));
                } else if summaries.contains_key(name.id.as_str()) {
                    lower_reference_call(
                        call,
                        summaries,
                        &environment,
                        &mut assumptions,
                        &mut obligations,
                        function,
                        path,
                        source,
                        offset,
                    )?;
                } else {
                    return unsupported_statement(function, statement.value.as_ref());
                }
            }
            ast::Stmt::Return(statement) => {
                if summary.pure_bool_result.is_some() {
                    let expression = statement.value.as_deref().ok_or_else(|| ContractFailure {
                        code: "frontend.python.references.pure-bool-return-missing",
                        message: format!(
                            "pure boolean function {:?} requires a return value",
                            function.name
                        ),
                    })?;
                    let offset = u32::from(statement.range.start());
                    let mut active_calls = BTreeSet::from([function.name.to_string()]);
                    let lowered = lower_reference_bool_expression(
                        expression,
                        &environment,
                        summaries,
                        builtin_identity_equality_classes,
                        &mut active_calls,
                    )?;
                    for (index, requirement) in lowered.call_requirements.into_iter().enumerate() {
                        obligations.push(obligation(
                            format!(
                                "{}:return-call-precondition:{index}:{offset}",
                                function.name
                            ),
                            assumptions.clone(),
                            requirement,
                            path,
                            source,
                            offset,
                        ));
                    }
                } else {
                    match (&summary.return_type, statement.value.as_deref()) {
                        (None, None) => {}
                        (Some(expected), Some(ast::Expr::Call(call))) => {
                            let offset = u32::from(statement.range.start());
                            let actual = lower_reference_call(
                                call,
                                summaries,
                                &environment,
                                &mut assumptions,
                                &mut obligations,
                                function,
                                path,
                                source,
                                offset,
                            )?
                            .ok_or_else(|| ContractFailure {
                                code: "frontend.python.references.return-type-mismatch",
                                message: "None-returning call used as a reference return"
                                    .to_owned(),
                            })?;
                            obligations.push(obligation(
                                format!("{}:return-type:{offset}", function.name),
                                assumptions.clone(),
                                call_type_compatible(expected, &actual),
                                path,
                                source,
                                offset,
                            ));
                        }
                        (Some(expected), Some(expression)) => {
                            let actual = lower_reference_value(expression, &environment)?;
                            let offset = u32::from(statement.range.start());
                            obligations.push(obligation(
                                format!("{}:return-type:{offset}", function.name),
                                assumptions.clone(),
                                call_type_compatible(expected, &actual),
                                path,
                                source,
                                offset,
                            ));
                        }
                        _ => {
                            return failure(
                                "frontend.python.references.return-type-mismatch",
                                format!(
                                    "function {:?} return does not match its nominal annotation",
                                    function.name
                                ),
                            );
                        }
                    }
                }
                returned = true;
            }
            ast::Stmt::Pass(_) => {}
            _ => {
                return failure(
                    "frontend.python.references.statement-unsupported",
                    format!(
                        "function {:?} contains unsupported statement {statement:?}",
                        function.name
                    ),
                );
            }
        }
    }
    if (summary.return_type.is_some() || summary.pure_bool_result.is_some()) && !returned {
        obligations.push(obligation(
            format!("{}:reference-return-totality", function.name),
            assumptions.clone(),
            Term::Bool { value: false },
            path,
            source,
            function.range.start().into(),
        ));
    }
    obligations.push(obligation(
        format!("{}:reference-function-complete", function.name),
        assumptions,
        Term::Bool { value: true },
        path,
        source,
        function.range.start().into(),
    ));
    Ok(obligations)
}

#[allow(clippy::too_many_arguments)]
fn lower_reference_call(
    call: &ast::ExprCall,
    summaries: &BTreeMap<String, FunctionSummary>,
    environment: &BTreeMap<String, ReferenceValue>,
    assumptions: &mut Vec<Term>,
    obligations: &mut Vec<Obligation>,
    function: &ast::StmtFunctionDef,
    path: &str,
    source: &str,
    offset: u32,
) -> Result<Option<ReferenceValue>, ContractFailure> {
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return failure(
            "frontend.python.references.call-target-unsupported",
            "reference calls require a direct imported or source function name",
        );
    };
    let callee = summaries
        .get(name.id.as_str())
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.references.call-unresolved",
            message: format!("reference call target {:?} is unresolved", name.id),
        })?;
    if !call.keywords.is_empty() || call.args.len() != callee.parameters.len() {
        return failure(
            "frontend.python.references.call-arguments",
            format!(
                "call to {:?} requires {} positional arguments",
                name.id,
                callee.parameters.len()
            ),
        );
    }
    let checks = callee
        .parameters
        .iter()
        .zip(&call.args)
        .map(|((_, expected), argument)| {
            let actual = lower_reference_value(argument, environment)?;
            Ok(call_type_compatible(expected, &actual))
        })
        .collect::<Result<Vec<_>, ContractFailure>>()?;
    obligations.push(obligation(
        format!("{}:call-precondition:{}:{offset}", function.name, name.id),
        assumptions.clone(),
        Term::And { values: checks },
        path,
        source,
        offset,
    ));
    let Some(return_type) = callee.return_type.clone() else {
        return Ok(None);
    };
    let value = ReferenceValue {
        term: Term::Variable {
            name: format!("{}::call-result:{}:{offset}", function.name, name.id),
            sort: Sort::Reference,
        },
        ty: return_type,
    };
    if matches!(value.ty, ReferenceType::NonNull(_)) {
        assumptions.push(not_null(value.term.clone()));
    }
    Ok(Some(value))
}

fn lower_identity(
    expression: &ast::Expr,
    environment: &BTreeMap<String, ReferenceValue>,
    builtin_identity_equality_classes: &BTreeSet<String>,
) -> Result<Term, ContractFailure> {
    let ast::Expr::Compare(comparison) = expression else {
        return failure(
            "frontend.python.references.assertion-unsupported",
            "reference Assert requires one identity comparison",
        );
    };
    if comparison.ops.len() != 1 || comparison.comparators.len() != 1 {
        return failure(
            "frontend.python.references.assertion-unsupported",
            "reference assertions require one comparison",
        );
    }
    let left = lower_reference_value(&comparison.left, environment)?;
    let right = lower_reference_value(&comparison.comparators[0], environment)?;
    let equality_uses_builtin_identity = match (left.ty.class(), right.ty.class()) {
        (Some(left_class), Some(right_class)) if left_class == right_class => {
            builtin_identity_equality_classes.contains(left_class)
        }
        _ => false,
    };
    let positive = match comparison.ops[0] {
        ast::CmpOp::Is => true,
        ast::CmpOp::IsNot => false,
        ast::CmpOp::Eq if equality_uses_builtin_identity => true,
        ast::CmpOp::NotEq if equality_uses_builtin_identity => false,
        ast::CmpOp::Eq | ast::CmpOp::NotEq => {
            return failure(
                "frontend.python.references.equality-dispatch-unsupported",
                "reference equality requires one exact source class with proven builtin object identity equality",
            );
        }
        _ => {
            return failure(
                "frontend.python.references.assertion-unsupported",
                "reference assertions require one is/is not or proven identity-equivalent ==/!= comparison",
            );
        }
    };
    let identity = identity_term(&left, &right);
    Ok(if positive {
        identity
    } else {
        Term::Not {
            value: Box::new(identity),
        }
    })
}

fn lower_reference_value(
    expression: &ast::Expr,
    environment: &BTreeMap<String, ReferenceValue>,
) -> Result<ReferenceValue, ContractFailure> {
    match expression {
        ast::Expr::Name(name) => {
            environment
                .get(name.id.as_str())
                .cloned()
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.references.name-unresolved",
                    message: format!("unknown reference name {:?}", name.id),
                })
        }
        ast::Expr::Constant(value) if value.value == ast::Constant::None => Ok(ReferenceValue {
            term: Term::NullReference,
            ty: ReferenceType::Null,
        }),
        _ => failure(
            "frontend.python.references.expression-unsupported",
            format!("unsupported reference expression {expression:?}"),
        ),
    }
}

fn identity_term(left: &ReferenceValue, right: &ReferenceValue) -> Term {
    let equality = Term::Equal {
        left: Box::new(left.term.clone()),
        right: Box::new(right.term.clone()),
    };
    match (left.ty.class(), right.ty.class()) {
        (None, _) | (_, None) => equality,
        (Some(left_class), Some(right_class)) if left_class == right_class => equality,
        (Some(_), Some(_)) if left.ty.is_optional() && right.ty.is_optional() => Term::And {
            values: vec![
                equality,
                Term::Equal {
                    left: Box::new(left.term.clone()),
                    right: Box::new(Term::NullReference),
                },
            ],
        },
        (Some(_), Some(_)) => Term::Bool { value: false },
    }
}

fn call_type_compatible(expected: &ReferenceType, actual: &ReferenceValue) -> Term {
    match (expected, &actual.ty) {
        (ReferenceType::Optional(_), ReferenceType::Null) => Term::Bool { value: true },
        (ReferenceType::NonNull(expected), ReferenceType::NonNull(actual_class))
            if expected == actual_class =>
        {
            Term::Bool { value: true }
        }
        (ReferenceType::NonNull(expected), ReferenceType::Optional(actual_class))
            if expected == actual_class =>
        {
            not_null(actual.term.clone())
        }
        (ReferenceType::Optional(expected), ReferenceType::NonNull(actual_class))
        | (ReferenceType::Optional(expected), ReferenceType::Optional(actual_class))
            if expected == actual_class =>
        {
            Term::Bool { value: true }
        }
        _ => Term::Bool { value: false },
    }
}

fn not_null(value: Term) -> Term {
    Term::Not {
        value: Box::new(Term::Equal {
            left: Box::new(value),
            right: Box::new(Term::NullReference),
        }),
    }
}

fn obligation(
    id: String,
    assumptions: Vec<Term>,
    conclusion: Term,
    path: &str,
    source: &str,
    offset: u32,
) -> Obligation {
    let (line, column) = location(source, offset);
    Obligation {
        id,
        expectation: ObligationExpectation::Prove,
        assumptions,
        conclusion,
        path: path.to_owned(),
        byte_offset: offset,
        line,
        column,
    }
}

fn location(source: &str, offset: u32) -> (u32, u32) {
    let offset = usize::try_from(offset)
        .unwrap_or(usize::MAX)
        .min(source.len());
    let prefix = &source[..offset];
    let line =
        u32::try_from(prefix.bytes().filter(|byte| *byte == b'\n').count() + 1).unwrap_or(u32::MAX);
    let column = u32::try_from(
        prefix
            .rsplit_once('\n')
            .map_or(prefix.len(), |(_, tail)| tail.len())
            + 1,
    )
    .unwrap_or(u32::MAX);
    (line, column)
}

fn unsupported_statement<T>(
    function: &ast::StmtFunctionDef,
    expression: &ast::Expr,
) -> Result<T, ContractFailure> {
    failure(
        "frontend.python.references.expression-unsupported",
        format!(
            "function {:?} contains unsupported expression {expression:?}",
            function.name
        ),
    )
}

fn is_inert_string_statement(statement: &ast::Stmt) -> bool {
    matches!(statement, ast::Stmt::Expr(expression)
        if matches!(expression.value.as_ref(), ast::Expr::Constant(constant)
            if matches!(constant.value, ast::Constant::Str(_))))
}

fn failure<T>(code: &'static str, message: impl Into<String>) -> Result<T, ContractFailure> {
    Err(ContractFailure {
        code,
        message: message.into(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vc::ObligationStatus;

    const FIXTURE: &str = "from nagini_contracts.contracts import Assert\nfrom typing import Optional\n\nclass B:\n    pass\n\nclass C:\n    pass\n\ndef maybe(b: Optional[B], c: Optional[C]) -> None:\n    Assert(b is not c)\n\ndef distinct(b: B, c: C) -> None:\n    Assert(b is not c)\n\ndef caller() -> None:\n    maybe(None, None)\n    distinct(None, None)\n";

    #[test]
    fn proves_nominal_distinction_and_refutes_nullable_identity_and_bad_call() {
        let result = verify_reference_module(FIXTURE, "references.py", &[]).unwrap();
        assert!(!result.passed);
        assert_eq!(
            result
                .obligations
                .iter()
                .filter(|obligation| obligation.status == ObligationStatus::Refuted)
                .count(),
            2
        );
        assert!(result.obligations.iter().any(|obligation| {
            obligation.id.starts_with("maybe:assert:")
                && obligation.status == ObligationStatus::Refuted
        }));
        assert!(result.obligations.iter().any(|obligation| {
            obligation
                .id
                .starts_with("caller:call-precondition:distinct:")
                && obligation.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn external_nominal_return_is_nonnull_and_composes_into_calls() {
        let external = parse_external_reference_contract_module(
            "from typing import Optional\nfrom nagini_contracts.contracts import ContractOnly\n\nclass Widget:\n    pass\n\n@ContractOnly\ndef make() -> Widget:\n    ...\n\n@ContractOnly\ndef consume(value: Widget) -> None:\n    ...\n",
            "provider_contract.py",
            "provider",
        )
        .unwrap();
        assert_eq!(external.type_names(), ["provider.Widget"]);
        let result = verify_reference_module_with_imports(
            "from nagini_contracts.contracts import Assert\nfrom provider import Widget, make, consume\n\ndef run() -> None:\n    value = make()\n    Assert(value is not None)\n    consume(value)\n",
            "adapter.py",
            &["run".to_owned()],
            &[external],
        )
        .unwrap();
        assert!(result.passed);
        assert!(
            result
                .obligations
                .iter()
                .any(|obligation| obligation.id.starts_with("run:assert:"))
        );
    }

    #[test]
    fn optional_external_return_does_not_become_nonnull_by_annotation_fiat() {
        let external = parse_external_reference_contract_module(
            "from typing import Optional\nfrom nagini_contracts.contracts import ContractOnly\n\nclass Widget:\n    pass\n\n@ContractOnly\ndef maybe() -> Optional[Widget]:\n    ...\n",
            "provider_contract.py",
            "provider",
        )
        .unwrap();
        let result = verify_reference_module_with_imports(
            "from nagini_contracts.contracts import Assert\nfrom provider import Widget, maybe\n\ndef run() -> None:\n    value = maybe()\n    Assert(value is not None)\n",
            "adapter.py",
            &["run".to_owned()],
            &[external],
        )
        .unwrap();
        assert!(!result.passed);
        assert!(result.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:")
                && obligation.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn source_wrapper_can_return_external_nominal_value() {
        let external = parse_external_reference_contract_module(
            "from nagini_contracts.contracts import ContractOnly\n\nclass Widget:\n    pass\n\n@ContractOnly\ndef make() -> Widget:\n    ...\n",
            "provider_contract.py",
            "provider",
        )
        .unwrap();
        let result = verify_reference_module_with_imports(
            "from provider import Widget, make\n\ndef build() -> Widget:\n    return make()\n",
            "adapter.py",
            &["build".to_owned()],
            &[external],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn external_reference_contract_refuses_executable_body() {
        let error = parse_external_reference_contract_module(
            "from nagini_contracts.contracts import ContractOnly\n\nclass Widget:\n    pass\n\n@ContractOnly\ndef make() -> Widget:\n    return Widget()\n",
            "provider_contract.py",
            "provider",
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.references.external-body-not-contract-only"
        );
    }

    #[test]
    fn source_nominal_type_survives_two_modular_summary_edges() {
        let (_, provider) = verify_and_export_source_reference_module(
            "class Widget:\n    pass\n\ndef identity(value: Widget) -> Widget:\n    return value\n",
            "provider.py",
            "provider",
            &[],
        )
        .unwrap();
        let (_, adapter) = verify_and_export_source_reference_module(
            "from provider import Widget, identity\n\ndef passthrough(value: Widget) -> Widget:\n    return identity(value)\n",
            "adapter.py",
            "adapter",
            std::slice::from_ref(&provider),
        )
        .unwrap();
        let result = verify_reference_module_with_imports(
            "from nagini_contracts.contracts import Assert\nfrom provider import Widget\nfrom adapter import passthrough\n\ndef run(value: Widget) -> None:\n    returned = passthrough(value)\n    Assert(returned is not None)\n",
            "app.py",
            &["run".to_owned()],
            &[provider, adapter],
        )
        .unwrap();
        assert!(result.passed);
    }
}
