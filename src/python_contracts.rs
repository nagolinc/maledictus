//! Lowering of the scalar Nagini contract fragment to verification conditions.

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroI128;

use rustpython_ast::Visitor;
use rustpython_parser::{Mode, Parse, Tok, ast, ast::Ranged, lexer::lex};
use serde::{Deserialize, Serialize};

use crate::call_binding::{
    ActualItem, BindingError, BoundArgument, CallSignature, FormalParameter, ParameterKind,
    TypedValue, bind_call_with,
};
use crate::python_sequence_builtins::{self, SequenceBuiltinError};
use crate::solver::discharge;
use crate::vc::{Obligation, ObligationExpectation, ObligationResult, Sort, Term};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractFailure {
    pub code: &'static str,
    pub message: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ContractVerification {
    pub schema: String,
    pub path: String,
    pub functions: Vec<String>,
    pub obligations: Vec<ObligationResult>,
    pub passed: bool,
}

#[derive(Clone, Debug)]
struct SymbolicState {
    environment: BTreeMap<String, Term>,
    identities: BTreeMap<String, PythonObjectIdentity>,
    assumptions: Vec<Term>,
}

/// A source assignment type comment. `Optional[T]` is kept distinct from `T`: erasing the
/// optional wrapper would either reject the valid `None` branch or lose the promised member type
/// for non-`None` values.
#[derive(Clone, Debug, Eq, PartialEq)]
enum ScalarTypeComment {
    Exact(Sort),
    Optional(Sort),
}

/// Proven object identity for the immutable scalar objects whose allocation behavior this
/// frontend models. Value terms deliberately remain separate: two fresh `str(...)` results can
/// compare equal while still having distinct identities.
#[derive(Clone, Debug, Eq, PartialEq)]
enum PythonObjectIdentity {
    EmptyTuple,
    EllipsisSingleton,
    InternedString(String),
    FunctionInput(String),
    Fresh(u32),
    Uncertain(u32),
}

const ELLIPSIS_TYPE_IDENTITY: &str = "types::EllipsisType";

fn ellipsis_singleton() -> Term {
    Term::NominalReference {
        name: "builtins::Ellipsis".to_owned(),
        class: ELLIPSIS_TYPE_IDENTITY.to_owned(),
    }
}

fn ellipsis_type_object() -> Term {
    Term::ClassLiteral {
        name: ELLIPSIS_TYPE_IDENTITY.to_owned(),
    }
}

#[derive(Clone, Debug)]
struct ReturnPath {
    state: SymbolicState,
    value: Term,
    byte_offset: u32,
}

#[derive(Clone, Debug)]
struct ExceptionalPath {
    state: SymbolicState,
    exception_type: String,
    byte_offset: u32,
    application_precondition: bool,
}

#[derive(Clone, Debug)]
struct RuntimeExceptionGuard {
    condition: Term,
    evaluation_condition: Term,
    exception_type: &'static str,
    byte_offset: u32,
}

#[derive(Clone, Debug)]
struct ContractPostcondition {
    expression: ast::Expr,
    result_binder: Option<String>,
}

#[derive(Clone, Debug)]
struct LoweredFunction {
    specification_safety: Vec<Obligation>,
    obligations: Vec<Obligation>,
}

type LoweredComprehensionSource = (
    String,
    Term,
    String,
    Sort,
    BTreeMap<String, Term>,
    Option<Term>,
);

#[derive(Clone, Debug)]
struct InlineParameter {
    name: String,
    sort: Sort,
    default: Option<ast::Expr>,
    positional_only: bool,
}

#[derive(Clone, Debug)]
struct InlineFunction {
    positional_parameters: Vec<InlineParameter>,
    keyword_only_parameters: Vec<InlineParameter>,
    var_args: Option<(String, Sort)>,
    keyword_args: Option<(String, Sort)>,
    return_sort: Sort,
    preconditions: Vec<ast::Expr>,
    postconditions: Vec<ContractPostcondition>,
    exceptional_postconditions: Vec<(String, ast::Expr)>,
    expression: Option<ast::Expr>,
    modular_call: bool,
    pure: bool,
    ghost: bool,
    captured_environment: Option<BTreeMap<String, Term>>,
    scalar_identity_result: Option<String>,
}

#[derive(Clone, Debug)]
struct ImmutableModuleGlobals {
    values: BTreeMap<String, Term>,
    initialization_failure: Option<ModuleInitializationFailure>,
    list_mutations: Vec<ModuleListMutationRecord>,
    obligations: Vec<Obligation>,
}

#[derive(Clone, Debug)]
struct ModuleIdentity {
    name: String,
    file: String,
}

struct ModuleDerivationContext<'a> {
    source: &'a str,
    path: &'a str,
    functions: &'a BTreeMap<String, InlineFunction>,
    type_comments: &'a BTreeMap<u32, ScalarTypeComment>,
    exception_hierarchy: &'a ExceptionHierarchy,
    conformance_mode: bool,
    identity: &'a ModuleIdentity,
}

impl ModuleIdentity {
    fn entry(path: &str) -> Self {
        Self {
            name: "__main__".to_owned(),
            file: path.replace('\\', "/"),
        }
    }

    fn imported(module: &str, path: &str) -> Self {
        Self {
            name: module.to_owned(),
            file: path.replace('\\', "/"),
        }
    }
}

fn is_protected_module_metadata(name: &str) -> bool {
    matches!(name, "__name__" | "__file__")
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ModuleListMutationRecord {
    binding: String,
    index: usize,
    evaluation: [ModuleListMutationStep; 6],
    previous: Term,
    right: Term,
    result: Term,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ModuleListMutationStep {
    Container,
    Index,
    Read,
    RightHandSide,
    PrimitiveOperation,
    Store,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ModuleListAugAssignShape {
    binding: String,
    index: usize,
}

#[derive(Clone, Debug)]
struct ModuleInitializationFailure {
    binding: String,
    byte_offset: u32,
}

type InlineSignature = (
    Vec<InlineParameter>,
    Vec<InlineParameter>,
    Option<(String, Sort)>,
    Option<(String, Sort)>,
);

fn inline_signature(arguments: &ast::Arguments) -> Result<InlineSignature, ContractFailure> {
    let mut positional_parameters =
        Vec::with_capacity(arguments.posonlyargs.len() + arguments.args.len());
    for argument in &arguments.posonlyargs {
        positional_parameters.push(InlineParameter {
            name: argument.def.arg.to_string(),
            sort: annotation_sort(argument.def.annotation.as_deref())?,
            default: argument.default.as_deref().cloned(),
            positional_only: true,
        });
    }
    for argument in &arguments.args {
        positional_parameters.push(InlineParameter {
            name: argument.def.arg.to_string(),
            sort: annotation_sort(argument.def.annotation.as_deref())?,
            default: argument.default.as_deref().cloned(),
            positional_only: false,
        });
    }
    let keyword_only_parameters = arguments
        .kwonlyargs
        .iter()
        .map(|argument| {
            Ok(InlineParameter {
                name: argument.def.arg.to_string(),
                sort: annotation_sort(argument.def.annotation.as_deref())?,
                default: argument.default.as_deref().cloned(),
                positional_only: false,
            })
        })
        .collect::<Result<Vec<_>, ContractFailure>>()?;
    let var_args = arguments
        .vararg
        .as_deref()
        .map(|argument| {
            Ok((
                argument.arg.to_string(),
                annotation_sort(argument.annotation.as_deref())?,
            ))
        })
        .transpose()?;
    if var_args.as_ref().is_some_and(|(_, sort)| {
        !matches!(
            sort,
            Sort::Bool | Sort::Int | Sort::String | Sort::Reference | Sort::Bytes
        )
    }) {
        return failure(
            "frontend.python.contracts.varargs-type-unsupported",
            "*args elements require a primitive, bytes, or reference annotation",
        );
    }
    let keyword_args = arguments
        .kwarg
        .as_deref()
        .map(|argument| {
            Ok((
                argument.arg.to_string(),
                annotation_sort(argument.annotation.as_deref())?,
            ))
        })
        .transpose()?;
    if keyword_args.as_ref().is_some_and(|(_, sort)| {
        !matches!(
            sort,
            Sort::Bool | Sort::Int | Sort::String | Sort::Reference | Sort::Bytes
        )
    }) {
        return failure(
            "frontend.python.contracts.kwargs-type-unsupported",
            "**kwargs values require a primitive, bytes, or reference annotation",
        );
    }
    Ok((
        positional_parameters,
        keyword_only_parameters,
        var_args,
        keyword_args,
    ))
}

#[derive(Clone, Debug, Default)]
struct ExceptionHierarchy {
    parents: BTreeMap<String, String>,
    visible: std::collections::BTreeSet<String>,
    origins: BTreeMap<String, String>,
}

impl ExceptionHierarchy {
    fn from_suite(suite: &[ast::Stmt]) -> Result<Self, ContractFailure> {
        let mut hierarchy = Self::default();
        for statement in suite {
            let ast::Stmt::ClassDef(class) = statement else {
                continue;
            };
            hierarchy.register_class_if_exception(class)?;
        }
        Ok(hierarchy)
    }

    fn register_class_if_exception(
        &mut self,
        class: &ast::StmtClassDef,
    ) -> Result<bool, ContractFailure> {
        if self.parents.contains_key(class.name.as_str()) {
            return failure(
                "frontend.python.contracts.exception-class-duplicate",
                format!("duplicate or shadowing exception class {:?}", class.name),
            );
        }
        if class.bases.len() != 1 || !class.keywords.is_empty() {
            return Ok(false);
        }
        let ast::Expr::Name(parent) = &class.bases[0] else {
            return Ok(false);
        };
        if !self.supports(parent.id.as_str()) {
            return Ok(false);
        }
        if !class.decorator_list.is_empty()
            || !class.type_params.is_empty()
            || !has_inert_class_body(&class.body)
        {
            return failure(
                "frontend.python.contracts.exception-class-body-unsupported",
                format!(
                    "exception class {:?} must be an undecorated inert-body subclass in the scalar fragment",
                    class.name
                ),
            );
        }
        self.parents
            .insert(class.name.to_string(), parent.id.to_string());
        self.visible.insert(class.name.to_string());
        Ok(true)
    }

    fn supports(&self, exception_type: &str) -> bool {
        builtin_exception_parent(exception_type).is_some()
            || exception_type == "BaseException"
            || self.visible.contains(exception_type)
    }

    fn merge_known(&mut self, other: &Self) -> Result<(), ContractFailure> {
        for (exception_type, parent) in &other.parents {
            if let Some(existing) = self.parents.get(exception_type) {
                if existing != parent
                    || self.origins.get(exception_type) != other.origins.get(exception_type)
                {
                    return failure(
                        "frontend.python.contracts.exception-hierarchy-conflict",
                        format!(
                            "exception name {exception_type:?} resolves to conflicting nominal types"
                        ),
                    );
                }
            } else {
                self.parents.insert(exception_type.clone(), parent.clone());
                let origin = other.origins.get(exception_type).ok_or_else(|| ContractFailure {
                    code: "frontend.python.contracts.exception-origin-missing",
                    message: format!(
                        "imported exception type {exception_type:?} has no declaring-module identity"
                    ),
                })?;
                self.origins.insert(exception_type.clone(), origin.clone());
            }
        }
        Ok(())
    }

    fn assign_unowned_origin(&mut self, module: &str) {
        for exception_type in self.parents.keys() {
            self.origins
                .entry(exception_type.clone())
                .or_insert_with(|| module.to_owned());
        }
    }

    fn canonical_identity(&self, exception_type: &str) -> String {
        self.origins.get(exception_type).map_or_else(
            || exception_type.to_owned(),
            |origin| format!("{origin}.{exception_type}"),
        )
    }

    fn import_visible(&mut self, exception_type: &str) -> Result<(), ContractFailure> {
        if !self.parents.contains_key(exception_type) {
            return failure(
                "frontend.python.contracts.exception-type-unresolved",
                format!("imported exception type {exception_type:?} has no known hierarchy"),
            );
        }
        self.visible.insert(exception_type.to_owned());
        Ok(())
    }

    fn matches(&self, declared: &str, actual: &str) -> bool {
        let mut current = Some(actual);
        let mut visited = std::collections::BTreeSet::new();
        while let Some(exception_type) = current {
            if exception_type == declared {
                return true;
            }
            if !visited.insert(exception_type.to_owned()) {
                return false;
            }
            current = self
                .parents
                .get(exception_type)
                .map(String::as_str)
                .or_else(|| builtin_exception_parent(exception_type));
        }
        false
    }
}

fn builtin_exception_parent(exception_type: &str) -> Option<&'static str> {
    match exception_type {
        "Exception" => Some("BaseException"),
        "ValueError" | "TypeError" | "RuntimeError" | "LookupError" | "ArithmeticError" => {
            Some("Exception")
        }
        "IndexError" | "KeyError" => Some("LookupError"),
        "ZeroDivisionError" => Some("ArithmeticError"),
        _ => None,
    }
}

/// A parsed, hash-bound contract for one environment-owned Python module.
///
/// The function bodies are deliberately not verified: `@ContractOnly` makes the provider's
/// conformance to these signatures and contracts an explicit proof assumption. Application
/// adapters that import the module are still symbolically executed and must establish every
/// precondition at each call site.
#[derive(Clone, Debug)]
pub struct ImportedContractModule {
    module: String,
    functions: BTreeMap<String, InlineFunction>,
    exception_hierarchy: ExceptionHierarchy,
}

/// The part of an explicit external contract that can be bound to a Dagcert callable field.
/// Preconditions are reported rather than discarded: the operation backend currently refuses
/// them until it can prove them at the callback call site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportedCallableContract {
    pub positional_parameter_sorts: Vec<Sort>,
    pub return_sort: Sort,
    pub declared_exceptions: BTreeSet<String>,
    pub has_preconditions: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractImportBinding {
    pub module: String,
    pub imported_name: String,
    pub local_name: String,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SourceContractImportRequest {
    pub module: String,
    pub relative_level: u32,
    pub imported_names: Vec<(String, Option<String>)>,
}

fn resolve_exception_hierarchy(
    suite: &[ast::Stmt],
    imported_modules: &[ImportedContractModule],
) -> Result<ExceptionHierarchy, ContractFailure> {
    let imported_by_name = imported_modules
        .iter()
        .map(|imported| (imported.module.as_str(), imported))
        .collect::<BTreeMap<_, _>>();
    let mut hierarchy = ExceptionHierarchy::default();
    for imported in imported_modules {
        hierarchy.merge_known(&imported.exception_hierarchy)?;
    }
    for statement in suite {
        match statement {
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
                for alias in &import.names {
                    let imported_name = alias.name.as_str();
                    if imported_name == "*" {
                        for exception_type in imported.exception_hierarchy.parents.keys() {
                            if !exception_type.starts_with('_')
                                && imported
                                    .exception_hierarchy
                                    .origins
                                    .get(exception_type)
                                    .is_some_and(|origin| origin == module_name)
                            {
                                hierarchy.import_visible(exception_type)?;
                            }
                        }
                        continue;
                    }
                    if imported
                        .exception_hierarchy
                        .parents
                        .contains_key(imported_name)
                    {
                        if alias.asname.is_some() {
                            return failure(
                                "frontend.python.contract-import.exception-alias-unsupported",
                                "exception type aliases require canonical type-identity mapping",
                            );
                        }
                        hierarchy.import_visible(imported_name)?;
                    }
                }
            }
            ast::Stmt::ClassDef(class) => {
                hierarchy.register_class_if_exception(class)?;
            }
            _ => {}
        }
    }
    Ok(hierarchy)
}

impl ImportedContractModule {
    pub fn module(&self) -> &str {
        &self.module
    }

    pub fn function_names(&self) -> Vec<String> {
        self.functions.keys().cloned().collect()
    }

    pub fn declared_exception_types(&self) -> Vec<String> {
        self.functions
            .values()
            .flat_map(|function| {
                function
                    .exceptional_postconditions
                    .iter()
                    .map(|(exception_type, _)| {
                        self.exception_hierarchy.canonical_identity(exception_type)
                    })
            })
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    pub fn exception_type_names(&self) -> Vec<String> {
        self.exception_hierarchy
            .parents
            .keys()
            .map(|exception_type| self.exception_hierarchy.canonical_identity(exception_type))
            .collect()
    }

    pub fn callable_contract(
        &self,
        symbol: &str,
    ) -> Result<ImportedCallableContract, ContractFailure> {
        let Some(function) = self.functions.get(symbol) else {
            return failure(
                "frontend.python.dagcert.external-callable-symbol-missing",
                format!(
                    "external contract module {:?} has no callable symbol {symbol:?}",
                    self.module
                ),
            );
        };
        if !function.keyword_only_parameters.is_empty()
            || function.var_args.is_some()
            || function.keyword_args.is_some()
            || function
                .positional_parameters
                .iter()
                .any(|parameter| parameter.default.is_some())
        {
            return failure(
                "frontend.python.dagcert.external-callable-signature-unsupported",
                format!(
                    "external callback {:?}.{symbol} must have a fixed positional signature without defaults",
                    self.module
                ),
            );
        }
        Ok(ImportedCallableContract {
            positional_parameter_sorts: function
                .positional_parameters
                .iter()
                .map(|parameter| parameter.sort.clone())
                .collect(),
            return_sort: function.return_sort.clone(),
            declared_exceptions: function
                .exceptional_postconditions
                .iter()
                .map(|(exception, _)| self.exception_hierarchy.canonical_identity(exception))
                .collect(),
            has_preconditions: !function.preconditions.is_empty(),
        })
    }
}

/// Construct the exact opaque Python-side summary for a compiler-proved primitive-total
/// cross-language export. The caller supplies only the canonical signature derived and checked by
/// the mixed-language resolver; no request assertion can reach this constructor unchecked.
pub fn imported_primitive_total_module(
    module: &str,
    function: &str,
    parameters: &[(String, Sort)],
    return_sort: Sort,
) -> Result<ImportedContractModule, ContractFailure> {
    if module.is_empty()
        || module
            .split('.')
            .any(|part| part.is_empty() || !is_python_identifier(part))
        || !is_python_identifier(function)
        || parameters.iter().any(|(name, sort)| {
            !is_python_identifier(name) || !matches!(sort, Sort::Bool | Sort::String)
        })
        || !matches!(return_sort, Sort::Bool | Sort::String | Sort::Unit)
    {
        return failure(
            "frontend.python.cross-language.signature-unsupported",
            "cross-language summary requires canonical bool/str parameters and bool/str/None return",
        );
    }
    let mut parameter_names = BTreeSet::new();
    if parameters
        .iter()
        .any(|(name, _)| !parameter_names.insert(name.clone()))
    {
        return failure(
            "frontend.python.cross-language.signature-duplicate",
            "cross-language summary contains duplicate parameter names",
        );
    }
    let summary = InlineFunction {
        positional_parameters: parameters
            .iter()
            .map(|(name, sort)| InlineParameter {
                name: name.clone(),
                sort: sort.clone(),
                default: None,
                positional_only: false,
            })
            .collect(),
        keyword_only_parameters: Vec::new(),
        var_args: None,
        keyword_args: None,
        return_sort,
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        exceptional_postconditions: Vec::new(),
        expression: None,
        modular_call: true,
        pure: false,
        ghost: false,
        captured_environment: None,
        scalar_identity_result: None,
    };
    let mut functions = BTreeMap::new();
    functions.insert(function.to_owned(), summary);
    let module = ImportedContractModule {
        module: module.to_owned(),
        functions,
        exception_hierarchy: ExceptionHierarchy::default(),
    };
    validate_external_contract_module(&module)?;
    Ok(module)
}

#[derive(Default)]
struct MixedBindingUseCollector {
    symbol: String,
    direct_calls: usize,
    unsafe_uses: usize,
}

impl Visitor for MixedBindingUseCollector {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if matches!(node.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == self.symbol) {
            self.direct_calls += 1;
            for argument in node.args {
                self.visit_expr(argument);
            }
            for keyword in node.keywords {
                self.visit_expr(keyword.value);
            }
        } else {
            self.generic_visit_expr_call(node);
        }
    }

    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if node.id.as_str() == self.symbol {
            self.unsafe_uses += 1;
        }
    }
}

struct ImpureDirectCallCollector<'a> {
    function_purity: &'a BTreeMap<String, bool>,
    predicate_names: &'a BTreeSet<String>,
    shadowed: &'a BTreeSet<String>,
    offsets: BTreeSet<u32>,
}

impl Visitor for ImpureDirectCallCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if let ast::Expr::Name(name) = node.func.as_ref()
            && !self.shadowed.contains(name.id.as_str())
            && !self.predicate_names.contains(name.id.as_str())
            && self
                .function_purity
                .get(name.id.as_str())
                .is_some_and(|pure| !pure)
        {
            self.offsets.insert(node.range.start().into());
        }
        self.generic_visit_expr_call(node);
    }
}

fn collect_impure_direct_calls(
    expression: &ast::Expr,
    function_purity: &BTreeMap<String, bool>,
    predicate_names: &BTreeSet<String>,
    shadowed: &BTreeSet<String>,
    offsets: &mut BTreeSet<u32>,
) {
    let mut collector = ImpureDirectCallCollector {
        function_purity,
        predicate_names,
        shadowed,
        offsets: BTreeSet::new(),
    };
    collector.visit_expr(expression.clone());
    offsets.extend(collector.offsets);
}

struct RequiredPurityUseCollector<'a> {
    function_purity: &'a BTreeMap<String, bool>,
    predicate_names: &'a BTreeSet<String>,
    shadowed: &'a BTreeSet<String>,
    offsets: BTreeSet<u32>,
}

impl RequiredPurityUseCollector<'_> {
    fn collect(&mut self, expression: &ast::Expr) {
        collect_impure_direct_calls(
            expression,
            self.function_purity,
            self.predicate_names,
            self.shadowed,
            &mut self.offsets,
        );
    }
}

impl Visitor for RequiredPurityUseCollector<'_> {
    fn visit_stmt_while(&mut self, node: ast::StmtWhile) {
        self.collect(&node.test);
        self.generic_visit_stmt_while(node);
    }

    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        const PURE_EXPRESSION_PRIMITIVES: &[&str] = &[
            "Decreases",
            "Ensures",
            "Exsures",
            "Fold",
            "Invariant",
            "Requires",
            "Unfold",
            "Unfolding",
        ];
        if let ast::Expr::Name(name) = node.func.as_ref()
            && PURE_EXPRESSION_PRIMITIVES.contains(&name.id.as_str())
        {
            let arguments = if name.id.as_str() == "Unfolding" {
                node.args.get(1..).unwrap_or_default()
            } else {
                node.args.as_slice()
            };
            for argument in arguments {
                self.collect(argument);
            }
            for keyword in &node.keywords {
                self.collect(&keyword.value);
            }
        }
        self.generic_visit_expr_call(node);
    }
}

fn source_purity_violations(
    declarations: &[&ast::StmtFunctionDef],
    function_purity: &BTreeMap<String, bool>,
) -> BTreeMap<String, BTreeSet<u32>> {
    let predicate_names = declarations
        .iter()
        .filter(|function| {
            function.decorator_list.iter().any(|decorator| {
                matches!(decorator, ast::Expr::Name(name)
                    if name.id.as_str() == "Predicate")
            })
        })
        .map(|function| function.name.to_string())
        .collect::<BTreeSet<_>>();
    let mut violations = BTreeMap::new();
    for function in declarations {
        let mut offsets = BTreeSet::new();
        let mut shadowed = function_local_binding_names(&function.body);
        shadowed.extend(
            function
                .args
                .posonlyargs
                .iter()
                .chain(function.args.args.iter())
                .chain(function.args.kwonlyargs.iter())
                .map(|argument| argument.def.arg.to_string()),
        );
        shadowed.extend(
            function
                .args
                .vararg
                .iter()
                .chain(function.args.kwarg.iter())
                .map(|argument| argument.arg.to_string()),
        );
        if function_purity
            .get(function.name.as_str())
            .is_some_and(|pure| *pure)
        {
            let mut collector = ImpureDirectCallCollector {
                function_purity,
                predicate_names: &predicate_names,
                shadowed: &shadowed,
                offsets: BTreeSet::new(),
            };
            for statement in &function.body {
                collector.visit_stmt(statement.clone());
            }
            offsets.extend(collector.offsets);
        } else {
            let mut collector = RequiredPurityUseCollector {
                function_purity,
                predicate_names: &predicate_names,
                shadowed: &shadowed,
                offsets: BTreeSet::new(),
            };
            for statement in &function.body {
                collector.visit_stmt(statement.clone());
            }
            offsets.extend(collector.offsets);
        }
        if !offsets.is_empty() {
            violations.insert(function.name.to_string(), offsets);
        }
    }
    violations
}

pub(crate) fn collect_source_purity_violations(
    source: &str,
    path: &str,
) -> Result<BTreeMap<String, BTreeSet<u32>>, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    let declarations = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => Some(function),
            _ => None,
        })
        .collect::<Vec<_>>();
    let function_purity = declarations
        .iter()
        .map(|function| {
            (
                function.name.to_string(),
                function.decorator_list.iter().any(|decorator| {
                    matches!(decorator, ast::Expr::Name(name)
                        if name.id.as_str() == "Pure")
                }),
            )
        })
        .collect::<BTreeMap<_, _>>();
    Ok(source_purity_violations(&declarations, &function_purity))
}

/// Require the explicit mixed binding to be imported and exercised only as direct calls. This
/// closes alias/escape paths before the ordinary scalar call binder checks every argument/result.
pub fn validate_mixed_binding_use(
    source: &str,
    path: &str,
    module: &str,
    symbol: &str,
    requested_symbols: &[String],
) -> Result<(), ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    let matching_imports = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import
                        .module
                        .as_ref()
                        .is_some_and(|name| name.as_str() == module) =>
            {
                Some(import)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    if matching_imports.len() != 1
        || matching_imports[0].names.len() != 1
        || matching_imports[0].names[0].name.as_str() != symbol
        || matching_imports[0].names[0].asname.is_some()
    {
        return failure(
            "frontend.python.cross-language.import-mismatch",
            format!(
                "mixed binding requires exactly `from {module} import {symbol}` without aliasing"
            ),
        );
    }
    if requested_symbols.len() != 1 {
        return failure(
            "frontend.python.cross-language.caller-selection",
            "mixed v1 requires exactly one requested Python caller function",
        );
    }
    let selected = requested_symbols[0].as_str();
    let selected_functions = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) if function.name.as_str() == selected => {
                Some(function)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    if selected_functions.len() != 1 {
        return failure(
            "frontend.python.cross-language.caller-selection",
            format!("requested mixed caller {selected:?} must identify one top-level function"),
        );
    }
    let selected_function = selected_functions[0];
    let shadows_binding = selected_function
        .args
        .posonlyargs
        .iter()
        .chain(selected_function.args.args.iter())
        .chain(selected_function.args.kwonlyargs.iter())
        .any(|argument| argument.def.arg.as_str() == symbol)
        || selected_function
            .args
            .vararg
            .as_ref()
            .is_some_and(|argument| argument.arg.as_str() == symbol)
        || selected_function
            .args
            .kwarg
            .as_ref()
            .is_some_and(|argument| argument.arg.as_str() == symbol);
    if shadows_binding {
        return failure(
            "frontend.python.cross-language.binding-shadowed",
            format!("requested caller {selected:?} shadows mixed binding {symbol:?}"),
        );
    }
    let mut collector = MixedBindingUseCollector {
        symbol: symbol.to_owned(),
        ..MixedBindingUseCollector::default()
    };
    for statement in &suite {
        collector.visit_stmt(statement.clone());
    }
    let mut selected_collector = MixedBindingUseCollector {
        symbol: symbol.to_owned(),
        ..MixedBindingUseCollector::default()
    };
    for statement in &selected_function.body {
        selected_collector.visit_stmt(statement.clone());
    }
    if selected_collector.direct_calls == 0 {
        return failure(
            "frontend.python.cross-language.call-missing",
            format!("mixed binding {module}.{symbol} is imported but never called"),
        );
    }
    if collector.unsafe_uses != 0 {
        return failure(
            "frontend.python.cross-language.binding-escape",
            format!("mixed binding {module}.{symbol} escapes a direct call position"),
        );
    }
    Ok(())
}

#[derive(Clone, Debug)]
struct SourceCallEffects {
    value: Term,
    preconditions: Vec<Term>,
    precondition_failure: CallPreconditionFailure,
    postconditions: Vec<Term>,
    exceptional_postconditions: Vec<(String, Vec<Term>)>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CallPreconditionFailure {
    Assertion,
    InsufficientPermission,
}

#[derive(Clone, Debug)]
struct ExpressionLowerer<'a> {
    functions: &'a BTreeMap<String, InlineFunction>,
    globals: &'a BTreeMap<String, Term>,
    type_comments: &'a BTreeMap<u32, ScalarTypeComment>,
    call_stack: Vec<String>,
    exception_hierarchy: &'a ExceptionHierarchy,
    conformance_mode: bool,
}

pub fn verify_contract_module(
    source: &str,
    path: &str,
    requested_symbols: &[String],
) -> Result<ContractVerification, ContractFailure> {
    verify_contract_module_with_imports(source, path, requested_symbols, &[])
}

pub fn verify_contract_module_with_imports(
    source: &str,
    path: &str,
    requested_symbols: &[String],
    imported_modules: &[ImportedContractModule],
) -> Result<ContractVerification, ContractFailure> {
    verify_contract_module_internal(
        source,
        path,
        requested_symbols,
        imported_modules,
        None,
        false,
        ModuleIdentity::entry(path),
    )
}

pub(crate) fn verify_contract_module_for_conformance(
    source: &str,
    path: &str,
    selected_symbols: Option<&BTreeSet<String>>,
) -> Result<ContractVerification, ContractFailure> {
    verify_contract_module_internal(
        source,
        path,
        &[],
        &[],
        selected_symbols,
        true,
        ModuleIdentity::entry(path),
    )
}

pub(crate) fn is_canonical_adt_import_binding(
    absolute: bool,
    module: &str,
    imported_names: &[(String, Option<String>)],
) -> bool {
    absolute && module == "nagini_contracts.adt" && imported_names == [("ADT".to_owned(), None)]
}

fn suite_has_canonical_adt_import(suite: &[ast::Stmt]) -> bool {
    suite.iter().any(|statement| {
        let ast::Stmt::ImportFrom(import) = statement else {
            return false;
        };
        let imported_names = import
            .names
            .iter()
            .map(|alias| {
                (
                    alias.name.to_string(),
                    alias.asname.as_ref().map(ToString::to_string),
                )
            })
            .collect::<Vec<_>>();
        is_canonical_adt_import_binding(
            import.level.is_none_or(|level| level == 0_u32),
            import.module.as_ref().map_or("", |module| module.as_str()),
            &imported_names,
        )
    })
}

fn is_canonical_ellipsis_type_import(import: &ast::StmtImportFrom) -> bool {
    import.level.is_none_or(|level| level == 0_u32)
        && import
            .module
            .as_ref()
            .is_some_and(|module| module.as_str() == "types")
        && matches!(import.names.as_slice(), [alias]
            if alias.name.as_str() == "EllipsisType" && alias.asname.is_none())
}

#[derive(Default)]
struct EllipsisTypeUseCollector {
    found: bool,
}

impl Visitor for EllipsisTypeUseCollector {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if node.id.as_str() == "EllipsisType" {
            self.found = true;
        }
    }
}

fn validate_ellipsis_singleton_bindings(suite: &[ast::Stmt]) -> Result<(), ContractFailure> {
    let import_count = suite
        .iter()
        .filter(|statement| {
            matches!(statement, ast::Stmt::ImportFrom(import)
                if is_canonical_ellipsis_type_import(import))
        })
        .count();
    if import_count == 0 {
        let mut collector = EllipsisTypeUseCollector::default();
        for statement in suite {
            collector.visit_stmt(statement.clone());
            if let ast::Stmt::FunctionDef(function) = statement {
                for argument in function
                    .args
                    .posonlyargs
                    .iter()
                    .chain(function.args.args.iter())
                    .chain(function.args.kwonlyargs.iter())
                {
                    if let Some(annotation) = argument.def.annotation.as_deref() {
                        collector.visit_expr(annotation.clone());
                    }
                }
                for argument in function
                    .args
                    .vararg
                    .iter()
                    .chain(function.args.kwarg.iter())
                {
                    if let Some(annotation) = argument.annotation.as_deref() {
                        collector.visit_expr(annotation.clone());
                    }
                }
                if let Some(annotation) = function.returns.as_deref() {
                    collector.visit_expr(annotation.clone());
                }
            }
        }
        if collector.found {
            return failure(
                "frontend.python.contracts.ellipsis-type-import-required",
                "EllipsisType annotations and runtime checks require `from types import EllipsisType`",
            );
        }
        return Ok(());
    }
    if import_count != 1 || scalar_module_binding_count_for_suite(suite, "EllipsisType") != 1 {
        return failure(
            "frontend.python.contracts.ellipsis-import-collision",
            "EllipsisType semantics require exactly one canonical unaliased import binding",
        );
    }
    for protected in ["Ellipsis", "type", "isinstance"] {
        if scalar_module_binding_count_for_suite(suite, protected) != 0 {
            return failure(
                "frontend.python.contracts.ellipsis-binding-shadowed",
                format!("Ellipsis singleton semantics require unshadowed builtin {protected:?}"),
            );
        }
    }
    for function in suite.iter().filter_map(|statement| match statement {
        ast::Stmt::FunctionDef(function) => Some(function),
        _ => None,
    }) {
        let parameter_names = function
            .args
            .posonlyargs
            .iter()
            .chain(function.args.args.iter())
            .chain(function.args.kwonlyargs.iter())
            .map(|argument| argument.def.arg.as_str())
            .chain(
                function
                    .args
                    .vararg
                    .iter()
                    .map(|argument| argument.arg.as_str()),
            )
            .chain(
                function
                    .args
                    .kwarg
                    .iter()
                    .map(|argument| argument.arg.as_str()),
            );
        let local_names = function_local_binding_names(&function.body);
        if let Some(shadowed) = parameter_names
            .chain(local_names.iter().map(String::as_str))
            .find(|name| matches!(*name, "Ellipsis" | "EllipsisType" | "type" | "isinstance"))
        {
            return failure(
                "frontend.python.contracts.ellipsis-binding-shadowed",
                format!(
                    "function {:?} shadows Ellipsis semantic binding {shadowed:?}",
                    function.name
                ),
            );
        }
    }
    Ok(())
}

fn scalar_module_binding_count_for_suite(suite: &[ast::Stmt], expected: &str) -> usize {
    suite
        .iter()
        .map(|statement| scalar_module_binding_count(statement, expected))
        .sum()
}

fn verify_contract_module_internal(
    source: &str,
    path: &str,
    requested_symbols: &[String],
    imported_modules: &[ImportedContractModule],
    selected_symbols: Option<&BTreeSet<String>>,
    conformance_mode: bool,
    module_identity: ModuleIdentity,
) -> Result<ContractVerification, ContractFailure> {
    let type_comments = collect_scalar_type_comments(source)?;
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    if imported_modules.is_empty()
        && let Some(shape) = closed_recursive_termination_module(&suite)
    {
        return verify_closed_recursive_termination_module(&shape, path, source, requested_symbols);
    }
    validate_ellipsis_singleton_bindings(&suite)?;
    validate_passive_scalar_class_bindings(&suite)?;
    if !suite_has_canonical_adt_import(&suite) {
        validate_scalar_class_declaration_islands(&suite, source, selected_symbols)?;
    }
    let mut exception_hierarchy = resolve_exception_hierarchy(&suite, imported_modules)?;
    let mut assignment_lines = std::collections::BTreeSet::new();
    for statement in &suite {
        collect_assignment_lines(
            std::slice::from_ref(statement),
            source,
            &mut assignment_lines,
        );
    }
    if let Some(line) = type_comments
        .keys()
        .find(|line| !assignment_lines.contains(line))
    {
        return failure(
            "frontend.python.contracts.type-comment-location",
            format!("scalar type comment on line {line} is not attached to an assignment"),
        );
    }
    let mut declarations = Vec::new();
    let mut imported_external_functions = BTreeMap::new();
    let imported_modules = imported_modules
        .iter()
        .map(|module| (module.module.as_str(), module))
        .collect::<BTreeMap<_, _>>();
    let mut used_external_modules = std::collections::BTreeSet::new();
    let mut functions = Vec::new();
    let mut obligations = Vec::new();
    for statement in &suite {
        match statement {
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import
                        .module
                        .as_ref()
                        .is_some_and(|module| module.as_str() == "nagini_contracts.contracts") => {}
            ast::Stmt::ImportFrom(import)
                if is_canonical_obligations_star_import(import)
                    && suite_has_only_supported_closed_termination_contracts(&suite) =>
            {
                // `MustTerminate` is consumed only by the closed ranking-function proof below.
            }
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import
                        .module
                        .as_ref()
                        .is_some_and(|module| module.as_str() == "typing") =>
            {
                // The scalar fragment resolves annotations itself. Imported typing names are
                // accepted at module scope, but using an unsupported annotation still refuses in
                // `annotation_sort`, and using one as a runtime value still refuses in lowering.
            }
            ast::Stmt::ImportFrom(import) if is_canonical_ellipsis_type_import(import) => {
                // `types.EllipsisType` is a CPython-defined type object. The source-bound
                // singleton/type bindings are installed below only for this exact import shape.
            }
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import
                        .module
                        .as_ref()
                        .is_some_and(|module| imported_modules.contains_key(module.as_str())) =>
            {
                let module_name = import
                    .module
                    .as_ref()
                    .expect("guard established external module")
                    .as_str();
                let contract = imported_modules[module_name];
                used_external_modules.insert(module_name.to_owned());
                for alias in &import.names {
                    let imported_name = alias.name.as_str();
                    if imported_name == "*" {
                        for (exported_name, summary) in &contract.functions {
                            if exported_name.starts_with('_') {
                                continue;
                            }
                            if imported_external_functions
                                .insert(exported_name.clone(), summary.clone())
                                .is_some()
                            {
                                return failure(
                                    "frontend.python.contract-import.import-collision",
                                    format!(
                                        "star import from {module_name:?} collides at local name {exported_name:?}"
                                    ),
                                );
                            }
                        }
                        continue;
                    }
                    let local_name = alias
                        .asname
                        .as_ref()
                        .map_or(imported_name, |name| name.as_str());
                    if let Some(summary) = contract.functions.get(imported_name) {
                        if imported_external_functions
                            .insert(local_name.to_owned(), summary.clone())
                            .is_some()
                        {
                            return failure(
                                "frontend.python.contract-import.import-collision",
                                format!("multiple contract imports bind local name {local_name:?}"),
                            );
                        }
                    } else if contract
                        .exception_hierarchy
                        .parents
                        .contains_key(imported_name)
                    {
                        if local_name != imported_name {
                            return failure(
                                "frontend.python.contract-import.exception-alias-unsupported",
                                "exception type aliases require canonical type-identity mapping",
                            );
                        }
                        exception_hierarchy.import_visible(imported_name)?;
                    } else {
                        return failure(
                            "frontend.python.contract-import.symbol-missing",
                            format!(
                                "contract module {module_name:?} does not declare imported symbol {imported_name:?}"
                            ),
                        );
                    }
                }
            }
            ast::Stmt::FunctionDef(function) => {
                declarations.push(function);
            }
            ast::Stmt::Assign(assignment)
                if assignment.type_comment.is_none()
                    && matches!(
                        assignment.targets.as_slice(),
                        [ast::Expr::Name(_) | ast::Expr::Tuple(_) | ast::Expr::List(_)]
                    ) => {}
            ast::Stmt::AnnAssign(assignment)
                if assignment.value.is_some()
                    && matches!(assignment.target.as_ref(), ast::Expr::Name(_)) => {}
            ast::Stmt::AugAssign(assignment)
                if matches!(assignment.target.as_ref(), ast::Expr::Name(name)
                    if is_protected_module_metadata(name.id.as_str())) => {}
            ast::Stmt::AugAssign(assignment)
                if closed_module_int_augassign(&suite, assignment).is_some() =>
            {
                let (binding, _) = closed_module_int_augassign(&suite, assignment)
                    .expect("guard established closed module int update");
                validate_closed_module_int_update_ownership(&suite, &binding)?;
            }
            ast::Stmt::AugAssign(assignment) => {
                validate_module_list_augassign_shape(&suite, assignment)?;
            }
            ast::Stmt::Assert(_) => {}
            ast::Stmt::Try(try_statement) => {
                validate_closed_module_countdown_try(try_statement)?;
            }
            ast::Stmt::ClassDef(class)
                if exception_hierarchy
                    .parents
                    .contains_key(class.name.as_str()) => {}
            ast::Stmt::ClassDef(class) if is_supported_scalar_class(class) => {
                // A no-base marker executes no user expression and remains absent from the scalar
                // value environment. A pass-only subclass of canonical builtin `int` additionally
                // receives the exact inherited numeric constructor summary installed below. A
                // declaration island is admitted only after proving that its declaration-time
                // expressions are inert and selected scalar code is independent of the class; it
                // receives no constructor, field, type, or method summary.
            }
            statement if is_inert_string_statement(statement) => {
                // Evaluating a literal string expression is total and has no application-visible
                // effect, whether Python records it as a leading docstring or discards it as a
                // later standalone expression.
            }
            ast::Stmt::Expr(expression)
                if closed_module_list_append_call(&suite, &expression.value).is_some() =>
            {
                // A closed source-owned global list append call is executed in module order by
                // `derive_immutable_module_globals` after its no-alias shape is revalidated.
            }
            ast::Stmt::Expr(expression)
                if closed_module_int_update_call(&suite, &expression.value).is_some() =>
            {
                let shape = closed_module_int_update_call(&suite, &expression.value)
                    .expect("guard established closed module int update call");
                validate_closed_module_int_update_ownership(&suite, &shape.binding)?;
            }
            ast::Stmt::Expr(expression)
                if closed_module_folded_int_update(&suite).is_some_and(|shape| {
                    is_closed_module_fold_call(&expression.value, &shape)
                        || is_closed_module_folded_int_call(&expression.value, &shape)
                }) =>
            {
                let shape = closed_module_folded_int_update(&suite)
                    .expect("guard established folded module int protocol");
                validate_closed_module_folded_int_ownership(&suite, &shape)?;
            }
            ast::Stmt::Expr(expression)
                if conformance_mode && is_conformance_literal_print(&expression.value) =>
            {
                // Nagini's fixture harness verifies selected callable bodies independently of
                // module-initialization effects. Preserve that comparison behavior only inside
                // the pinned conformance entry point. Production verification (where
                // `selected_symbols` is `None`) still refuses every executable module statement.
            }
            _ => {
                return failure(
                    "frontend.python.contracts.module-statement-unsupported",
                    format!("unsupported module statement: {statement:?}"),
                );
            }
        }
    }
    for module in imported_modules.keys() {
        if !used_external_modules.contains(*module) {
            return failure(
                "frontend.python.contract-import.module-unused",
                format!("contract module {module:?} is not imported by source {path:?}"),
            );
        }
    }
    let expanded_selected =
        selected_symbols.map(|selected| expand_revealed_selection(&declarations, selected));
    let selected_symbols = expanded_selected.as_ref();
    let folded_predicates = closed_module_folded_int_update(&suite)
        .map(|shape| BTreeSet::from([shape.predicate]))
        .unwrap_or_default();
    let mut inline_functions = build_inline_functions(
        &declarations,
        &exception_hierarchy,
        selected_symbols,
        &folded_predicates,
    )?;
    install_scalar_int_subclass_constructors(&suite, &mut inline_functions)?;
    for (name, summary) in imported_external_functions {
        if inline_functions.insert(name.clone(), summary).is_some() {
            return failure(
                "frontend.python.contract-import.import-collision",
                format!("contract import shadows source function {name:?}"),
            );
        }
    }
    let function_purity = inline_functions
        .iter()
        .map(|(name, summary)| (name.clone(), summary.pure))
        .collect::<BTreeMap<_, _>>();
    let purity_violations = source_purity_violations(&declarations, &function_purity);
    let has_selected_purity_violation = purity_violations
        .keys()
        .any(|name| selected_symbols.is_none_or(|selected| selected.contains(name.as_str())));
    let module_globals = derive_immutable_module_globals(
        &suite,
        ModuleDerivationContext {
            source,
            path,
            functions: &inline_functions,
            type_comments: &type_comments,
            exception_hierarchy: &exception_hierarchy,
            conformance_mode,
            identity: &module_identity,
        },
    )?;
    validate_module_list_mutation_records(&module_globals)?;
    if let Some(failure) = &module_globals.initialization_failure {
        let (line, column) = source_location(source, failure.byte_offset);
        obligations.push(
            discharge(&Obligation {
                id: format!("module:undefined-call:{}", failure.binding),
                expectation: ObligationExpectation::Prove,
                assumptions: Vec::new(),
                conclusion: Term::Bool { value: false },
                path: path.to_owned(),
                byte_offset: failure.byte_offset,
                line,
                column,
            })
            .map_err(|message| ContractFailure {
                code: "solver.translation-failed",
                message,
            })?,
        );
    }
    for obligation in &module_globals.obligations {
        obligations.push(discharge(obligation).map_err(|message| ContractFailure {
            code: "solver.translation-failed",
            message,
        })?);
    }
    let global_environment = &module_globals.values;
    for function in declarations {
        if selected_symbols.is_some_and(|selected| !selected.contains(function.name.as_str())) {
            continue;
        }
        if has_selected_purity_violation {
            functions.push(function.name.to_string());
            if let Some(offsets) = purity_violations.get(function.name.as_str()) {
                for (index, byte_offset) in offsets.iter().enumerate() {
                    let (line, column) = source_location(source, *byte_offset);
                    obligations.push(
                        discharge(&Obligation {
                            id: format!("{}:purity-violation:{index}", function.name),
                            expectation: ObligationExpectation::Prove,
                            assumptions: Vec::new(),
                            conclusion: Term::Bool { value: false },
                            path: path.to_owned(),
                            byte_offset: *byte_offset,
                            line,
                            column,
                        })
                        .map_err(|message| ContractFailure {
                            code: "solver.translation-failed",
                            message,
                        })?,
                    );
                }
            }
            continue;
        }
        if let Some(shape) = closed_termination_loop(function) {
            functions.push(function.name.to_string());
            for obligation in lower_closed_termination_loop(&shape, path, source) {
                obligations.push(discharge(&obligation).map_err(|message| ContractFailure {
                    code: "solver.translation-failed",
                    message,
                })?);
            }
            continue;
        }
        if let Some(shape) = closed_vacuous_termination_loop(function) {
            functions.push(function.name.to_string());
            obligations.push(
                discharge(&lower_closed_vacuous_termination_loop(&shape, path, source)).map_err(
                    |message| ContractFailure {
                        code: "solver.translation-failed",
                        message,
                    },
                )?,
            );
            continue;
        }
        if let Some(shape) = closed_vacuous_termination_precondition(function) {
            functions.push(function.name.to_string());
            obligations.push(
                discharge(&lower_closed_vacuous_termination_precondition(
                    &shape, path, source,
                ))
                .map_err(|message| ContractFailure {
                    code: "solver.translation-failed",
                    message,
                })?,
            );
            continue;
        }
        if let Some(closed_float_obligations) =
            lower_closed_float_literal_function(function, path, source)?
        {
            functions.push(function.name.to_string());
            for obligation in closed_float_obligations {
                obligations.push(discharge(&obligation).map_err(|message| ContractFailure {
                    code: "solver.translation-failed",
                    message,
                })?);
            }
            continue;
        }
        let folded_int_function = closed_module_folded_int_update(&suite).is_some_and(|shape| {
            matches!(function.name.as_str(), name
                if name == shape.predicate || name == shape.getter || name == shape.updater)
        });
        if closed_module_list_append_function(function).is_some()
            || closed_module_int_update_function(function).is_some()
            || folded_int_function
        {
            functions.push(function.name.to_string());
            continue;
        }
        let lowered = lower_function(
            function,
            path,
            source,
            &inline_functions,
            &type_comments,
            global_environment,
            &exception_hierarchy,
            conformance_mode,
        )?;
        functions.push(function.name.to_string());
        for obligation in lowered.specification_safety {
            let result = discharge(&obligation).map_err(|message| ContractFailure {
                code: "solver.translation-failed",
                message,
            })?;
            if !result.satisfied() {
                return failure(
                    "frontend.python.contracts.partial-operation-in-spec",
                    format!(
                        "function precondition contains a partial runtime operation whose safety is not established by its evaluation guards and preceding preconditions at line {}, column {}",
                        result.line, result.column
                    ),
                );
            }
            obligations.push(result);
        }
        for obligation in lowered.obligations {
            obligations.push(discharge(&obligation).map_err(|message| ContractFailure {
                code: "solver.translation-failed",
                message,
            })?);
        }
    }
    for symbol in requested_symbols {
        if !functions.contains(symbol) {
            return failure(
                "frontend.python.symbol.missing",
                format!("requested symbol {symbol:?} is not a verified function"),
            );
        }
    }
    let passed = obligations.iter().all(ObligationResult::satisfied);
    Ok(ContractVerification {
        schema: "maledictus-python-contract-verification/v1".to_owned(),
        path: path.to_owned(),
        functions,
        obligations,
        passed,
    })
}

fn scalar_class_has_inert_body(class: &ast::StmtClassDef) -> bool {
    class.keywords.is_empty()
        && class.decorator_list.is_empty()
        && class.type_params.is_empty()
        && has_inert_class_body(&class.body)
}

fn has_inert_class_body(body: &[ast::Stmt]) -> bool {
    let body = if body.first().is_some_and(is_inert_string_statement) {
        &body[1..]
    } else {
        body
    };
    matches!(body, [] | [ast::Stmt::Pass(_)])
}

fn is_passive_scalar_class(class: &ast::StmtClassDef) -> bool {
    class.bases.is_empty() && scalar_class_has_inert_body(class)
}

fn is_scalar_int_subclass(class: &ast::StmtClassDef) -> bool {
    scalar_class_has_inert_body(class)
        && matches!(class.bases.as_slice(), [ast::Expr::Name(base)] if base.id.as_str() == "int")
}

fn is_inert_scalar_method_annotation(annotation: Option<&ast::Expr>) -> bool {
    match annotation {
        None => true,
        Some(ast::Expr::Name(name)) => matches!(
            name.id.as_str(),
            "bool" | "bytes" | "int" | "object" | "str"
        ),
        Some(ast::Expr::Constant(constant)) => matches!(constant.value, ast::Constant::None),
        Some(_) => false,
    }
}

fn is_inert_scalar_method_declaration(function: &ast::StmtFunctionDef) -> bool {
    function.decorator_list.is_empty()
        && function.type_params.is_empty()
        && function
            .args
            .posonlyargs
            .iter()
            .chain(function.args.args.iter())
            .chain(function.args.kwonlyargs.iter())
            .all(|argument| {
                argument.default.is_none()
                    && is_inert_scalar_method_annotation(argument.def.annotation.as_deref())
            })
        && function.args.vararg.as_deref().is_none_or(|argument| {
            is_inert_scalar_method_annotation(argument.annotation.as_deref())
        })
        && function.args.kwarg.as_deref().is_none_or(|argument| {
            is_inert_scalar_method_annotation(argument.annotation.as_deref())
        })
        && is_inert_scalar_method_annotation(function.returns.as_deref())
}

fn is_scalar_class_declaration_island(class: &ast::StmtClassDef) -> bool {
    if !class.bases.is_empty()
        || !class.keywords.is_empty()
        || !class.decorator_list.is_empty()
        || !class.type_params.is_empty()
    {
        return false;
    }
    let body = if class.body.first().is_some_and(is_inert_string_statement) {
        &class.body[1..]
    } else {
        class.body.as_slice()
    };
    let mut method_count = 0;
    for statement in body {
        match statement {
            ast::Stmt::FunctionDef(function) if is_inert_scalar_method_declaration(function) => {
                method_count += 1;
            }
            statement if is_inert_string_statement(statement) => {}
            ast::Stmt::Pass(_) => {}
            _ => return false,
        }
    }
    method_count != 0
}

fn is_supported_scalar_class(class: &ast::StmtClassDef) -> bool {
    is_passive_scalar_class(class)
        || is_scalar_int_subclass(class)
        || is_scalar_class_declaration_island(class)
}

#[derive(Default)]
struct ScalarClassDependencyCollector {
    names: BTreeSet<String>,
}

impl Visitor for ScalarClassDependencyCollector {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        self.names.insert(node.id.to_string());
    }
}

fn class_source_contains_expected_output(
    source: &str,
    class: &ast::StmtClassDef,
) -> Result<bool, ContractFailure> {
    crate::conformance::source_range_has_expected_output_annotation(
        source,
        class.range.start().into(),
        class.range.end().into(),
    )
    .map_err(|message| ContractFailure {
        code: "frontend.python.contracts.class-declaration-island-diagnostic-unsupported",
        message,
    })
}

fn validate_scalar_class_declaration_islands(
    suite: &[ast::Stmt],
    source: &str,
    selected_symbols: Option<&BTreeSet<String>>,
) -> Result<(), ContractFailure> {
    let islands = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ClassDef(class) if is_scalar_class_declaration_island(class) => Some(class),
            _ => None,
        })
        .collect::<Vec<_>>();
    if islands.is_empty() {
        return Ok(());
    }

    if islands
        .iter()
        .map(|class| class_source_contains_expected_output(source, class))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .any(|contains_annotation| contains_annotation)
    {
        return failure(
            "frontend.python.contracts.class-declaration-island-diagnostic-unsupported",
            "an unowned class declaration contains an expected verifier diagnostic",
        );
    }

    let declarations = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => Some((function.name.as_str(), function)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let class_names = islands
        .iter()
        .map(|class| class.name.to_string())
        .collect::<BTreeSet<_>>();
    let method_names = islands
        .iter()
        .flat_map(|class| {
            class.body.iter().filter_map(|statement| match statement {
                ast::Stmt::FunctionDef(function) => Some(function.name.to_string()),
                _ => None,
            })
        })
        .collect::<BTreeSet<_>>();

    if selected_symbols.is_some_and(|selected| {
        selected
            .iter()
            .any(|name| class_names.contains(name) || method_names.contains(name))
    }) {
        return failure(
            "frontend.python.contracts.class-declaration-island-selected",
            "the selected target names a class or method that the scalar frontend does not own",
        );
    }

    let mut reachable = selected_symbols.map_or_else(
        || declarations.keys().map(|name| name.to_string()).collect(),
        |selected| {
            selected
                .iter()
                .filter(|name| declarations.contains_key(name.as_str()))
                .cloned()
                .collect::<BTreeSet<_>>()
        },
    );
    if reachable.is_empty() {
        return failure(
            "frontend.python.contracts.class-declaration-island-unowned",
            "a class declaration island requires at least one independently analyzed scalar function",
        );
    }

    let mut checked = BTreeSet::new();
    while let Some(name) = reachable
        .iter()
        .find(|name| !checked.contains(*name))
        .cloned()
    {
        checked.insert(name.clone());
        let function = declarations
            .get(name.as_str())
            .expect("reachable names originate from source declarations");
        let mut collector = ScalarClassDependencyCollector::default();
        for decorator in &function.decorator_list {
            collector.visit_expr(decorator.clone());
        }
        for argument in function
            .args
            .posonlyargs
            .iter()
            .chain(function.args.args.iter())
            .chain(function.args.kwonlyargs.iter())
        {
            if let Some(annotation) = argument.def.annotation.as_deref() {
                collector.visit_expr(annotation.clone());
            }
            if let Some(default) = argument.default.as_deref() {
                collector.visit_expr(default.clone());
            }
        }
        for argument in function
            .args
            .vararg
            .iter()
            .chain(function.args.kwarg.iter())
        {
            if let Some(annotation) = argument.annotation.as_deref() {
                collector.visit_expr(annotation.clone());
            }
        }
        if let Some(annotation) = function.returns.as_deref() {
            collector.visit_expr(annotation.clone());
        }
        for statement in &function.body {
            collector.visit_stmt(statement.clone());
        }
        if let Some(class_name) = collector
            .names
            .iter()
            .find(|name| class_names.contains(*name))
        {
            return failure(
                "frontend.python.contracts.class-declaration-island-dependency",
                format!(
                    "scalar function {:?} depends on unowned class {class_name:?}",
                    function.name
                ),
            );
        }
        reachable.extend(
            collector
                .names
                .into_iter()
                .filter(|referenced| declarations.contains_key(referenced.as_str())),
        );
    }
    Ok(())
}

fn install_scalar_int_subclass_constructors(
    suite: &[ast::Stmt],
    functions: &mut BTreeMap<String, InlineFunction>,
) -> Result<(), ContractFailure> {
    for class in suite.iter().filter_map(|statement| match statement {
        ast::Stmt::ClassDef(class) if is_scalar_int_subclass(class) => Some(class),
        _ => None,
    }) {
        let constructor = InlineFunction {
            positional_parameters: vec![InlineParameter {
                name: "value".to_owned(),
                sort: Sort::Int,
                default: None,
                positional_only: true,
            }],
            keyword_only_parameters: Vec::new(),
            var_args: None,
            keyword_args: None,
            return_sort: Sort::Int,
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            exceptional_postconditions: Vec::new(),
            expression: None,
            modular_call: false,
            pure: true,
            ghost: false,
            captured_environment: Some(BTreeMap::new()),
            scalar_identity_result: Some("value".to_owned()),
        };
        if functions
            .insert(class.name.to_string(), constructor)
            .is_some()
        {
            return failure(
                "frontend.python.contracts.passive-class-binding-shadowed",
                format!(
                    "scalar int subclass name {:?} collides with another callable",
                    class.name
                ),
            );
        }
    }
    Ok(())
}

#[derive(Clone, Debug)]
struct ClosedModuleListAppend {
    function: String,
    binding: String,
    value: i64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClosedModuleIntUpdate {
    function: String,
    binding: String,
    minimum: i64,
    increment: i64,
    returns_permission: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClosedModuleFoldedIntUpdate {
    binding: String,
    predicate: String,
    getter: String,
    updater: String,
    maximum: i64,
    increment: i64,
}

fn direct_contract_argument<'a>(statement: &'a ast::Stmt, contract: &str) -> Option<&'a ast::Expr> {
    let ast::Stmt::Expr(expression) = statement else {
        return None;
    };
    let ast::Expr::Call(call) = expression.value.as_ref() else {
        return None;
    };
    matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == contract)
        .then_some(())?;
    (call.args.len() == 1 && call.keywords.is_empty()).then(|| &call.args[0])
}

fn is_acc_list_predicate(expression: &ast::Expr, binding: &str) -> bool {
    let ast::Expr::Call(acc) = expression else {
        return false;
    };
    if acc.args.len() != 1
        || !acc.keywords.is_empty()
        || !matches!(acc.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Acc")
    {
        return false;
    }
    let ast::Expr::Call(predicate) = &acc.args[0] else {
        return false;
    };
    predicate.args.len() == 1
        && predicate.keywords.is_empty()
        && matches!(predicate.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "list_pred")
        && matches!(predicate.args.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == binding)
}

fn is_list_append_length_postcondition(expression: &ast::Expr, binding: &str) -> bool {
    let ast::Expr::Compare(comparison) = expression else {
        return false;
    };
    let [ast::CmpOp::Eq] = comparison.ops.as_slice() else {
        return false;
    };
    let [right] = comparison.comparators.as_slice() else {
        return false;
    };
    let is_length = |expression: &ast::Expr| {
        matches!(expression, ast::Expr::Call(call)
            if call.args.len() == 1
                && call.keywords.is_empty()
                && matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "len")
                && matches!(call.args.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == binding))
    };
    if !is_length(&comparison.left) {
        return false;
    }
    let ast::Expr::BinOp(increment) = right else {
        return false;
    };
    if !matches!(increment.op, ast::Operator::Add)
        || constant_tuple_index(&increment.right) != Some(1)
    {
        return false;
    }
    let ast::Expr::Call(old) = increment.left.as_ref() else {
        return false;
    };
    old.args.len() == 1
        && old.keywords.is_empty()
        && matches!(old.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Old")
        && old.args.first().is_some_and(is_length)
}

fn closed_module_list_append_function(
    function: &ast::StmtFunctionDef,
) -> Option<ClosedModuleListAppend> {
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || !function.args.posonlyargs.is_empty()
        || !function.args.args.is_empty()
        || function.args.vararg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function.args.kwarg.is_some()
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Constant(constant)) if matches!(constant.value, ast::Constant::None))
    {
        return None;
    }
    let [
        requires,
        permission_postcondition,
        length_postcondition,
        body,
    ] = function.body.as_slice()
    else {
        return None;
    };
    direct_contract_argument(requires, "Requires")?;
    let permission_postcondition = direct_contract_argument(permission_postcondition, "Ensures")?;
    let length_postcondition = direct_contract_argument(length_postcondition, "Ensures")?;
    let ast::Stmt::Expr(body) = body else {
        return None;
    };
    let ast::Expr::Call(append) = body.value.as_ref() else {
        return None;
    };
    if append.args.len() != 1 || !append.keywords.is_empty() {
        return None;
    }
    let ast::Expr::Attribute(method) = append.func.as_ref() else {
        return None;
    };
    let ast::Expr::Name(binding) = method.value.as_ref() else {
        return None;
    };
    if method.attr.as_str() != "append"
        || !is_acc_list_predicate(permission_postcondition, binding.id.as_str())
        || !is_list_append_length_postcondition(length_postcondition, binding.id.as_str())
    {
        return None;
    }
    let value = closed_module_int_literal(&append.args[0], "closed module list append").ok()?;
    Some(ClosedModuleListAppend {
        function: function.name.to_string(),
        binding: binding.id.to_string(),
        value,
    })
}

fn closed_module_list_append_call(
    suite: &[ast::Stmt],
    expression: &ast::Expr,
) -> Option<ClosedModuleListAppend> {
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    if !call.args.is_empty() || !call.keywords.is_empty() {
        return None;
    }
    let ast::Expr::Name(callee) = call.func.as_ref() else {
        return None;
    };
    suite.iter().find_map(|statement| match statement {
        ast::Stmt::FunctionDef(function) if function.name == callee.id => {
            closed_module_list_append_function(function)
        }
        _ => None,
    })
}

fn is_acc_module_global(expression: &ast::Expr, binding: &str) -> bool {
    let ast::Expr::Call(call) = expression else {
        return false;
    };
    call.args.len() == 1
        && call.keywords.is_empty()
        && matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Acc")
        && matches!(call.args.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == binding)
}

fn module_int_permission_precondition(expression: &ast::Expr, binding: &str) -> Option<i64> {
    let ast::Expr::BoolOp(conjunction) = expression else {
        return None;
    };
    let [permission, lower_bound] = conjunction.values.as_slice() else {
        return None;
    };
    if conjunction.op != ast::BoolOp::And || !is_acc_module_global(permission, binding) {
        return None;
    }
    let ast::Expr::Compare(comparison) = lower_bound else {
        return None;
    };
    let [ast::CmpOp::GtE] = comparison.ops.as_slice() else {
        return None;
    };
    let [minimum] = comparison.comparators.as_slice() else {
        return None;
    };
    if !matches!(comparison.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binding) {
        return None;
    }
    closed_module_int_literal(minimum, "closed module int update lower bound").ok()
}

fn is_module_int_update_postcondition(
    expression: &ast::Expr,
    binding: &str,
    increment: i64,
) -> bool {
    let ast::Expr::BoolOp(conjunction) = expression else {
        return false;
    };
    let [permission, equality] = conjunction.values.as_slice() else {
        return false;
    };
    if conjunction.op != ast::BoolOp::And || !is_acc_module_global(permission, binding) {
        return false;
    }
    let ast::Expr::Compare(comparison) = equality else {
        return false;
    };
    let [ast::CmpOp::Eq] = comparison.ops.as_slice() else {
        return false;
    };
    let [right] = comparison.comparators.as_slice() else {
        return false;
    };
    if !matches!(comparison.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binding) {
        return false;
    }
    let ast::Expr::BinOp(addition) = right else {
        return false;
    };
    if addition.op != ast::Operator::Add
        || closed_module_int_literal(&addition.right, "closed module int update postcondition").ok()
            != Some(increment)
    {
        return false;
    }
    let ast::Expr::Call(old) = addition.left.as_ref() else {
        return false;
    };
    old.args.len() == 1
        && old.keywords.is_empty()
        && matches!(old.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Old")
        && matches!(old.args.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == binding)
}

fn closed_module_int_update_function(
    function: &ast::StmtFunctionDef,
) -> Option<ClosedModuleIntUpdate> {
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || !function.args.posonlyargs.is_empty()
        || !function.args.args.is_empty()
        || function.args.vararg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function.args.kwarg.is_some()
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == "int")
        || !matches!(function.body.len(), 4 | 5)
    {
        return None;
    }

    let ast::Stmt::Global(global) = &function.body[0] else {
        return None;
    };
    let ast::Stmt::AugAssign(update) = &function.body[function.body.len() - 2] else {
        return None;
    };
    let ast::Expr::Name(binding) = update.target.as_ref() else {
        return None;
    };
    if global.names.len() != 1 || global.names[0] != binding.id || update.op != ast::Operator::Add {
        return None;
    }
    let increment =
        closed_module_int_literal(&update.value, "closed module int update increment").ok()?;
    if increment <= 0 {
        return None;
    }
    let ast::Stmt::Return(returned) = &function.body[function.body.len() - 1] else {
        return None;
    };
    if !matches!(returned.value.as_deref(), Some(ast::Expr::Name(name)) if name.id == binding.id) {
        return None;
    }
    let minimum = module_int_permission_precondition(
        direct_contract_argument(&function.body[1], "Requires")?,
        binding.id.as_str(),
    )?;
    let returns_permission = function.body.len() == 5;
    if returns_permission
        && !is_module_int_update_postcondition(
            direct_contract_argument(&function.body[2], "Ensures")?,
            binding.id.as_str(),
            increment,
        )
    {
        return None;
    }
    Some(ClosedModuleIntUpdate {
        function: function.name.to_string(),
        binding: binding.id.to_string(),
        minimum,
        increment,
        returns_permission,
    })
}

fn closed_module_int_update_call(
    suite: &[ast::Stmt],
    expression: &ast::Expr,
) -> Option<ClosedModuleIntUpdate> {
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    if !call.args.is_empty() || !call.keywords.is_empty() {
        return None;
    }
    let ast::Expr::Name(callee) = call.func.as_ref() else {
        return None;
    };
    suite.iter().find_map(|statement| match statement {
        ast::Stmt::FunctionDef(function) if function.name == callee.id => {
            closed_module_int_update_function(function)
        }
        _ => None,
    })
}

fn closed_module_int_augassign(
    suite: &[ast::Stmt],
    assignment: &ast::StmtAugAssign,
) -> Option<(String, i64)> {
    let ast::Expr::Name(binding) = assignment.target.as_ref() else {
        return None;
    };
    if assignment.op != ast::Operator::Add {
        return None;
    }
    let increment =
        closed_module_int_literal(&assignment.value, "closed module int initializer update")
            .ok()?;
    (increment > 0
        && suite.iter().any(|statement| {
            matches!(statement, ast::Stmt::FunctionDef(function)
                if closed_module_int_update_function(function)
                    .is_some_and(|shape| shape.binding.as_str() == binding.id.as_str()))
        }))
    .then(|| (binding.id.to_string(), increment))
}

fn is_half_fraction(expression: &ast::Expr) -> bool {
    matches!(expression, ast::Expr::BinOp(fraction)
        if fraction.op == ast::Operator::Div
            && closed_module_int_literal(&fraction.left, "half-permission numerator").ok() == Some(1)
            && closed_module_int_literal(&fraction.right, "half-permission denominator").ok() == Some(2))
}

fn is_acc_module_global_half(expression: &ast::Expr, binding: &str) -> bool {
    let ast::Expr::Call(call) = expression else {
        return false;
    };
    call.args.len() == 2
        && call.keywords.is_empty()
        && matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Acc")
        && matches!(&call.args[0], ast::Expr::Name(name) if name.id.as_str() == binding)
        && is_half_fraction(&call.args[1])
}

fn is_zero_argument_named_call(expression: &ast::Expr, expected: &str) -> bool {
    matches!(expression, ast::Expr::Call(call)
        if call.args.is_empty()
            && call.keywords.is_empty()
            && matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == expected))
}

fn direct_zero_argument_contract_call(statement: &ast::Stmt, contract: &str, callee: &str) -> bool {
    direct_contract_argument(statement, contract)
        .is_some_and(|argument| is_zero_argument_named_call(argument, callee))
}

fn folded_int_predicate_function(function: &ast::StmtFunctionDef) -> Option<(String, String)> {
    if !function.type_params.is_empty()
        || !function.args.posonlyargs.is_empty()
        || !function.args.args.is_empty()
        || function.args.vararg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function.args.kwarg.is_some()
        || !matches!(function.decorator_list.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == "Predicate")
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == "bool")
        || function.body.len() != 1
    {
        return None;
    }
    let ast::Stmt::Return(returned) = &function.body[0] else {
        return None;
    };
    let expression = returned.value.as_deref()?;
    let ast::Expr::Call(acc) = expression else {
        return None;
    };
    let ast::Expr::Name(binding) = acc.args.first()? else {
        return None;
    };
    is_acc_module_global_half(expression, binding.id.as_str())
        .then(|| (function.name.to_string(), binding.id.to_string()))
}

fn folded_int_getter_function(
    function: &ast::StmtFunctionDef,
    predicate: &str,
    binding: &str,
) -> bool {
    if !function.type_params.is_empty()
        || !function.args.posonlyargs.is_empty()
        || !function.args.args.is_empty()
        || function.args.vararg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function.args.kwarg.is_some()
        || !matches!(function.decorator_list.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == "Pure")
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == "int")
        || function.body.len() != 2
        || !direct_zero_argument_contract_call(&function.body[0], "Requires", predicate)
    {
        return false;
    }
    let ast::Stmt::Return(returned) = &function.body[1] else {
        return false;
    };
    let Some(ast::Expr::Call(unfolding)) = returned.value.as_deref() else {
        return false;
    };
    unfolding.args.len() == 2
        && unfolding.keywords.is_empty()
        && matches!(unfolding.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Unfolding")
        && is_zero_argument_named_call(&unfolding.args[0], predicate)
        && matches!(&unfolding.args[1], ast::Expr::Name(name) if name.id.as_str() == binding)
}

fn folded_int_update_bound(expression: &ast::Expr, predicate: &str, getter: &str) -> Option<i64> {
    let ast::Expr::BoolOp(conjunction) = expression else {
        return None;
    };
    let [permission, bound] = conjunction.values.as_slice() else {
        return None;
    };
    if conjunction.op != ast::BoolOp::And || !is_zero_argument_named_call(permission, predicate) {
        return None;
    }
    let ast::Expr::Compare(comparison) = bound else {
        return None;
    };
    let [ast::CmpOp::LtE] = comparison.ops.as_slice() else {
        return None;
    };
    let [maximum] = comparison.comparators.as_slice() else {
        return None;
    };
    if !is_zero_argument_named_call(&comparison.left, getter) {
        return None;
    }
    closed_module_int_literal(maximum, "folded module int upper bound").ok()
}

fn is_folded_int_update_postcondition(
    expression: &ast::Expr,
    binding: &str,
    increment: i64,
) -> bool {
    let ast::Expr::BoolOp(conjunction) = expression else {
        return false;
    };
    let [permission, equality] = conjunction.values.as_slice() else {
        return false;
    };
    if conjunction.op != ast::BoolOp::And || !is_acc_module_global_half(permission, binding) {
        return false;
    }
    let ast::Expr::Compare(comparison) = equality else {
        return false;
    };
    let [ast::CmpOp::Eq] = comparison.ops.as_slice() else {
        return false;
    };
    let [right] = comparison.comparators.as_slice() else {
        return false;
    };
    if !matches!(comparison.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binding) {
        return false;
    }
    let ast::Expr::BinOp(addition) = right else {
        return false;
    };
    if addition.op != ast::Operator::Add
        || closed_module_int_literal(&addition.right, "folded module int postcondition").ok()
            != Some(increment)
    {
        return false;
    }
    let ast::Expr::Call(old) = addition.left.as_ref() else {
        return false;
    };
    old.args.len() == 1
        && old.keywords.is_empty()
        && matches!(old.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Old")
        && matches!(old.args.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == binding)
}

fn is_fold_or_unfold_statement(statement: &ast::Stmt, operation: &str, predicate: &str) -> bool {
    direct_contract_argument(statement, operation)
        .is_some_and(|argument| is_zero_argument_named_call(argument, predicate))
}

fn folded_int_updater_function(
    function: &ast::StmtFunctionDef,
    predicate: &str,
    getter: &str,
    binding: &str,
) -> Option<(i64, i64)> {
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || !function.args.posonlyargs.is_empty()
        || !function.args.args.is_empty()
        || function.args.vararg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function.args.kwarg.is_some()
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == "int")
        || function.body.len() != 9
    {
        return None;
    }
    let ast::Stmt::Global(global) = &function.body[0] else {
        return None;
    };
    if !matches!(global.names.as_slice(), [name] if name.as_str() == binding)
        || !direct_contract_argument(&function.body[1], "Requires")
            .is_some_and(|expression| is_acc_module_global_half(expression, binding))
        || !direct_zero_argument_contract_call(&function.body[3], "Ensures", predicate)
        || !is_fold_or_unfold_statement(&function.body[5], "Unfold", predicate)
        || !is_fold_or_unfold_statement(&function.body[7], "Fold", predicate)
    {
        return None;
    }
    let maximum = folded_int_update_bound(
        direct_contract_argument(&function.body[2], "Requires")?,
        predicate,
        getter,
    )?;
    let ast::Stmt::AugAssign(update) = &function.body[6] else {
        return None;
    };
    if update.op != ast::Operator::Add
        || !matches!(update.target.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binding)
    {
        return None;
    }
    let increment = closed_module_int_literal(&update.value, "folded module int increment").ok()?;
    if increment <= 0
        || !is_folded_int_update_postcondition(
            direct_contract_argument(&function.body[4], "Ensures")?,
            binding,
            increment,
        )
    {
        return None;
    }
    let ast::Stmt::Return(returned) = &function.body[8] else {
        return None;
    };
    matches!(returned.value.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == binding)
        .then_some((maximum, increment))
}

fn closed_module_folded_int_update(suite: &[ast::Stmt]) -> Option<ClosedModuleFoldedIntUpdate> {
    let (predicate, binding) = suite.iter().find_map(|statement| match statement {
        ast::Stmt::FunctionDef(function) => folded_int_predicate_function(function),
        _ => None,
    })?;
    let getter = suite.iter().find_map(|statement| match statement {
        ast::Stmt::FunctionDef(function)
            if folded_int_getter_function(function, &predicate, &binding) =>
        {
            Some(function.name.to_string())
        }
        _ => None,
    })?;
    let (updater, maximum, increment) = suite.iter().find_map(|statement| match statement {
        ast::Stmt::FunctionDef(function) => {
            folded_int_updater_function(function, &predicate, &getter, &binding)
                .map(|(maximum, increment)| (function.name.to_string(), maximum, increment))
        }
        _ => None,
    })?;
    Some(ClosedModuleFoldedIntUpdate {
        binding,
        predicate,
        getter,
        updater,
        maximum,
        increment,
    })
}

fn is_closed_module_fold_call(expression: &ast::Expr, shape: &ClosedModuleFoldedIntUpdate) -> bool {
    let ast::Expr::Call(fold) = expression else {
        return false;
    };
    fold.args.len() == 1
        && fold.keywords.is_empty()
        && matches!(fold.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Fold")
        && is_zero_argument_named_call(&fold.args[0], &shape.predicate)
}

fn is_closed_module_folded_int_call(
    expression: &ast::Expr,
    shape: &ClosedModuleFoldedIntUpdate,
) -> bool {
    is_zero_argument_named_call(expression, &shape.updater)
}

fn validate_passive_scalar_class_bindings(suite: &[ast::Stmt]) -> Result<(), ContractFailure> {
    const RESERVED_SCALAR_NAMES: &[&str] = &[
        "Acc",
        "Assert",
        "Assume",
        "ContractOnly",
        "Ensures",
        "Exsures",
        "Forall",
        "Implies",
        "Old",
        "Pure",
        "RaisedException",
        "Requires",
        "Result",
        "bool",
        "bytes",
        "int",
        "len",
        "list",
        "max",
        "min",
        "object",
        "range",
        "str",
        "tuple",
    ];

    let passive_names = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ClassDef(class) if is_supported_scalar_class(class) => {
                Some(class.name.as_str())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    for name in passive_names {
        if RESERVED_SCALAR_NAMES.contains(&name) {
            return failure(
                "frontend.python.contracts.passive-class-name-reserved",
                format!("passive scalar class name {name:?} shadows modeled scalar syntax"),
            );
        }
        let binding_count = suite
            .iter()
            .map(|statement| scalar_module_binding_count(statement, name))
            .sum::<usize>();
        if binding_count != 1 {
            return failure(
                "frontend.python.contracts.passive-class-binding-shadowed",
                format!(
                    "passive scalar class name {name:?} is rebound by another module statement"
                ),
            );
        }
    }
    if suite.iter().any(
        |statement| matches!(statement, ast::Stmt::ClassDef(class) if is_scalar_int_subclass(class)),
    ) && suite
        .iter()
        .map(|statement| scalar_module_binding_count(statement, "int"))
        .sum::<usize>()
        != 0
    {
        return failure(
            "frontend.python.contracts.scalar-subclass-base-shadowed",
            "pass-only scalar int subclasses require the canonical unshadowed builtin int",
        );
    }
    Ok(())
}

fn scalar_module_binding_count(statement: &ast::Stmt, expected: &str) -> usize {
    match statement {
        ast::Stmt::FunctionDef(function) => usize::from(function.name.as_str() == expected),
        ast::Stmt::ClassDef(class) => usize::from(class.name.as_str() == expected),
        ast::Stmt::ImportFrom(import) => import
            .names
            .iter()
            .filter(|alias| {
                alias.name.as_str() != "*"
                    && alias
                        .asname
                        .as_ref()
                        .map_or(alias.name.as_str(), |name| name.as_str())
                        == expected
            })
            .count(),
        ast::Stmt::Assign(assignment) => assignment
            .targets
            .iter()
            .filter(
                |target| matches!(target, ast::Expr::Name(name) if name.id.as_str() == expected),
            )
            .count(),
        ast::Stmt::AnnAssign(assignment) => usize::from(
            matches!(assignment.target.as_ref(), ast::Expr::Name(name) if name.id.as_str() == expected),
        ),
        _ => 0,
    }
}

fn is_conformance_literal_print(expression: &ast::Expr) -> bool {
    let ast::Expr::Call(call) = expression else {
        return false;
    };
    matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "print")
        && call.keywords.is_empty()
        && matches!(call.args.as_slice(), [ast::Expr::Constant(constant)] if matches!(constant.value, ast::Constant::Str(_)))
}

fn is_inert_string_statement(statement: &ast::Stmt) -> bool {
    matches!(
        statement,
        ast::Stmt::Expr(ast::StmtExpr { value, .. }) if matches!(
            value.as_ref(),
            ast::Expr::Constant(ast::ExprConstant {
                value: ast::Constant::Str(_),
                ..
            })
        )
    )
}

fn closed_python_float_literal(expression: &ast::Expr) -> Option<f64> {
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    if call.args.len() != 1
        || !call.keywords.is_empty()
        || !matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "float")
    {
        return None;
    }
    let ast::Expr::Constant(constant) = &call.args[0] else {
        return None;
    };
    let ast::Constant::Str(text) = &constant.value else {
        return None;
    };
    if text.trim() != text {
        return None;
    }
    match text.to_ascii_lowercase().as_str() {
        "nan" | "+nan" | "-nan" => Some(f64::NAN),
        "inf" | "+inf" | "infinity" | "+infinity" => Some(f64::INFINITY),
        "-inf" | "-infinity" => Some(f64::NEG_INFINITY),
        _ => text.parse::<f64>().ok(),
    }
}

fn closed_float_value(expression: &ast::Expr, values: &BTreeMap<String, f64>) -> Option<f64> {
    match expression {
        ast::Expr::Name(name) => values.get(name.id.as_str()).copied(),
        expression => closed_python_float_literal(expression),
    }
}

fn closed_float_assertion(expression: &ast::Expr, values: &BTreeMap<String, f64>) -> Option<bool> {
    if let ast::Expr::UnaryOp(negation) = expression
        && negation.op == ast::UnaryOp::Not
    {
        return closed_float_assertion(&negation.operand, values).map(|value| !value);
    }
    let ast::Expr::Compare(comparison) = expression else {
        return None;
    };
    let [operator] = comparison.ops.as_slice() else {
        return None;
    };
    let [right] = comparison.comparators.as_slice() else {
        return None;
    };
    let left = closed_float_value(&comparison.left, values)?;
    let right = closed_float_value(right, values)?;
    Some(match operator {
        ast::CmpOp::Eq => left == right,
        ast::CmpOp::NotEq => left != right,
        ast::CmpOp::Lt => left < right,
        ast::CmpOp::LtE => left <= right,
        ast::CmpOp::Gt => left > right,
        ast::CmpOp::GtE => left >= right,
        _ => return None,
    })
}

fn lower_closed_float_literal_function(
    function: &ast::StmtFunctionDef,
    path: &str,
    source: &str,
) -> Result<Option<Vec<Obligation>>, ContractFailure> {
    let has_float_conversion = function.body.iter().any(|statement| {
        matches!(statement, ast::Stmt::Assign(assignment)
            if closed_python_float_literal(&assignment.value).is_some())
    });
    if !has_float_conversion {
        return Ok(None);
    }
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || !function.args.posonlyargs.is_empty()
        || !function.args.args.is_empty()
        || function.args.vararg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function.args.kwarg.is_some()
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Constant(constant)) if matches!(constant.value, ast::Constant::None))
    {
        return failure(
            "frontend.python.contracts.closed-float-function-shape",
            "closed float conversion semantics require an undecorated zero-argument None-returning function",
        );
    }

    let mut values = BTreeMap::new();
    let mut obligations = Vec::new();
    for statement in &function.body {
        match statement {
            ast::Stmt::Assign(assignment) => {
                let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
                    return failure(
                        "frontend.python.contracts.closed-float-assignment-target",
                        "closed float conversion assignments require one fresh direct-name target",
                    );
                };
                if values.contains_key(target.id.as_str()) {
                    return failure(
                        "frontend.python.contracts.closed-float-reassignment",
                        format!(
                            "closed float binding {:?} is assigned more than once",
                            target.id
                        ),
                    );
                }
                let value = closed_python_float_literal(&assignment.value).ok_or_else(|| {
                    ContractFailure {
                        code: "frontend.python.contracts.closed-float-conversion",
                        message: "closed float conversion requires one canonical string literal"
                            .to_owned(),
                    }
                })?;
                values.insert(target.id.to_string(), value);
            }
            ast::Stmt::Expr(expression) if contract_assertion(&expression.value).is_some() => {
                let assertion = contract_assertion(&expression.value)
                    .expect("guard established closed float assertion");
                let conclusion =
                    closed_float_assertion(assertion, &values).ok_or_else(|| ContractFailure {
                        code: "frontend.python.contracts.closed-float-assertion",
                        message: "closed float assertions require one direct IEEE-754 comparison"
                            .to_owned(),
                    })?;
                let byte_offset = u32::from(expression.range.start());
                obligations.push(Obligation {
                    id: format!(
                        "{}:assert:closed-float:{byte_offset}:{}",
                        function.name,
                        obligations.len()
                    ),
                    expectation: ObligationExpectation::Prove,
                    assumptions: Vec::new(),
                    conclusion: Term::Bool { value: conclusion },
                    path: path.to_owned(),
                    byte_offset,
                    line: source_location(source, byte_offset).0,
                    column: source_location(source, byte_offset).1,
                });
            }
            _ => {
                return failure(
                    "frontend.python.contracts.closed-float-statement",
                    "closed float conversion functions permit only fresh conversions and direct assertions",
                );
            }
        }
    }
    if obligations.is_empty() {
        return failure(
            "frontend.python.contracts.closed-float-obligations",
            "closed float conversion functions require at least one source assertion",
        );
    }
    Ok(Some(obligations))
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClosedTerminationLoop {
    function: String,
    parameter: String,
    induction: String,
    step: i64,
    invariant_offset: u32,
}

fn closed_termination_loop(function: &ast::StmtFunctionDef) -> Option<ClosedTerminationLoop> {
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || !function.args.posonlyargs.is_empty()
        || function.args.args.len() != 1
        || function.args.vararg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function.args.kwarg.is_some()
        || function.args.args[0].default.is_some()
        || !matches!(function.args.args[0].def.annotation.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == "int")
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Constant(constant)) if matches!(constant.value, ast::Constant::None))
        || function.body.len() != 3
    {
        return None;
    }
    let parameter = function.args.args[0].def.arg.to_string();
    let precondition = direct_contract_argument(&function.body[0], "Requires")?;
    let ast::Expr::Compare(precondition) = precondition else {
        return None;
    };
    if !matches!(precondition.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == parameter)
        || !matches!(precondition.ops.as_slice(), [ast::CmpOp::Gt])
        || !matches!(precondition.comparators.as_slice(), [bound]
            if closed_module_int_literal(bound, "termination loop precondition").is_ok())
    {
        return None;
    }
    let ast::Stmt::Assign(initializer) = &function.body[1] else {
        return None;
    };
    let [ast::Expr::Name(induction)] = initializer.targets.as_slice() else {
        return None;
    };
    if initializer.type_comment.is_some()
        || closed_module_int_literal(&initializer.value, "termination loop initializer").is_err()
    {
        return None;
    }
    let ast::Stmt::While(loop_statement) = &function.body[2] else {
        return None;
    };
    if !loop_statement.orelse.is_empty() || loop_statement.body.len() != 2 {
        return None;
    }
    let ast::Expr::Compare(guard) = loop_statement.test.as_ref() else {
        return None;
    };
    if !matches!(guard.left.as_ref(), ast::Expr::Name(name) if name.id == induction.id)
        || !matches!(guard.ops.as_slice(), [ast::CmpOp::Lt])
        || !matches!(guard.comparators.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == parameter)
    {
        return None;
    }
    let measure = direct_contract_argument(&loop_statement.body[0], "Invariant")?;
    let ast::Expr::Call(must_terminate) = measure else {
        return None;
    };
    if must_terminate.args.len() != 1
        || !must_terminate.keywords.is_empty()
        || !matches!(must_terminate.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "MustTerminate")
    {
        return None;
    }
    let ast::Expr::BinOp(measure) = &must_terminate.args[0] else {
        return None;
    };
    if measure.op != ast::Operator::Sub
        || !matches!(measure.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == parameter)
        || !matches!(measure.right.as_ref(), ast::Expr::Name(name) if name.id == induction.id)
    {
        return None;
    }
    let ast::Stmt::AugAssign(update) = &loop_statement.body[1] else {
        return None;
    };
    if update.op != ast::Operator::Add
        || !matches!(update.target.as_ref(), ast::Expr::Name(name) if name.id == induction.id)
    {
        return None;
    }
    let step = closed_module_int_literal(&update.value, "termination loop step").ok()?;
    if step <= 0 {
        return None;
    }
    Some(ClosedTerminationLoop {
        function: function.name.to_string(),
        parameter,
        induction: induction.id.to_string(),
        step,
        invariant_offset: loop_statement.body[0].range().start().into(),
    })
}

fn suite_has_only_supported_closed_termination_contracts(suite: &[ast::Stmt]) -> bool {
    let functions = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => Some(function),
            _ => None,
        })
        .collect::<Vec<_>>();
    !functions.is_empty()
        && functions.iter().all(|function| {
            closed_termination_loop(function).is_some()
                || closed_vacuous_termination_loop(function).is_some()
                || closed_vacuous_termination_precondition(function).is_some()
        })
}

fn is_canonical_obligations_star_import(import: &ast::StmtImportFrom) -> bool {
    import.level.is_none_or(|level| level == 0_u32)
        && import
            .module
            .as_ref()
            .is_some_and(|module| module.as_str() == "nagini_contracts.obligations")
        && matches!(import.names.as_slice(), [alias]
            if alias.name.as_str() == "*" && alias.asname.is_none())
}

fn lower_closed_termination_loop(
    shape: &ClosedTerminationLoop,
    path: &str,
    source: &str,
) -> Vec<Obligation> {
    let parameter = Term::Variable {
        name: format!("{}::{}", shape.function, shape.parameter),
        sort: Sort::Int,
    };
    let induction = Term::Variable {
        name: format!("{}::{}::loop", shape.function, shape.induction),
        sort: Sort::Int,
    };
    let guard = Term::Less {
        left: Box::new(induction.clone()),
        right: Box::new(parameter.clone()),
    };
    let measure = Term::Subtract {
        left: Box::new(parameter.clone()),
        right: Box::new(induction.clone()),
    };
    let next_measure = Term::Subtract {
        left: Box::new(parameter),
        right: Box::new(Term::Add {
            left: Box::new(induction),
            right: Box::new(Term::Int { value: shape.step }),
        }),
    };
    let (line, column) = source_location(source, shape.invariant_offset);
    vec![
        Obligation {
            id: format!("{}:termination-measure-positive", shape.function),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![guard.clone()],
            conclusion: Term::Greater {
                left: Box::new(measure.clone()),
                right: Box::new(Term::Int { value: 0 }),
            },
            path: path.to_owned(),
            byte_offset: shape.invariant_offset,
            line,
            column,
        },
        Obligation {
            id: format!("{}:termination-measure-decrease", shape.function),
            expectation: ObligationExpectation::Prove,
            assumptions: vec![guard],
            conclusion: Term::Less {
                left: Box::new(next_measure),
                right: Box::new(measure),
            },
            path: path.to_owned(),
            byte_offset: shape.invariant_offset,
            line,
            column,
        },
    ]
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClosedVacuousTerminationLoop {
    function: String,
    proof: Term,
    invariant_offset: u32,
}

fn closed_termination_integer_term(expression: &ast::Expr) -> Option<Term> {
    match expression {
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Int(value) => Some(Term::Int {
                value: value.to_string().parse().ok()?,
            }),
            _ => None,
        },
        ast::Expr::UnaryOp(operation) => {
            let value = Box::new(closed_termination_integer_term(&operation.operand)?);
            match operation.op {
                ast::UnaryOp::UAdd => Some(*value),
                ast::UnaryOp::USub => Some(Term::Negate { value }),
                _ => None,
            }
        }
        ast::Expr::BinOp(operation) => {
            let left = Box::new(closed_termination_integer_term(&operation.left)?);
            let right = Box::new(closed_termination_integer_term(&operation.right)?);
            match operation.op {
                ast::Operator::Add => Some(Term::Add { left, right }),
                ast::Operator::Sub => Some(Term::Subtract { left, right }),
                ast::Operator::Mult => Some(Term::Multiply { left, right }),
                _ => None,
            }
        }
        _ => None,
    }
}

fn closed_termination_boolean_term(expression: &ast::Expr) -> Option<Term> {
    match expression {
        ast::Expr::Constant(constant) => match constant.value {
            ast::Constant::Bool(value) => Some(Term::Bool { value }),
            _ => None,
        },
        ast::Expr::UnaryOp(operation) if operation.op == ast::UnaryOp::Not => Some(Term::Not {
            value: Box::new(closed_termination_boolean_term(&operation.operand)?),
        }),
        ast::Expr::Compare(comparison)
            if comparison.ops.len() == 1 && comparison.comparators.len() == 1 =>
        {
            let left = Box::new(closed_termination_integer_term(&comparison.left)?);
            let right = Box::new(closed_termination_integer_term(&comparison.comparators[0])?);
            match comparison.ops[0] {
                ast::CmpOp::Eq => Some(Term::Equal { left, right }),
                ast::CmpOp::NotEq => Some(Term::Not {
                    value: Box::new(Term::Equal { left, right }),
                }),
                ast::CmpOp::Lt => Some(Term::Less { left, right }),
                ast::CmpOp::LtE => Some(Term::LessEqual { left, right }),
                ast::CmpOp::Gt => Some(Term::Greater { left, right }),
                ast::CmpOp::GtE => Some(Term::GreaterEqual { left, right }),
                _ => None,
            }
        }
        _ => None,
    }
}

fn direct_closed_must_terminate_measure(expression: &ast::Expr) -> Option<Term> {
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    if !call.keywords.is_empty()
        || !matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "MustTerminate")
    {
        return None;
    }
    let [measure] = call.args.as_slice() else {
        return None;
    };
    closed_termination_integer_term(measure)
}

fn closed_implied_termination_antecedent(expression: &ast::Expr) -> Option<Term> {
    let ast::Expr::Call(implies) = expression else {
        return None;
    };
    if !implies.keywords.is_empty()
        || !matches!(implies.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Implies")
    {
        return None;
    }
    let [antecedent, measure] = implies.args.as_slice() else {
        return None;
    };
    direct_closed_must_terminate_measure(measure)?;
    closed_termination_boolean_term(antecedent)
}

fn closed_vacuous_termination_loop(
    function: &ast::StmtFunctionDef,
) -> Option<ClosedVacuousTerminationLoop> {
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || !function.args.posonlyargs.is_empty()
        || !function.args.args.is_empty()
        || function.args.vararg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function.args.kwarg.is_some()
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Constant(constant)) if matches!(constant.value, ast::Constant::None))
    {
        return None;
    }
    let [ast::Stmt::While(loop_statement)] = function.body.as_slice() else {
        return None;
    };
    if !loop_statement.orelse.is_empty()
        || !matches!(loop_statement.body.as_slice(), [_, ast::Stmt::Pass(_)])
    {
        return None;
    }
    let invariant = direct_contract_argument(&loop_statement.body[0], "Invariant")?;
    let proof = if direct_closed_must_terminate_measure(invariant).is_some() {
        Term::Not {
            value: Box::new(closed_termination_boolean_term(&loop_statement.test)?),
        }
    } else {
        closed_termination_boolean_term(&loop_statement.test)?;
        Term::Not {
            value: Box::new(closed_implied_termination_antecedent(invariant)?),
        }
    };
    Some(ClosedVacuousTerminationLoop {
        function: function.name.to_string(),
        proof,
        invariant_offset: loop_statement.body[0].range().start().into(),
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClosedVacuousTerminationPrecondition {
    function: String,
    proof: Term,
    precondition_offset: u32,
}

fn closed_vacuous_termination_precondition(
    function: &ast::StmtFunctionDef,
) -> Option<ClosedVacuousTerminationPrecondition> {
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || !function.args.posonlyargs.is_empty()
        || !function.args.args.is_empty()
        || function.args.vararg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function.args.kwarg.is_some()
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Constant(constant)) if matches!(constant.value, ast::Constant::None))
    {
        return None;
    }
    let [precondition] = function.body.as_slice() else {
        return None;
    };
    let condition = direct_contract_argument(precondition, "Requires")?;
    Some(ClosedVacuousTerminationPrecondition {
        function: function.name.to_string(),
        proof: Term::Not {
            value: Box::new(closed_implied_termination_antecedent(condition)?),
        },
        precondition_offset: precondition.range().start().into(),
    })
}

fn lower_closed_vacuous_termination_precondition(
    shape: &ClosedVacuousTerminationPrecondition,
    path: &str,
    source: &str,
) -> Obligation {
    let (line, column) = source_location(source, shape.precondition_offset);
    Obligation {
        id: format!("{}:vacuous-termination-precondition", shape.function),
        expectation: ObligationExpectation::Prove,
        assumptions: Vec::new(),
        conclusion: shape.proof.clone(),
        path: path.to_owned(),
        byte_offset: shape.precondition_offset,
        line,
        column,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClosedRecursiveTerminationCall {
    decrement: i64,
    byte_offset: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClosedRecursiveTerminationModule {
    function: String,
    parameter: String,
    first_base: i64,
    second_base: i64,
    calls: Vec<ClosedRecursiveTerminationCall>,
}

fn canonical_contract_import_with_symbols(statement: &ast::Stmt, expected: &[&str]) -> bool {
    let ast::Stmt::ImportFrom(import) = statement else {
        return false;
    };
    import.level.is_none_or(|level| level == 0_u32)
        && import
            .module
            .as_ref()
            .is_some_and(|module| module.as_str() == "nagini_contracts.contracts")
        && import.names.len() == expected.len()
        && import
            .names
            .iter()
            .zip(expected)
            .all(|(alias, expected)| alias.name.as_str() == *expected && alias.asname.is_none())
}

fn closed_recursive_call(
    statement: &ast::Stmt,
    receiver: &str,
    method: &str,
    parameter: &str,
) -> Option<(String, ClosedRecursiveTerminationCall)> {
    let ast::Stmt::Assign(assignment) = statement else {
        return None;
    };
    let [ast::Expr::Name(binding)] = assignment.targets.as_slice() else {
        return None;
    };
    if assignment.type_comment.is_some() {
        return None;
    }
    let ast::Expr::Call(call) = assignment.value.as_ref() else {
        return None;
    };
    let ast::Expr::Attribute(callee) = call.func.as_ref() else {
        return None;
    };
    if callee.attr.as_str() != method
        || !matches!(callee.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == receiver)
        || !call.keywords.is_empty()
    {
        return None;
    }
    let [ast::Expr::BinOp(argument)] = call.args.as_slice() else {
        return None;
    };
    if argument.op != ast::Operator::Sub
        || !matches!(argument.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == parameter)
    {
        return None;
    }
    let decrement =
        closed_module_int_literal(&argument.right, "recursive termination decrement").ok()?;
    if decrement <= 0 {
        return None;
    }
    Some((
        binding.id.to_string(),
        ClosedRecursiveTerminationCall {
            decrement,
            byte_offset: statement.range().start().into(),
        },
    ))
}

fn closed_recursive_termination_class(
    class: &ast::StmtClassDef,
) -> Option<ClosedRecursiveTerminationModule> {
    if !class.bases.is_empty()
        || !class.keywords.is_empty()
        || !class.decorator_list.is_empty()
        || !class.type_params.is_empty()
    {
        return None;
    }
    let [ast::Stmt::FunctionDef(method)] = class.body.as_slice() else {
        return None;
    };
    if !method.decorator_list.is_empty()
        || !method.type_params.is_empty()
        || !method.args.posonlyargs.is_empty()
        || method.args.args.len() != 2
        || method.args.vararg.is_some()
        || !method.args.kwonlyargs.is_empty()
        || method.args.kwarg.is_some()
        || method
            .args
            .args
            .iter()
            .any(|argument| argument.default.is_some())
        || method.args.args[0].def.annotation.is_some()
        || !matches!(method.args.args[1].def.annotation.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == "int")
        || !matches!(method.returns.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == "int")
        || method.body.len() != 2
    {
        return None;
    }
    let receiver = method.args.args[0].def.arg.as_str();
    let parameter = method.args.args[1].def.arg.as_str();
    if receiver == parameter {
        return None;
    }
    let precondition = direct_contract_argument(&method.body[0], "Requires")?;
    let ast::Expr::Call(must_terminate) = precondition else {
        return None;
    };
    if !must_terminate.keywords.is_empty()
        || !matches!(must_terminate.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "MustTerminate")
        || !matches!(must_terminate.args.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == parameter)
    {
        return None;
    }
    let ast::Stmt::If(first_branch) = &method.body[1] else {
        return None;
    };
    let ast::Expr::Compare(first_test) = first_branch.test.as_ref() else {
        return None;
    };
    if !matches!(first_test.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == parameter)
        || !matches!(first_test.ops.as_slice(), [ast::CmpOp::LtE])
        || !matches!(first_branch.body.as_slice(), [ast::Stmt::Return(return_statement)]
            if return_statement.value.as_deref().is_some_and(|value|
                closed_module_int_literal(value, "recursive base return").is_ok()))
    {
        return None;
    }
    let [first_bound] = first_test.comparators.as_slice() else {
        return None;
    };
    let first_base = closed_module_int_literal(first_bound, "recursive first base").ok()?;
    let [ast::Stmt::If(second_branch)] = first_branch.orelse.as_slice() else {
        return None;
    };
    let ast::Expr::Compare(second_test) = second_branch.test.as_ref() else {
        return None;
    };
    if !matches!(second_test.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == parameter)
        || !matches!(second_test.ops.as_slice(), [ast::CmpOp::Eq])
        || !matches!(second_branch.body.as_slice(), [ast::Stmt::Return(return_statement)]
            if return_statement.value.as_deref().is_some_and(|value|
                closed_module_int_literal(value, "recursive base return").is_ok()))
        || second_branch.orelse.len() != 3
    {
        return None;
    }
    let [second_bound] = second_test.comparators.as_slice() else {
        return None;
    };
    let second_base = closed_module_int_literal(second_bound, "recursive second base").ok()?;
    let (first_binding, first_call) = closed_recursive_call(
        &second_branch.orelse[0],
        receiver,
        method.name.as_str(),
        parameter,
    )?;
    let (second_binding, second_call) = closed_recursive_call(
        &second_branch.orelse[1],
        receiver,
        method.name.as_str(),
        parameter,
    )?;
    if first_binding == second_binding
        || matches!(first_binding.as_str(), name if name == receiver || name == parameter)
    {
        return None;
    }
    let ast::Stmt::Return(return_statement) = &second_branch.orelse[2] else {
        return None;
    };
    let ast::Expr::BinOp(result) = return_statement.value.as_deref()? else {
        return None;
    };
    if result.op != ast::Operator::Add
        || !matches!(result.left.as_ref(), ast::Expr::Name(name)
            if name.id.as_str() == first_binding || name.id.as_str() == second_binding)
        || !matches!(result.right.as_ref(), ast::Expr::Name(name)
            if name.id.as_str() == first_binding || name.id.as_str() == second_binding)
        || matches!((result.left.as_ref(), result.right.as_ref()),
            (ast::Expr::Name(left), ast::Expr::Name(right)) if left.id == right.id)
    {
        return None;
    }
    Some(ClosedRecursiveTerminationModule {
        function: format!("{}.{}", class.name, method.name),
        parameter: parameter.to_owned(),
        first_base,
        second_base,
        calls: vec![first_call, second_call],
    })
}

fn closed_recursive_termination_module(
    suite: &[ast::Stmt],
) -> Option<ClosedRecursiveTerminationModule> {
    let suite = if suite.first().is_some_and(is_inert_string_statement) {
        &suite[1..]
    } else {
        suite
    };
    let [contracts, obligations, ast::Stmt::ClassDef(class)] = suite else {
        return None;
    };
    if !canonical_contract_import_with_symbols(contracts, &["Requires"])
        || !matches!(obligations, ast::Stmt::ImportFrom(import)
            if is_canonical_obligations_star_import(import))
    {
        return None;
    }
    closed_recursive_termination_class(class)
}

fn verify_closed_recursive_termination_module(
    shape: &ClosedRecursiveTerminationModule,
    path: &str,
    source: &str,
    requested_symbols: &[String],
) -> Result<ContractVerification, ContractFailure> {
    if requested_symbols
        .iter()
        .any(|symbol| symbol != &shape.function)
    {
        return failure(
            "frontend.python.symbol.missing",
            "requested symbol is not the verified recursive method",
        );
    }
    let parameter = Term::Variable {
        name: format!("{}::{}", shape.function, shape.parameter),
        sort: Sort::Int,
    };
    let assumptions = vec![
        Term::Not {
            value: Box::new(Term::LessEqual {
                left: Box::new(parameter.clone()),
                right: Box::new(Term::Int {
                    value: shape.first_base,
                }),
            }),
        },
        Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(parameter.clone()),
                right: Box::new(Term::Int {
                    value: shape.second_base,
                }),
            }),
        },
    ];
    let mut obligations = Vec::new();
    for (index, call) in shape.calls.iter().enumerate() {
        let measure = Term::Subtract {
            left: Box::new(parameter.clone()),
            right: Box::new(Term::Int {
                value: call.decrement,
            }),
        };
        let (line, column) = source_location(source, call.byte_offset);
        for (property, conclusion) in [
            (
                "positive",
                Term::Greater {
                    left: Box::new(measure.clone()),
                    right: Box::new(Term::Int { value: 0 }),
                },
            ),
            (
                "decrease",
                Term::Less {
                    left: Box::new(measure),
                    right: Box::new(parameter.clone()),
                },
            ),
        ] {
            obligations.push(
                discharge(&Obligation {
                    id: format!("{}:recursive-call-{index}:{property}", shape.function),
                    expectation: ObligationExpectation::Prove,
                    assumptions: assumptions.clone(),
                    conclusion,
                    path: path.to_owned(),
                    byte_offset: call.byte_offset,
                    line,
                    column,
                })
                .map_err(|message| ContractFailure {
                    code: "solver.translation-failed",
                    message,
                })?,
            );
        }
    }
    let passed = obligations.iter().all(ObligationResult::satisfied);
    Ok(ContractVerification {
        schema: "maledictus-python-contract-verification/v1".to_owned(),
        path: path.to_owned(),
        functions: vec![shape.function.clone()],
        obligations,
        passed,
    })
}

fn lower_closed_vacuous_termination_loop(
    shape: &ClosedVacuousTerminationLoop,
    path: &str,
    source: &str,
) -> Obligation {
    let (line, column) = source_location(source, shape.invariant_offset);
    Obligation {
        id: format!("{}:vacuous-termination-condition", shape.function),
        expectation: ObligationExpectation::Prove,
        assumptions: Vec::new(),
        conclusion: shape.proof.clone(),
        path: path.to_owned(),
        byte_offset: shape.invariant_offset,
        line,
        column,
    }
}

fn validate_module_list_augassign_shape(
    suite: &[ast::Stmt],
    assignment: &ast::StmtAugAssign,
) -> Result<ModuleListAugAssignShape, ContractFailure> {
    let ast::Expr::Subscript(target) = assignment.target.as_ref() else {
        return failure(
            "frontend.python.contracts.module-list-mutation-target",
            "module list mutation requires one direct-name subscript target",
        );
    };
    let ast::Expr::Name(container) = target.value.as_ref() else {
        return failure(
            "frontend.python.contracts.module-list-mutation-container",
            "module list mutation requires one source-owned direct-name container",
        );
    };
    let raw_index = constant_tuple_index(&target.slice).ok_or_else(|| ContractFailure {
        code: "frontend.python.contracts.module-list-mutation-index",
        message: "module list mutation requires a statically known nonnegative integer index"
            .to_owned(),
    })?;
    let index = usize::try_from(raw_index).map_err(|_| ContractFailure {
        code: "frontend.python.contracts.module-list-mutation-index",
        message: format!(
            "module list mutation index {raw_index} is negative or exceeds the platform index range"
        ),
    })?;
    if !matches!(
        assignment.op,
        ast::Operator::Add | ast::Operator::Sub | ast::Operator::Mult
    ) {
        return failure(
            "frontend.python.contracts.module-list-mutation-operator",
            "module list augmented assignment supports only primitive int +, -, and *",
        );
    }
    if !matches!(
        assignment.value.as_ref(),
        ast::Expr::Constant(ast::ExprConstant {
            value: ast::Constant::Int(_),
            ..
        })
    ) {
        return failure(
            "frontend.python.contracts.module-list-mutation-rhs",
            "module list augmented assignment requires one effect-free int literal right-hand side",
        );
    }

    let binding = container.id.to_string();
    let mutation_offset = u32::from(assignment.range.start());
    let mut initializer_found = false;
    for statement in suite {
        if statement.range().start() == assignment.range.start() {
            continue;
        }
        match statement {
            ast::Stmt::AnnAssign(initializer) if matches!(initializer.target.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binding) =>
            {
                if initializer_found || u32::from(initializer.range.start()) >= mutation_offset {
                    return failure(
                        "frontend.python.contracts.module-list-mutation-provenance",
                        format!(
                            "module list {binding:?} must have exactly one earlier source-owned initializer"
                        ),
                    );
                }
                let expected = annotation_sort(Some(&initializer.annotation))?;
                if expected != Sort::List(Box::new(Sort::Int)) {
                    return failure(
                        "frontend.python.contracts.module-list-mutation-element-type",
                        format!(
                            "module list {binding:?} must be annotated exactly as List[int], found {expected:?}"
                        ),
                    );
                }
                let Some(ast::Expr::List(list)) = initializer.value.as_deref() else {
                    return failure(
                        "frontend.python.contracts.module-list-mutation-provenance",
                        format!(
                            "module list {binding:?} must originate from a direct finite list literal"
                        ),
                    );
                };
                if !list.elts.iter().all(|element| {
                    matches!(
                        element,
                        ast::Expr::Constant(ast::ExprConstant {
                            value: ast::Constant::Int(_),
                            ..
                        })
                    )
                }) {
                    return failure(
                        "frontend.python.contracts.module-list-mutation-element-type",
                        "module list mutation requires a finite literal containing only exact int elements",
                    );
                }
                if index >= list.elts.len() {
                    return failure(
                        "frontend.python.contracts.module-list-mutation-index",
                        format!(
                            "module list mutation index {index} is out of bounds for literal length {}",
                            list.elts.len()
                        ),
                    );
                }
                initializer_found = true;
            }
            ast::Stmt::FunctionDef(_) | ast::Stmt::ClassDef(_) => {
                return failure(
                    "frontend.python.contracts.module-list-mutation-escape",
                    format!(
                        "module list {binding:?} cannot share a module with callable or class bodies in the closed mutation fragment"
                    ),
                );
            }
            ast::Stmt::Assign(other)
                if other.targets.iter().any(
                    |target| matches!(target, ast::Expr::Name(name) if name.id.as_str() == binding),
                ) =>
            {
                return failure(
                    "frontend.python.contracts.module-list-mutation-provenance",
                    format!("module list {binding:?} is rebound outside its unique initializer"),
                );
            }
            ast::Stmt::AnnAssign(other) if matches!(other.target.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binding) =>
            {
                return failure(
                    "frontend.python.contracts.module-list-mutation-provenance",
                    format!("module list {binding:?} is rebound outside its unique initializer"),
                );
            }
            ast::Stmt::AugAssign(_) => {
                return failure(
                    "frontend.python.contracts.module-list-mutation-count",
                    "the closed module list mutation fragment permits exactly one mutation",
                );
            }
            _ if statement_unconditional_read_names(statement).contains(&binding) => {
                return failure(
                    "frontend.python.contracts.module-list-mutation-alias",
                    format!(
                        "module list {binding:?} is read or escapes outside its one certified mutation"
                    ),
                );
            }
            _ => {}
        }
    }
    if !initializer_found {
        return failure(
            "frontend.python.contracts.module-list-mutation-provenance",
            format!("module list {binding:?} has no unique earlier List[int] literal initializer"),
        );
    }
    Ok(ModuleListAugAssignShape { binding, index })
}

#[allow(clippy::too_many_arguments)]
fn apply_module_list_augassign(
    assignment: &ast::StmtAugAssign,
    shape: &ModuleListAugAssignShape,
    globals: &mut BTreeMap<String, Term>,
    available_functions: &BTreeMap<String, InlineFunction>,
    type_comments: &BTreeMap<u32, ScalarTypeComment>,
    exception_hierarchy: &ExceptionHierarchy,
    conformance_mode: bool,
) -> Result<ModuleListMutationRecord, ContractFailure> {
    let container = globals
        .get(shape.binding.as_str())
        .cloned()
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-list-mutation-provenance",
            message: format!(
                "module list {:?} is unavailable when its mutation executes",
                shape.binding
            ),
        })?;
    let Term::List {
        element_sort,
        mut values,
    } = container
    else {
        return failure(
            "frontend.python.contracts.module-list-mutation-container-type",
            format!("module binding {:?} is not a finite list", shape.binding),
        );
    };
    if element_sort != Sort::Int {
        return failure(
            "frontend.python.contracts.module-list-mutation-element-type",
            format!(
                "module list {:?} has non-int element sort {element_sort:?}",
                shape.binding
            ),
        );
    }
    let previous = values
        .get(shape.index)
        .cloned()
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-list-mutation-index",
            message: format!(
                "module list mutation index {} is out of bounds for runtime literal length {}",
                shape.index,
                values.len()
            ),
        })?;
    let previous = coerce_python_int(previous, "module list mutation read")?;
    let lowerer = ExpressionLowerer {
        functions: available_functions,
        globals,
        type_comments,
        call_stack: vec!["<module-list-mutation>".to_owned()],
        exception_hierarchy,
        conformance_mode,
    };
    let right = coerce_python_int(
        lowerer.lower(&assignment.value, globals, None)?,
        "module list mutation right-hand side",
    )?;
    let result = match assignment.op {
        ast::Operator::Add => Term::Add {
            left: Box::new(previous.clone()),
            right: Box::new(right.clone()),
        },
        ast::Operator::Sub => Term::Subtract {
            left: Box::new(previous.clone()),
            right: Box::new(right.clone()),
        },
        ast::Operator::Mult => Term::Multiply {
            left: Box::new(previous.clone()),
            right: Box::new(right.clone()),
        },
        _ => {
            return failure(
                "frontend.python.contracts.module-list-mutation-operator",
                "module list mutation operator changed after shape validation",
            );
        }
    };
    result.sort().map_err(type_failure)?;
    let slot = values.get_mut(shape.index).ok_or_else(|| ContractFailure {
        code: "frontend.python.contracts.module-list-mutation-index",
        message: format!(
            "module list mutation index {} became unavailable before its store",
            shape.index
        ),
    })?;
    *slot = result.clone();
    globals.insert(
        shape.binding.clone(),
        Term::List {
            element_sort,
            values,
        },
    );
    let record = ModuleListMutationRecord {
        binding: shape.binding.clone(),
        index: shape.index,
        evaluation: [
            ModuleListMutationStep::Container,
            ModuleListMutationStep::Index,
            ModuleListMutationStep::Read,
            ModuleListMutationStep::RightHandSide,
            ModuleListMutationStep::PrimitiveOperation,
            ModuleListMutationStep::Store,
        ],
        previous,
        right,
        result,
    };
    validate_module_list_mutation_record(&record)?;
    Ok(record)
}

fn validate_module_list_mutation_record(
    record: &ModuleListMutationRecord,
) -> Result<(), ContractFailure> {
    if record.binding.is_empty()
        || record.evaluation
            != [
                ModuleListMutationStep::Container,
                ModuleListMutationStep::Index,
                ModuleListMutationStep::Read,
                ModuleListMutationStep::RightHandSide,
                ModuleListMutationStep::PrimitiveOperation,
                ModuleListMutationStep::Store,
            ]
        || record.previous.sort().map_err(type_failure)? != Sort::Int
        || record.right.sort().map_err(type_failure)? != Sort::Int
        || record.result.sort().map_err(type_failure)? != Sort::Int
    {
        return failure(
            "frontend.python.contracts.module-list-mutation-record",
            format!(
                "module list mutation record for {:?}[{}] is not canonical",
                record.binding, record.index
            ),
        );
    }
    Ok(())
}

fn validate_module_list_mutation_records(
    module_globals: &ImmutableModuleGlobals,
) -> Result<(), ContractFailure> {
    for record in &module_globals.list_mutations {
        validate_module_list_mutation_record(record)?;
    }
    Ok(())
}

#[derive(Clone, Debug)]
struct ClosedModuleCountdownTry {
    counter: String,
    start: i64,
    stop: i64,
    step: i64,
    invariants: Vec<(ast::Expr, u32)>,
    result_binding: String,
    source_binding: String,
    fallback: ast::Expr,
}

fn closed_module_int_literal(
    expression: &ast::Expr,
    context: &str,
) -> Result<i64, ContractFailure> {
    let value = constant_tuple_index(expression).ok_or_else(|| ContractFailure {
        code: "frontend.python.contracts.module-countdown-integer",
        message: format!("{context} requires one exact integer literal"),
    })?;
    i64::try_from(value).map_err(|_| ContractFailure {
        code: "frontend.python.integer.out-of-range",
        message: format!("{context} integer literal exceeds the scalar i64 range"),
    })
}

fn validate_closed_module_countdown_try(
    statement: &ast::StmtTry,
) -> Result<ClosedModuleCountdownTry, ContractFailure> {
    if !statement.orelse.is_empty() || !statement.finalbody.is_empty() {
        return failure(
            "frontend.python.contracts.module-countdown-try-shape",
            "closed module countdown try does not permit else or finally clauses",
        );
    }
    let [initialize, loop_statement, success] = statement.body.as_slice() else {
        return failure(
            "frontend.python.contracts.module-countdown-try-shape",
            "closed module countdown try requires initialization, one while loop, and one result assignment",
        );
    };
    let ast::Stmt::Assign(initialize) = initialize else {
        return failure(
            "frontend.python.contracts.module-countdown-initializer",
            "module countdown must start with one direct integer assignment",
        );
    };
    let [ast::Expr::Name(counter)] = initialize.targets.as_slice() else {
        return failure(
            "frontend.python.contracts.module-countdown-initializer",
            "module countdown initializer requires one direct name",
        );
    };
    let start = closed_module_int_literal(&initialize.value, "module countdown initializer")?;

    let ast::Stmt::While(loop_statement) = loop_statement else {
        return failure(
            "frontend.python.contracts.module-countdown-loop",
            "closed module countdown requires one while loop",
        );
    };
    if !loop_statement.orelse.is_empty() {
        return failure(
            "frontend.python.contracts.module-countdown-loop",
            "closed module countdown while does not permit an else suite",
        );
    }
    let ast::Expr::Compare(condition) = loop_statement.test.as_ref() else {
        return failure(
            "frontend.python.contracts.module-countdown-condition",
            "module countdown condition must compare its counter with an integer literal",
        );
    };
    let [ast::CmpOp::Gt] = condition.ops.as_slice() else {
        return failure(
            "frontend.python.contracts.module-countdown-condition",
            "module countdown condition must use a strict greater-than comparison",
        );
    };
    let ast::Expr::Name(condition_counter) = condition.left.as_ref() else {
        return failure(
            "frontend.python.contracts.module-countdown-condition",
            "module countdown condition requires its direct counter name",
        );
    };
    let [stop] = condition.comparators.as_slice() else {
        return failure(
            "frontend.python.contracts.module-countdown-condition",
            "module countdown condition requires one integer stopping value",
        );
    };
    if condition_counter.id != counter.id {
        return failure(
            "frontend.python.contracts.module-countdown-condition",
            "module countdown condition must read the initialized counter",
        );
    }
    let stop = closed_module_int_literal(stop, "module countdown stopping value")?;

    let invariant_count = loop_statement
        .body
        .iter()
        .take_while(|nested| contract_invariant(nested).is_some())
        .count();
    if invariant_count == 0 {
        return failure(
            "frontend.python.contracts.module-countdown-invariant",
            "module countdown requires at least one leading Invariant(...) contract",
        );
    }
    let [ast::Stmt::AugAssign(update)] = &loop_statement.body[invariant_count..] else {
        return failure(
            "frontend.python.contracts.module-countdown-body",
            "module countdown body permits only its invariant prefix and one decrement",
        );
    };
    if !matches!(update.op, ast::Operator::Sub)
        || !matches!(update.target.as_ref(), ast::Expr::Name(name) if name.id == counter.id)
    {
        return failure(
            "frontend.python.contracts.module-countdown-update",
            "module countdown must subtract a positive integer literal from its counter",
        );
    }
    let step = closed_module_int_literal(&update.value, "module countdown decrement")?;
    if step <= 0 {
        return failure(
            "frontend.python.contracts.module-countdown-update",
            "module countdown decrement must be strictly positive",
        );
    }
    let invariants = loop_statement.body[..invariant_count]
        .iter()
        .map(|invariant| {
            (
                contract_invariant(invariant)
                    .expect("invariant prefix was counted from these statements")
                    .clone(),
                u32::from(invariant.range().start()),
            )
        })
        .collect();

    let ast::Stmt::Assign(success) = success else {
        return failure(
            "frontend.python.contracts.module-countdown-result",
            "closed module countdown must finish with one direct list-index result assignment",
        );
    };
    let [ast::Expr::Name(result_binding)] = success.targets.as_slice() else {
        return failure(
            "frontend.python.contracts.module-countdown-result",
            "module countdown result requires one direct target name",
        );
    };
    let ast::Expr::List(result_list) = success.value.as_ref() else {
        return failure(
            "frontend.python.contracts.module-countdown-result",
            "module countdown result must wrap one indexed value in a list",
        );
    };
    let [ast::Expr::Subscript(indexed)] = result_list.elts.as_slice() else {
        return failure(
            "frontend.python.contracts.module-countdown-result",
            "module countdown result must contain exactly one subscript",
        );
    };
    let ast::Expr::Name(source_binding) = indexed.value.as_ref() else {
        return failure(
            "frontend.python.contracts.module-countdown-result",
            "module countdown subscript requires a direct source list",
        );
    };
    if !matches!(indexed.slice.as_ref(), ast::Expr::Name(name) if name.id == counter.id) {
        return failure(
            "frontend.python.contracts.module-countdown-result",
            "module countdown subscript must use the final counter value",
        );
    }

    let [ast::ExceptHandler::ExceptHandler(handler)] = statement.handlers.as_slice() else {
        return failure(
            "frontend.python.contracts.module-countdown-handler",
            "closed module countdown requires exactly one Exception handler",
        );
    };
    if !matches!(handler.type_.as_deref(), Some(ast::Expr::Name(name)) if name.id.as_str() == "Exception")
    {
        return failure(
            "frontend.python.contracts.module-countdown-handler",
            "closed module countdown handler must catch exactly Exception",
        );
    }
    let [ast::Stmt::Assign(fallback)] = handler.body.as_slice() else {
        return failure(
            "frontend.python.contracts.module-countdown-handler",
            "closed module countdown handler requires one direct fallback assignment",
        );
    };
    if !matches!(fallback.targets.as_slice(), [ast::Expr::Name(name)] if name.id == result_binding.id)
    {
        return failure(
            "frontend.python.contracts.module-countdown-handler",
            "module countdown fallback must assign the same result binding",
        );
    }
    if handler.name.as_ref().is_some_and(|name| {
        statement_unconditional_read_names(&handler.body[0]).contains(name.as_str())
    }) {
        return failure(
            "frontend.python.contracts.module-countdown-handler-binding",
            "closed module countdown fallback cannot inspect or escape its exception binding",
        );
    }

    Ok(ClosedModuleCountdownTry {
        counter: counter.id.to_string(),
        start,
        stop,
        step,
        invariants,
        result_binding: result_binding.id.to_string(),
        source_binding: source_binding.id.to_string(),
        fallback: fallback.value.as_ref().clone(),
    })
}

fn lower_closed_module_countdown_invariant(
    expression: &ast::Expr,
    counter: &str,
    lowerer: &ExpressionLowerer<'_>,
    environment: &BTreeMap<String, Term>,
    context: &str,
) -> Result<Term, ContractFailure> {
    if let ast::Expr::Call(call) = expression
        && call.args.len() == 1
        && call.keywords.is_empty()
        && matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Acc")
        && matches!(call.args.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == counter)
    {
        // Module initialization owns the binding it just created. This permission is scoped to
        // the closed countdown; Acc of any pre-existing module global still follows the ordinary
        // module-global permission path.
        return Ok(Term::Bool { value: true });
    }
    lowerer.lower_spec(expression, environment, None, context)
}

#[allow(clippy::too_many_arguments)]
fn apply_closed_module_countdown_try(
    statement: &ast::StmtTry,
    globals: &mut BTreeMap<String, Term>,
    available_functions: &BTreeMap<String, InlineFunction>,
    type_comments: &BTreeMap<u32, ScalarTypeComment>,
    exception_hierarchy: &ExceptionHierarchy,
    conformance_mode: bool,
    source: &str,
    path: &str,
    obligations: &mut Vec<Obligation>,
) -> Result<(), ContractFailure> {
    let shape = validate_closed_module_countdown_try(statement)?;
    if is_protected_module_metadata(&shape.counter)
        || is_protected_module_metadata(&shape.result_binding)
    {
        return failure(
            "frontend.python.contracts.module-countdown-protected-binding",
            "closed module countdown cannot assign protected module metadata",
        );
    }
    let Term::List {
        element_sort: source_element_sort,
        values: source_values,
    } = globals
        .get(&shape.source_binding)
        .cloned()
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-countdown-source",
            message: format!(
                "module countdown source list {:?} is not initialized before the try statement",
                shape.source_binding
            ),
        })?
    else {
        return failure(
            "frontend.python.contracts.module-countdown-source",
            "closed module countdown subscript source must be a finite list",
        );
    };

    let mut initial_environment = globals.clone();
    initial_environment.insert(shape.counter.clone(), Term::Int { value: shape.start });
    let initial_lowerer = ExpressionLowerer {
        functions: available_functions,
        globals: &initial_environment,
        type_comments,
        call_stack: vec!["<module-countdown-establishment>".to_owned()],
        exception_hierarchy,
        conformance_mode,
    };
    for (index, (expression, byte_offset)) in shape.invariants.iter().enumerate() {
        let conclusion = lower_closed_module_countdown_invariant(
            expression,
            &shape.counter,
            &initial_lowerer,
            &initial_environment,
            "module countdown invariant establishment",
        )?;
        ensure_boolean(&conclusion, "module countdown invariant")?;
        let (line, column) = source_location(source, *byte_offset);
        obligations.push(Obligation {
            id: format!("module:countdown-invariant-establishment:{index}"),
            expectation: ObligationExpectation::Prove,
            assumptions: Vec::new(),
            conclusion: conclusion.clone(),
            path: path.to_owned(),
            byte_offset: *byte_offset,
            line,
            column,
        });
    }

    let symbolic_counter = Term::Variable {
        name: format!("module::countdown:{}", u32::from(statement.range.start())),
        sort: Sort::Int,
    };
    let mut head_environment = globals.clone();
    head_environment.insert(shape.counter.clone(), symbolic_counter.clone());
    let head_lowerer = ExpressionLowerer {
        functions: available_functions,
        globals: &head_environment,
        type_comments,
        call_stack: vec!["<module-countdown-head>".to_owned()],
        exception_hierarchy,
        conformance_mode,
    };
    let mut head_invariants = Vec::with_capacity(shape.invariants.len());
    for (expression, _) in &shape.invariants {
        let invariant = lower_closed_module_countdown_invariant(
            expression,
            &shape.counter,
            &head_lowerer,
            &head_environment,
            "module countdown invariant assumption",
        )?;
        ensure_boolean(&invariant, "module countdown invariant")?;
        head_invariants.push(invariant);
    }
    let loop_condition = Term::Greater {
        left: Box::new(symbolic_counter.clone()),
        right: Box::new(Term::Int { value: shape.stop }),
    };
    let mut preservation_environment = head_environment;
    preservation_environment.insert(
        shape.counter.clone(),
        Term::Subtract {
            left: Box::new(symbolic_counter),
            right: Box::new(Term::Int { value: shape.step }),
        },
    );
    let preservation_lowerer = ExpressionLowerer {
        functions: available_functions,
        globals: &preservation_environment,
        type_comments,
        call_stack: vec!["<module-countdown-preservation>".to_owned()],
        exception_hierarchy,
        conformance_mode,
    };
    let mut preservation_assumptions = head_invariants;
    preservation_assumptions.push(loop_condition);
    for (index, (expression, byte_offset)) in shape.invariants.iter().enumerate() {
        let conclusion = lower_closed_module_countdown_invariant(
            expression,
            &shape.counter,
            &preservation_lowerer,
            &preservation_environment,
            "module countdown invariant preservation",
        )?;
        ensure_boolean(&conclusion, "module countdown invariant")?;
        let (line, column) = source_location(source, *byte_offset);
        obligations.push(Obligation {
            id: format!("module:countdown-invariant-preservation:{index}"),
            expectation: ObligationExpectation::Prove,
            assumptions: preservation_assumptions.clone(),
            conclusion,
            path: path.to_owned(),
            byte_offset: *byte_offset,
            line,
            column,
        });
    }

    let start = i128::from(shape.start);
    let stop = i128::from(shape.stop);
    let step = i128::from(shape.step);
    let iterations = if start <= stop {
        0
    } else {
        let distance = start - stop;
        let quotient = distance / step;
        quotient + i128::from(distance % step != 0)
    };
    let final_counter = start - iterations * step;
    let final_counter = i64::try_from(final_counter).map_err(|_| ContractFailure {
        code: "frontend.python.integer.out-of-range",
        message: "module countdown final value exceeds the scalar i64 range".to_owned(),
    })?;
    globals.insert(
        shape.counter.clone(),
        Term::Int {
            value: final_counter,
        },
    );

    let length = i128::try_from(source_values.len()).map_err(|_| ContractFailure {
        code: "frontend.python.contracts.sequence-length-overflow",
        message: "module countdown source list length exceeds the signed index frontend".to_owned(),
    })?;
    let index = i128::from(final_counter);
    let normalized = if index < 0 {
        index.checked_add(length)
    } else {
        Some(index)
    };
    let selected = normalized
        .filter(|index| *index >= 0 && *index < length)
        .and_then(|index| usize::try_from(index).ok())
        .and_then(|index| source_values.get(index).cloned());
    let result = if let Some(selected) = selected {
        Term::List {
            element_sort: source_element_sort,
            values: vec![selected],
        }
    } else {
        let fallback_lowerer = ExpressionLowerer {
            functions: available_functions,
            globals,
            type_comments,
            call_stack: vec!["<module-countdown-handler>".to_owned()],
            exception_hierarchy,
            conformance_mode,
        };
        fallback_lowerer.lower(&shape.fallback, globals, None)?
    };
    if !matches!(result.sort().map_err(type_failure)?, Sort::List(_)) {
        return failure(
            "frontend.python.contracts.module-countdown-handler",
            "module countdown success and fallback values must both be finite lists",
        );
    }
    globals.insert(shape.result_binding, result);
    Ok(())
}

fn validate_closed_module_list_append_ownership(
    suite: &[ast::Stmt],
    shape: &ClosedModuleListAppend,
) -> Result<(), ContractFailure> {
    if scalar_module_binding_count_for_suite(suite, &shape.binding) != 1 {
        return failure(
            "frontend.python.contracts.module-list-append-provenance",
            format!(
                "closed module list {:?} requires exactly one source-owned initializer",
                shape.binding
            ),
        );
    }
    let matching_functions = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => closed_module_list_append_function(function),
            _ => None,
        })
        .filter(|candidate| candidate.binding == shape.binding)
        .count();
    if matching_functions != 1 {
        return failure(
            "frontend.python.contracts.module-list-append-function-count",
            "closed module list append requires exactly one owning append function",
        );
    }
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) if function.name.as_str() == shape.function => {}
            ast::Stmt::FunctionDef(_) => {
                return failure(
                    "frontend.python.contracts.module-list-append-escape",
                    "closed module list append cannot share its module with another function",
                );
            }
            ast::Stmt::Assign(assignment) if matches!(assignment.targets.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == shape.binding) => {
                if !matches!(assignment.value.as_ref(), ast::Expr::List(_)) {
                    return failure(
                        "frontend.python.contracts.module-list-append-provenance",
                        "closed module list append requires a direct finite list initializer",
                    );
                }
            }
            ast::Stmt::AnnAssign(assignment) if matches!(assignment.target.as_ref(), ast::Expr::Name(name) if name.id.as_str() == shape.binding) => {
                if !matches!(assignment.value.as_deref(), Some(ast::Expr::List(_))) {
                    return failure(
                        "frontend.python.contracts.module-list-append-provenance",
                        "closed module list append requires a direct finite list initializer",
                    );
                }
            }
            ast::Stmt::Expr(expression)
                if closed_module_list_append_call(suite, &expression.value)
                    .is_some_and(|candidate| candidate.function == shape.function) => {}
            _ if statement_unconditional_read_names(statement).contains(&shape.binding) => {
                return failure(
                    "frontend.python.contracts.module-list-append-alias",
                    format!(
                        "closed module list {:?} is read or escapes outside its owning append function",
                        shape.binding
                    ),
                );
            }
            _ => {}
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn apply_closed_module_list_append_call(
    suite: &[ast::Stmt],
    expression: &ast::StmtExpr,
    globals: &mut BTreeMap<String, Term>,
    available_functions: &BTreeMap<String, InlineFunction>,
    type_comments: &BTreeMap<u32, ScalarTypeComment>,
    exception_hierarchy: &ExceptionHierarchy,
    conformance_mode: bool,
    source: &str,
    path: &str,
    obligations: &mut Vec<Obligation>,
) -> Result<(), ContractFailure> {
    let shape = closed_module_list_append_call(suite, &expression.value).ok_or_else(|| {
        ContractFailure {
            code: "frontend.python.contracts.module-list-append-call-shape",
            message: "module expression is not a closed source-owned list append call".to_owned(),
        }
    })?;
    validate_closed_module_list_append_ownership(suite, &shape)?;
    let summary = available_functions
        .get(&shape.function)
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-list-append-function-order",
            message: format!(
                "closed module list append function {:?} is called before its definition",
                shape.function
            ),
        })?;
    let lowerer = ExpressionLowerer {
        functions: available_functions,
        globals,
        type_comments,
        call_stack: vec!["<module-list-append-call>".to_owned()],
        exception_hierarchy,
        conformance_mode,
    };
    let byte_offset = u32::from(expression.range.start());
    for (precondition_index, precondition) in summary.preconditions.iter().enumerate() {
        for (clause_index, conclusion) in lowerer
            .lower_specification_clauses(
                precondition,
                globals,
                None,
                "module list append call precondition",
            )?
            .into_iter()
            .enumerate()
        {
            ensure_boolean(&conclusion, "module list append call precondition")?;
            let (line, column) = source_location(source, byte_offset);
            obligations.push(Obligation {
                id: format!(
                    "module:call-precondition:{precondition_index}:{clause_index}:{}",
                    obligations.len()
                ),
                expectation: ObligationExpectation::Prove,
                assumptions: Vec::new(),
                conclusion,
                path: path.to_owned(),
                byte_offset,
                line,
                column,
            });
        }
    }
    let current = globals
        .get(&shape.binding)
        .cloned()
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-list-append-provenance",
            message: format!(
                "closed module list {:?} is unavailable at its call site",
                shape.binding
            ),
        })?;
    let Term::List {
        element_sort,
        mut values,
    } = current
    else {
        return failure(
            "frontend.python.contracts.module-list-append-type",
            "closed module list append receiver must remain a finite list",
        );
    };
    if element_sort != Sort::Int {
        return failure(
            "frontend.python.contracts.module-list-append-type",
            format!("closed module list append requires List[int], found List[{element_sort:?}]"),
        );
    }
    values
        .try_reserve_exact(1)
        .map_err(|error| ContractFailure {
            code: "frontend.python.contracts.module-list-append-allocation-failed",
            message: format!("closed module list append could not reserve one element: {error}"),
        })?;
    values.push(Term::Int { value: shape.value });
    globals.insert(
        shape.binding,
        Term::List {
            element_sort,
            values,
        },
    );
    Ok(())
}

fn validate_closed_module_int_update_ownership(
    suite: &[ast::Stmt],
    binding: &str,
) -> Result<(), ContractFailure> {
    let shapes = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => closed_module_int_update_function(function),
            _ => None,
        })
        .filter(|shape| shape.binding == binding)
        .collect::<Vec<_>>();
    if shapes.is_empty() {
        return failure(
            "frontend.python.contracts.module-int-update-function",
            format!("closed module int {binding:?} has no owning update function"),
        );
    }
    if scalar_module_binding_count_for_suite(suite, binding) != 1 {
        return failure(
            "frontend.python.contracts.module-int-update-provenance",
            format!("closed module int {binding:?} requires exactly one source-owned initializer"),
        );
    }

    let mut initialized = false;
    let mut owned = false;
    let mut failed_call_seen = false;
    let mut module_update_count = 0usize;
    let maximum_minimum = shapes
        .iter()
        .map(|shape| shape.minimum)
        .max()
        .expect("nonempty shapes checked");
    for statement in suite {
        match statement {
            ast::Stmt::Assign(assignment) if matches!(assignment.targets.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == binding) =>
            {
                if initialized || failed_call_seen {
                    return failure(
                        "frontend.python.contracts.module-int-update-provenance",
                        format!("closed module int {binding:?} is rebound outside its initializer"),
                    );
                }
                let initial =
                    closed_module_int_literal(&assignment.value, "closed module int initializer")?;
                if initial < maximum_minimum {
                    return failure(
                        "frontend.python.contracts.module-int-update-lower-bound",
                        format!(
                            "closed module int {binding:?} initializer {initial} is below required minimum {maximum_minimum}"
                        ),
                    );
                }
                initialized = true;
                owned = true;
            }
            ast::Stmt::AugAssign(assignment) if matches!(assignment.target.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binding) =>
            {
                if !initialized || !owned || failed_call_seen {
                    return failure(
                        "frontend.python.contracts.module-int-update-order",
                        format!(
                            "closed module int {binding:?} update requires its live source-owned initializer"
                        ),
                    );
                }
                let Some((candidate, _)) = closed_module_int_augassign(suite, assignment) else {
                    return failure(
                        "frontend.python.contracts.module-int-update-shape",
                        "closed module int initialization permits only a positive int-literal += update",
                    );
                };
                if candidate != binding {
                    return failure(
                        "frontend.python.contracts.module-int-update-binding",
                        "closed module int update changed binding after recognition",
                    );
                }
                module_update_count += 1;
            }
            ast::Stmt::FunctionDef(function) => {
                if !closed_module_int_update_function(function)
                    .is_some_and(|shape| shape.binding == binding)
                {
                    return failure(
                        "frontend.python.contracts.module-int-update-escape",
                        format!(
                            "closed module int {binding:?} cannot share its module with an unrecognized function"
                        ),
                    );
                }
            }
            ast::Stmt::Expr(expression)
                if closed_module_int_update_call(suite, &expression.value)
                    .is_some_and(|shape| shape.binding == binding) =>
            {
                if !initialized || failed_call_seen {
                    return failure(
                        "frontend.python.contracts.module-int-update-order",
                        format!(
                            "closed module int {binding:?} call occurs outside its live execution prefix"
                        ),
                    );
                }
                let shape = closed_module_int_update_call(suite, &expression.value)
                    .expect("guard established recognized call");
                if owned {
                    owned = shape.returns_permission;
                } else {
                    failed_call_seen = true;
                }
            }
            ast::Stmt::Assert(assertion)
                if statement_unconditional_read_names(statement).contains(binding) =>
            {
                if !owned || failed_call_seen || assertion.msg.is_some() {
                    return failure(
                        "frontend.python.contracts.module-int-update-read",
                        format!(
                            "closed module int {binding:?} may be asserted only while its permission is owned"
                        ),
                    );
                }
            }
            _ if statement_unconditional_read_names(statement).contains(binding) => {
                return failure(
                    "frontend.python.contracts.module-int-update-alias",
                    format!(
                        "closed module int {binding:?} is read or escapes outside its certified update sequence"
                    ),
                );
            }
            _ => {}
        }
    }
    if !initialized || module_update_count != 1 {
        return failure(
            "frontend.python.contracts.module-int-update-provenance",
            format!(
                "closed module int {binding:?} requires one initializer and one module-level += update"
            ),
        );
    }
    Ok(())
}

fn validate_closed_module_folded_int_ownership(
    suite: &[ast::Stmt],
    shape: &ClosedModuleFoldedIntUpdate,
) -> Result<(), ContractFailure> {
    if scalar_module_binding_count_for_suite(suite, &shape.binding) != 1 {
        return failure(
            "frontend.python.contracts.module-folded-int-provenance",
            format!(
                "folded module int {:?} requires exactly one source-owned initializer",
                shape.binding
            ),
        );
    }
    let mut initialized = false;
    let mut definitions = BTreeSet::new();
    let mut folded = false;
    let mut calls = 0usize;
    for statement in suite {
        match statement {
            ast::Stmt::Assign(assignment) if matches!(assignment.targets.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == shape.binding) =>
            {
                if initialized || folded || calls != 0 {
                    return failure(
                        "frontend.python.contracts.module-folded-int-provenance",
                        "folded module int is rebound outside its unique initializer",
                    );
                }
                let initial =
                    closed_module_int_literal(&assignment.value, "folded module int initializer")?;
                if initial != shape.maximum {
                    return failure(
                        "frontend.python.contracts.module-folded-int-initial-value",
                        format!(
                            "folded module int initializer {initial} must equal the source precondition boundary {}",
                            shape.maximum
                        ),
                    );
                }
                initialized = true;
            }
            ast::Stmt::FunctionDef(function)
                if matches!(function.name.as_str(), name
                    if name == shape.predicate || name == shape.getter || name == shape.updater) =>
            {
                definitions.insert(function.name.to_string());
            }
            ast::Stmt::FunctionDef(_) => {
                return failure(
                    "frontend.python.contracts.module-folded-int-escape",
                    "folded module int cannot share its closed module with another function",
                );
            }
            ast::Stmt::Expr(expression) if is_closed_module_fold_call(&expression.value, shape) => {
                if !initialized || folded || calls != 0 || !definitions.contains(&shape.predicate) {
                    return failure(
                        "frontend.python.contracts.module-folded-int-fold-order",
                        "folded module int requires one predicate Fold after initialization and definition",
                    );
                }
                folded = true;
            }
            ast::Stmt::Expr(expression)
                if is_closed_module_folded_int_call(&expression.value, shape) =>
            {
                if !folded || !definitions.contains(&shape.updater) || calls >= 2 {
                    return failure(
                        "frontend.python.contracts.module-folded-int-call-order",
                        "folded module int requires exactly two ordered calls after Fold",
                    );
                }
                calls += 1;
            }
            _ if statement_unconditional_read_names(statement).contains(&shape.binding) => {
                return failure(
                    "frontend.python.contracts.module-folded-int-alias",
                    format!(
                        "folded module int {:?} is read or escapes outside its certified predicate protocol",
                        shape.binding
                    ),
                );
            }
            _ => {}
        }
    }
    let expected_definitions = BTreeSet::from([
        shape.predicate.clone(),
        shape.getter.clone(),
        shape.updater.clone(),
    ]);
    if !initialized || !folded || calls != 2 || definitions != expected_definitions {
        return failure(
            "frontend.python.contracts.module-folded-int-protocol",
            "folded module int requires its initializer, three owning functions, one Fold, and two calls",
        );
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn apply_closed_module_folded_int_call(
    expression: &ast::StmtExpr,
    shape: &ClosedModuleFoldedIntUpdate,
    folded: bool,
    globals: &mut BTreeMap<String, Term>,
    source: &str,
    path: &str,
    obligations: &mut Vec<Obligation>,
) -> Result<(), ContractFailure> {
    if !is_closed_module_folded_int_call(&expression.value, shape) {
        return failure(
            "frontend.python.contracts.module-folded-int-call-shape",
            "module expression is not the certified folded int updater call",
        );
    }
    let current = globals
        .get(&shape.binding)
        .cloned()
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-folded-int-provenance",
            message: format!(
                "folded module int {:?} is unavailable at its call site",
                shape.binding
            ),
        })?;
    let current = coerce_python_int(current, "folded module int update receiver")?;
    let conclusion = Term::And {
        values: vec![
            Term::Bool { value: folded },
            Term::LessEqual {
                left: Box::new(current.clone()),
                right: Box::new(Term::Int {
                    value: shape.maximum,
                }),
            },
        ],
    };
    let byte_offset = u32::from(expression.range.start());
    let obligation = Obligation {
        id: format!("module:call-precondition:folded-int:{}", obligations.len()),
        expectation: ObligationExpectation::Prove,
        assumptions: Vec::new(),
        conclusion,
        path: path.to_owned(),
        byte_offset,
        line: source_location(source, byte_offset).0,
        column: source_location(source, byte_offset).1,
    };
    let satisfied = discharge(&obligation)
        .map_err(|message| ContractFailure {
            code: "solver.translation-failed",
            message,
        })?
        .satisfied();
    obligations.push(obligation);
    if satisfied {
        globals.insert(
            shape.binding.clone(),
            Term::Add {
                left: Box::new(current),
                right: Box::new(Term::Int {
                    value: shape.increment,
                }),
            },
        );
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn apply_closed_module_int_update_call(
    suite: &[ast::Stmt],
    expression: &ast::StmtExpr,
    globals: &mut BTreeMap<String, Term>,
    permissions: &mut BTreeMap<String, bool>,
    available_functions: &BTreeMap<String, InlineFunction>,
    type_comments: &BTreeMap<u32, ScalarTypeComment>,
    exception_hierarchy: &ExceptionHierarchy,
    conformance_mode: bool,
    source: &str,
    path: &str,
    obligations: &mut Vec<Obligation>,
) -> Result<(), ContractFailure> {
    let shape =
        closed_module_int_update_call(suite, &expression.value).ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-int-update-call-shape",
            message: "module expression is not a closed source-owned int update call".to_owned(),
        })?;
    validate_closed_module_int_update_ownership(suite, &shape.binding)?;
    available_functions
        .get(&shape.function)
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-int-update-function-order",
            message: format!(
                "closed module int update function {:?} is called before its definition",
                shape.function
            ),
        })?;
    let function = suite
        .iter()
        .find_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) if function.name.as_str() == shape.function => {
                Some(function)
            }
            _ => None,
        })
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-int-update-function",
            message: format!(
                "closed module int update function {:?} disappeared after recognition",
                shape.function
            ),
        })?;
    let precondition =
        direct_contract_argument(&function.body[1], "Requires").ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-int-update-precondition",
            message: format!(
                "closed module int update function {:?} lost its canonical precondition",
                shape.function
            ),
        })?;
    let owned = permissions.get(&shape.binding).copied().unwrap_or(false);
    let lowerer = ExpressionLowerer {
        functions: available_functions,
        globals,
        type_comments,
        call_stack: vec!["<module-int-update-call>".to_owned()],
        exception_hierarchy,
        conformance_mode,
    };
    let byte_offset = u32::from(expression.range.start());
    let mut preconditions_satisfied = true;
    for (clause_index, clause) in lowerer
        .lower_specification_clauses(
            precondition,
            globals,
            None,
            "module int update call precondition",
        )?
        .into_iter()
        .enumerate()
    {
        let conclusion = instantiate_frontend_bound_term(
            &clause,
            &format!("module-global-permission::{}", shape.binding),
            &Term::Bool { value: owned },
        )?;
        ensure_boolean(&conclusion, "module int update call precondition")?;
        let obligation = Obligation {
            id: format!(
                "module:{}:0:{clause_index}:{}",
                if owned {
                    "call-precondition"
                } else {
                    "call-permission-precondition"
                },
                obligations.len()
            ),
            expectation: ObligationExpectation::Prove,
            assumptions: Vec::new(),
            conclusion,
            path: path.to_owned(),
            byte_offset,
            line: source_location(source, byte_offset).0,
            column: source_location(source, byte_offset).1,
        };
        preconditions_satisfied &= discharge(&obligation)
            .map_err(|message| ContractFailure {
                code: "solver.translation-failed",
                message,
            })?
            .satisfied();
        obligations.push(obligation);
    }
    if !preconditions_satisfied {
        return Ok(());
    }
    let current = globals
        .get(&shape.binding)
        .cloned()
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.module-int-update-provenance",
            message: format!(
                "closed module int {:?} is unavailable at its call site",
                shape.binding
            ),
        })?;
    let current = coerce_python_int(current, "closed module int update receiver")?;
    globals.insert(
        shape.binding.clone(),
        Term::Add {
            left: Box::new(current),
            right: Box::new(Term::Int {
                value: shape.increment,
            }),
        },
    );
    permissions.insert(shape.binding, shape.returns_permission);
    Ok(())
}

fn derive_immutable_module_globals(
    suite: &[ast::Stmt],
    context: ModuleDerivationContext<'_>,
) -> Result<ImmutableModuleGlobals, ContractFailure> {
    let ModuleDerivationContext {
        source,
        path,
        functions: all_functions,
        type_comments,
        exception_hierarchy,
        conformance_mode,
        identity: module_identity,
    } = context;
    let mut globals = BTreeMap::from([
        (
            "__name__".to_owned(),
            Term::String {
                value: module_identity.name.clone(),
            },
        ),
        (
            "__file__".to_owned(),
            Term::String {
                value: module_identity.file.clone(),
            },
        ),
        ("Ellipsis".to_owned(), ellipsis_singleton()),
    ]);
    let mut available_functions = BTreeMap::new();
    let mut identities = BTreeMap::from([(
        "Ellipsis".to_owned(),
        PythonObjectIdentity::EllipsisSingleton,
    )]);
    if suite.iter().any(|statement| {
        matches!(statement, ast::Stmt::ImportFrom(import)
            if is_canonical_ellipsis_type_import(import))
    }) {
        globals.insert("EllipsisType".to_owned(), ellipsis_type_object());
    }
    let mut initialization_failure = None;
    let mut list_mutations = Vec::new();
    let mut obligations = Vec::new();
    let mut closed_module_int_permissions = BTreeMap::new();
    let closed_module_folded_int = closed_module_folded_int_update(suite);
    let mut closed_module_folded_int_is_folded = false;
    let mut shadowed_builtin_types = BTreeSet::new();
    let mut reserved_bindings = all_functions.keys().cloned().collect::<BTreeSet<_>>();
    for statement in suite {
        match statement {
            ast::Stmt::ImportFrom(import) => {
                reserved_bindings.extend(
                    import
                        .names
                        .iter()
                        .filter(|alias| alias.name.as_str() != "*")
                        .map(|alias| {
                            alias
                                .asname
                                .as_ref()
                                .map_or_else(|| alias.name.to_string(), ToString::to_string)
                        }),
                );
            }
            ast::Stmt::ClassDef(class) => {
                reserved_bindings.insert(class.name.to_string());
            }
            _ => {}
        }
    }
    for statement in suite {
        match statement {
            ast::Stmt::ImportFrom(import) => {
                for alias in &import.names {
                    let imported_name = alias.name.as_str();
                    let local_name = alias
                        .asname
                        .as_ref()
                        .map_or(imported_name, |name| name.as_str());
                    if let Some(summary) = all_functions.get(local_name) {
                        available_functions.insert(local_name.to_owned(), summary.clone());
                    }
                    shadowed_builtin_types.insert(local_name.to_owned());
                }
            }
            ast::Stmt::FunctionDef(function) => {
                if let Some(summary) = all_functions.get(function.name.as_str()) {
                    if function_definition_has_undefined_default(
                        summary,
                        all_functions,
                        &available_functions,
                        &globals,
                        type_comments,
                        exception_hierarchy,
                        conformance_mode,
                    )? {
                        initialization_failure = Some(ModuleInitializationFailure {
                            binding: function.name.to_string(),
                            byte_offset: statement.range().start().into(),
                        });
                        break;
                    }
                    available_functions.insert(function.name.to_string(), summary.clone());
                }
                shadowed_builtin_types.insert(function.name.to_string());
            }
            ast::Stmt::ClassDef(class) if is_scalar_int_subclass(class) => {
                if let Some(summary) = all_functions.get(class.name.as_str()) {
                    available_functions.insert(class.name.to_string(), summary.clone());
                }
                shadowed_builtin_types.insert(class.name.to_string());
            }
            ast::Stmt::ClassDef(class) => {
                shadowed_builtin_types.insert(class.name.to_string());
            }
            ast::Stmt::Assign(assignment) => {
                let [target] = assignment.targets.as_slice() else {
                    return failure(
                        "frontend.python.contracts.module-assignment-target-unsupported",
                        "immutable module initialization requires exactly one assignment target",
                    );
                };
                let ast::Expr::Name(target) = target else {
                    initialization_failure = apply_static_module_unpacking(
                        target,
                        &assignment.value,
                        statement,
                        ModuleUnpackingContext {
                            source,
                            path,
                            all_functions,
                            available_functions: &available_functions,
                            type_comments,
                            exception_hierarchy,
                            conformance_mode,
                            reserved_bindings: &reserved_bindings,
                            globals: &mut globals,
                            identities: &mut identities,
                            obligations: &mut obligations,
                            shadowed_builtin_types: &mut shadowed_builtin_types,
                        },
                    )?;
                    if initialization_failure.is_some() {
                        break;
                    }
                    continue;
                };
                if is_protected_module_metadata(target.id.as_str()) {
                    obligations.push(module_obligation(
                        format!("module:field-write-permission:{}", target.id),
                        Term::Bool { value: false },
                        statement,
                        source,
                        path,
                    ));
                    continue;
                }
                ensure_unreserved_module_binding(target.id.as_str(), &reserved_bindings)?;
                ensure_canonical_identity_constructor_bindings(
                    &assignment.value,
                    &shadowed_builtin_types,
                )?;
                if first_unavailable_initializer_function(
                    &assignment.value,
                    all_functions,
                    &available_functions,
                )
                .is_some()
                {
                    initialization_failure = Some(ModuleInitializationFailure {
                        binding: target.id.to_string(),
                        byte_offset: statement.range().start().into(),
                    });
                    break;
                }
                let object_identity =
                    python_object_identity(&assignment.value, &globals, &identities);
                insert_immutable_module_global(
                    target.id.as_str(),
                    &assignment.value,
                    None,
                    &mut globals,
                    &available_functions,
                    type_comments,
                    exception_hierarchy,
                    conformance_mode,
                    &shadowed_builtin_types,
                )?;
                if suite.iter().any(|statement| {
                    matches!(statement, ast::Stmt::FunctionDef(function)
                        if closed_module_int_update_function(function)
                            .is_some_and(|shape| shape.binding.as_str() == target.id.as_str()))
                }) {
                    closed_module_int_permissions.insert(target.id.to_string(), true);
                }
                if let Some(object_identity) = object_identity {
                    identities.insert(target.id.to_string(), object_identity);
                } else {
                    identities.remove(target.id.as_str());
                }
                shadowed_builtin_types.insert(target.id.to_string());
            }
            ast::Stmt::AnnAssign(assignment) => {
                let ast::Expr::Name(target) = assignment.target.as_ref() else {
                    return failure(
                        "frontend.python.contracts.module-assignment-target-unsupported",
                        "immutable module initialization requires a direct annotated name target",
                    );
                };
                if is_protected_module_metadata(target.id.as_str()) {
                    obligations.push(module_obligation(
                        format!("module:field-write-permission:{}", target.id),
                        Term::Bool { value: false },
                        statement,
                        source,
                        path,
                    ));
                    continue;
                }
                let value = assignment.value.as_deref().ok_or_else(|| ContractFailure {
                    code: "frontend.python.contracts.module-annotation-without-value",
                    message: format!(
                        "module global {:?} has an annotation but no initialization value",
                        target.id
                    ),
                })?;
                ensure_unreserved_module_binding(target.id.as_str(), &reserved_bindings)?;
                ensure_canonical_identity_constructor_bindings(value, &shadowed_builtin_types)?;
                let expected = annotation_sort(Some(&assignment.annotation))?;
                if first_unavailable_initializer_function(
                    value,
                    all_functions,
                    &available_functions,
                )
                .is_some()
                {
                    initialization_failure = Some(ModuleInitializationFailure {
                        binding: target.id.to_string(),
                        byte_offset: statement.range().start().into(),
                    });
                    break;
                }
                let object_identity = python_object_identity(value, &globals, &identities);
                insert_immutable_module_global(
                    target.id.as_str(),
                    value,
                    Some(&expected),
                    &mut globals,
                    &available_functions,
                    type_comments,
                    exception_hierarchy,
                    conformance_mode,
                    &shadowed_builtin_types,
                )?;
                if let Some(object_identity) = object_identity {
                    identities.insert(target.id.to_string(), object_identity);
                } else {
                    identities.remove(target.id.as_str());
                }
                shadowed_builtin_types.insert(target.id.to_string());
            }
            ast::Stmt::AugAssign(assignment) => {
                if let ast::Expr::Name(target) = assignment.target.as_ref()
                    && is_protected_module_metadata(target.id.as_str())
                {
                    obligations.push(module_obligation(
                        format!("module:field-write-permission:{}", target.id),
                        Term::Bool { value: false },
                        statement,
                        source,
                        path,
                    ));
                    continue;
                }
                if let Some((binding, increment)) = closed_module_int_augassign(suite, assignment) {
                    validate_closed_module_int_update_ownership(suite, &binding)?;
                    if !closed_module_int_permissions
                        .get(&binding)
                        .copied()
                        .unwrap_or(false)
                    {
                        return failure(
                            "frontend.python.contracts.module-int-update-permission",
                            format!(
                                "closed module int {binding:?} update lacks its source-owned permission"
                            ),
                        );
                    }
                    let current = globals.get(&binding).cloned().ok_or_else(|| {
                        ContractFailure {
                            code: "frontend.python.contracts.module-int-update-provenance",
                            message: format!(
                                "closed module int {binding:?} is unavailable for its initializer update"
                            ),
                        }
                    })?;
                    let current =
                        coerce_python_int(current, "closed module int initializer update")?;
                    globals.insert(
                        binding,
                        Term::Add {
                            left: Box::new(current),
                            right: Box::new(Term::Int { value: increment }),
                        },
                    );
                    continue;
                }
                let shape = validate_module_list_augassign_shape(suite, assignment)?;
                list_mutations.push(apply_module_list_augassign(
                    assignment,
                    &shape,
                    &mut globals,
                    &available_functions,
                    type_comments,
                    exception_hierarchy,
                    conformance_mode,
                )?);
            }
            ast::Stmt::Try(try_statement) => {
                apply_closed_module_countdown_try(
                    try_statement,
                    &mut globals,
                    &available_functions,
                    type_comments,
                    exception_hierarchy,
                    conformance_mode,
                    source,
                    path,
                    &mut obligations,
                )?;
            }
            ast::Stmt::Expr(expression)
                if closed_module_folded_int
                    .as_ref()
                    .is_some_and(|shape| is_closed_module_fold_call(&expression.value, shape)) =>
            {
                let shape = closed_module_folded_int
                    .as_ref()
                    .expect("guard established folded module int Fold");
                validate_closed_module_folded_int_ownership(suite, shape)?;
                closed_module_folded_int_is_folded = true;
            }
            ast::Stmt::Expr(expression)
                if closed_module_folded_int.as_ref().is_some_and(|shape| {
                    is_closed_module_folded_int_call(&expression.value, shape)
                }) =>
            {
                let shape = closed_module_folded_int
                    .as_ref()
                    .expect("guard established folded module int call");
                validate_closed_module_folded_int_ownership(suite, shape)?;
                apply_closed_module_folded_int_call(
                    expression,
                    shape,
                    closed_module_folded_int_is_folded,
                    &mut globals,
                    source,
                    path,
                    &mut obligations,
                )?;
            }
            ast::Stmt::Expr(expression)
                if closed_module_int_update_call(suite, &expression.value).is_some() =>
            {
                apply_closed_module_int_update_call(
                    suite,
                    expression,
                    &mut globals,
                    &mut closed_module_int_permissions,
                    &available_functions,
                    type_comments,
                    exception_hierarchy,
                    conformance_mode,
                    source,
                    path,
                    &mut obligations,
                )?;
            }
            ast::Stmt::Expr(expression)
                if closed_module_list_append_call(suite, &expression.value).is_some() =>
            {
                apply_closed_module_list_append_call(
                    suite,
                    expression,
                    &mut globals,
                    &available_functions,
                    type_comments,
                    exception_hierarchy,
                    conformance_mode,
                    source,
                    path,
                    &mut obligations,
                )?;
            }
            ast::Stmt::Assert(assertion) => {
                if assertion.msg.is_some() {
                    return failure(
                        "frontend.python.contracts.module-assert-message-unsupported",
                        "module assertions with failure-message expressions are not yet modeled",
                    );
                }
                ensure_canonical_identity_constructor_bindings(
                    &assertion.test,
                    &shadowed_builtin_types,
                )?;
                let lowerer = ExpressionLowerer {
                    functions: &available_functions,
                    globals: &globals,
                    type_comments,
                    call_stack: vec!["<module-assert>".to_owned()],
                    exception_hierarchy,
                    conformance_mode,
                };
                let conclusion =
                    lower_proven_object_identity(&assertion.test, &lowerer, &globals, &identities)?
                        .map(Ok)
                        .unwrap_or_else(|| {
                            lowerer.lower_spec(&assertion.test, &globals, None, "module assertion")
                        })?;
                let conclusion = coerce_truthy(conclusion, "module assertion")?;
                obligations.push(module_obligation(
                    "module:assert".to_owned(),
                    conclusion,
                    statement,
                    source,
                    path,
                ));
            }
            _ => {}
        }
    }
    Ok(ImmutableModuleGlobals {
        values: globals,
        initialization_failure,
        list_mutations,
        obligations,
    })
}

struct ModuleUnpackingContext<'a> {
    source: &'a str,
    path: &'a str,
    all_functions: &'a BTreeMap<String, InlineFunction>,
    available_functions: &'a BTreeMap<String, InlineFunction>,
    type_comments: &'a BTreeMap<u32, ScalarTypeComment>,
    exception_hierarchy: &'a ExceptionHierarchy,
    conformance_mode: bool,
    reserved_bindings: &'a BTreeSet<String>,
    globals: &'a mut BTreeMap<String, Term>,
    identities: &'a mut BTreeMap<String, PythonObjectIdentity>,
    obligations: &'a mut Vec<Obligation>,
    shadowed_builtin_types: &'a mut BTreeSet<String>,
}

fn apply_static_module_unpacking(
    target: &ast::Expr,
    value: &ast::Expr,
    statement: &ast::Stmt,
    context: ModuleUnpackingContext<'_>,
) -> Result<Option<ModuleInitializationFailure>, ContractFailure> {
    let mut bindings = Vec::new();
    collect_static_module_unpacking(target, value, &mut bindings)?;

    let mut unique_names = BTreeSet::new();
    for (target, initializer) in &bindings {
        let name = target.id.as_str();
        if !unique_names.insert(name) {
            return failure(
                "frontend.python.contracts.module-binding-reassigned",
                format!("module unpacking assigns binding {name:?} more than once"),
            );
        }
        if !is_protected_module_metadata(name) {
            ensure_unreserved_module_binding(name, context.reserved_bindings)?;
            if context.globals.contains_key(name) || context.available_functions.contains_key(name)
            {
                return failure(
                    "frontend.python.contracts.module-binding-reassigned",
                    format!("module binding {name:?} is already assigned or shadows a function"),
                );
            }
        }
        ensure_canonical_identity_constructor_bindings(
            initializer,
            context.shadowed_builtin_types,
        )?;
        if first_unavailable_initializer_function(
            initializer,
            context.all_functions,
            context.available_functions,
        )
        .is_some()
        {
            return Ok(Some(ModuleInitializationFailure {
                binding: name.to_owned(),
                byte_offset: statement.range().start().into(),
            }));
        }
    }

    // Python evaluates the complete right-hand side before assigning any target. Lower every
    // leaf against the same pre-assignment environment, then publish the prepared bindings.
    let lowerer = ExpressionLowerer {
        functions: context.available_functions,
        globals: context.globals,
        type_comments: context.type_comments,
        call_stack: vec!["<module-unpacking>".to_owned()],
        exception_hierarchy: context.exception_hierarchy,
        conformance_mode: context.conformance_mode,
    };
    let mut prepared = Vec::with_capacity(bindings.len());
    for (target, initializer) in bindings {
        let value = canonical_builtin_type_object(initializer, context.shadowed_builtin_types)
            .map(Ok)
            .unwrap_or_else(|| {
                lowerer.lower_spec(
                    initializer,
                    context.globals,
                    None,
                    "module unpacking initializer",
                )
            })?;
        value.sort().map_err(type_failure)?;
        prepared.push((
            target.id.to_string(),
            value,
            python_object_identity(initializer, context.globals, context.identities),
        ));
    }

    for (name, value, identity) in prepared {
        if is_protected_module_metadata(&name) {
            context.obligations.push(module_obligation(
                format!("module:field-write-permission:{name}"),
                Term::Bool { value: false },
                statement,
                context.source,
                context.path,
            ));
            continue;
        }
        context.globals.insert(name.clone(), value);
        if let Some(identity) = identity {
            context.identities.insert(name.clone(), identity);
        }
        context.shadowed_builtin_types.insert(name);
    }
    Ok(None)
}

fn collect_static_module_unpacking<'a>(
    target: &'a ast::Expr,
    value: &'a ast::Expr,
    bindings: &mut Vec<(&'a ast::ExprName, &'a ast::Expr)>,
) -> Result<(), ContractFailure> {
    match target {
        ast::Expr::Name(name) => {
            bindings.push((name, value));
            Ok(())
        }
        ast::Expr::Tuple(targets) => {
            let ast::Expr::Tuple(values) = value else {
                return failure(
                    "frontend.python.contracts.module-unpacking-value-unsupported",
                    "tuple unpacking requires a statically sized tuple value",
                );
            };
            collect_static_module_unpacking_elements(&targets.elts, &values.elts, bindings)
        }
        ast::Expr::List(targets) => {
            let ast::Expr::List(values) = value else {
                return failure(
                    "frontend.python.contracts.module-unpacking-value-unsupported",
                    "list unpacking requires a statically sized list value",
                );
            };
            collect_static_module_unpacking_elements(&targets.elts, &values.elts, bindings)
        }
        ast::Expr::Starred(_) => failure(
            "frontend.python.contracts.module-unpacking-starred-unsupported",
            "starred module unpacking has variable-length semantics",
        ),
        _ => failure(
            "frontend.python.contracts.module-unpacking-target-unsupported",
            "module unpacking targets must be names or nested tuple/list patterns",
        ),
    }
}

fn collect_static_module_unpacking_elements<'a>(
    targets: &'a [ast::Expr],
    values: &'a [ast::Expr],
    bindings: &mut Vec<(&'a ast::ExprName, &'a ast::Expr)>,
) -> Result<(), ContractFailure> {
    if targets.len() != values.len() {
        return failure(
            "frontend.python.contracts.module-unpacking-arity",
            format!(
                "module unpacking has {} targets but {} values",
                targets.len(),
                values.len()
            ),
        );
    }
    for (target, value) in targets.iter().zip(values) {
        collect_static_module_unpacking(target, value, bindings)?;
    }
    Ok(())
}

fn module_obligation(
    id: String,
    conclusion: Term,
    statement: &ast::Stmt,
    source: &str,
    path: &str,
) -> Obligation {
    let byte_offset = u32::from(statement.range().start());
    let (line, column) = source_location(source, byte_offset);
    Obligation {
        id,
        expectation: ObligationExpectation::Prove,
        assumptions: Vec::new(),
        conclusion,
        path: path.to_owned(),
        byte_offset,
        line,
        column,
    }
}

fn first_unavailable_initializer_function(
    initializer: &ast::Expr,
    all_functions: &BTreeMap<String, InlineFunction>,
    available_functions: &BTreeMap<String, InlineFunction>,
) -> Option<String> {
    let mut pending = BTreeSet::new();
    collect_called_names_expression(initializer, &mut pending);
    let mut visited = BTreeSet::new();
    while let Some(function_name) = pending.pop_first() {
        let Some(summary) = all_functions.get(function_name.as_str()) else {
            continue;
        };
        if !available_functions.contains_key(function_name.as_str()) {
            return Some(function_name);
        }
        if !visited.insert(function_name) {
            continue;
        }
        if let Some(expression) = &summary.expression {
            collect_called_names_expression(expression, &mut pending);
        }
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn function_definition_has_undefined_default(
    summary: &InlineFunction,
    all_functions: &BTreeMap<String, InlineFunction>,
    available_functions: &BTreeMap<String, InlineFunction>,
    globals: &BTreeMap<String, Term>,
    type_comments: &BTreeMap<u32, ScalarTypeComment>,
    exception_hierarchy: &ExceptionHierarchy,
    conformance_mode: bool,
) -> Result<bool, ContractFailure> {
    let lowerer = ExpressionLowerer {
        functions: available_functions,
        globals,
        type_comments,
        call_stack: vec!["<module-default>".to_owned()],
        exception_hierarchy,
        conformance_mode,
    };
    for parameter in summary
        .positional_parameters
        .iter()
        .chain(summary.keyword_only_parameters.iter())
    {
        let Some(default) = &parameter.default else {
            continue;
        };
        if first_unavailable_initializer_function(default, all_functions, available_functions)
            .is_some()
        {
            return Ok(true);
        }
        let value = match lowerer.lower_spec(default, globals, None, "source function default") {
            Ok(value) => value,
            Err(error) if error.code == "frontend.python.name.unresolved" => return Ok(true),
            Err(error) => return Err(error),
        };
        coerce_to_sort(value, &parameter.sort, "source function default")?;
    }
    Ok(false)
}

fn ensure_unreserved_module_binding(
    name: &str,
    reserved_bindings: &BTreeSet<String>,
) -> Result<(), ContractFailure> {
    if reserved_bindings.contains(name) {
        failure(
            "frontend.python.contracts.module-binding-reassigned",
            format!("module binding {name:?} collides with a function, import, or class"),
        )
    } else {
        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
fn insert_immutable_module_global(
    name: &str,
    initializer: &ast::Expr,
    expected_sort: Option<&Sort>,
    globals: &mut BTreeMap<String, Term>,
    available_functions: &BTreeMap<String, InlineFunction>,
    type_comments: &BTreeMap<u32, ScalarTypeComment>,
    exception_hierarchy: &ExceptionHierarchy,
    conformance_mode: bool,
    shadowed_builtin_types: &BTreeSet<String>,
) -> Result<(), ContractFailure> {
    if globals.contains_key(name) || available_functions.contains_key(name) {
        return failure(
            "frontend.python.contracts.module-binding-reassigned",
            format!("module binding {name:?} is assigned more than once or shadows a function"),
        );
    }
    let lowerer = ExpressionLowerer {
        functions: available_functions,
        globals,
        type_comments,
        call_stack: vec!["<module>".to_owned()],
        exception_hierarchy,
        conformance_mode,
    };
    let value =
        if let Some(value) = canonical_builtin_type_object(initializer, shadowed_builtin_types) {
            if expected_sort.is_some() {
                return failure(
                    "frontend.python.contracts.module-global-type-mismatch",
                    "a builtin type-object alias does not match a scalar module annotation",
                );
            }
            value
        } else if let Some(expected) = expected_sort {
            let value = lowerer.lower_spec(initializer, globals, None, "module initializer")?;
            coerce_to_sort(value, expected, "module initializer")?
        } else {
            lowerer.lower_spec(initializer, globals, None, "module initializer")?
        };
    value.sort().map_err(type_failure)?;
    globals.insert(name.to_owned(), value);
    Ok(())
}

fn canonical_builtin_type_object(
    expression: &ast::Expr,
    shadowed_builtin_types: &BTreeSet<String>,
) -> Option<Term> {
    let ast::Expr::Name(name) = expression else {
        return None;
    };
    let builtin = name.id.as_str();
    matches!(builtin, "bool" | "int" | "object")
        .then(|| {
            (!shadowed_builtin_types.contains(builtin)).then(|| Term::ClassLiteral {
                name: format!("builtins::{builtin}"),
            })
        })
        .flatten()
}

/// Parse an explicit Nagini-style `@ContractOnly` provider contract.
///
/// This accepts only scalar signatures and leading `Requires`/`Ensures` clauses followed by
/// `pass` or `...`. Executable provider code is rejected so the assumed boundary cannot be
/// confused with source that Maledictus verified.
pub fn parse_external_contract_module(
    source: &str,
    path: &str,
    module: &str,
) -> Result<ImportedContractModule, ContractFailure> {
    if module.is_empty()
        || module
            .split('.')
            .any(|part| part.is_empty() || !is_python_identifier(part))
    {
        return failure(
            "frontend.python.external.module-invalid",
            format!("external module name {module:?} is not a dotted Python identifier"),
        );
    }
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.external.parse-error",
        message: error.to_string(),
    })?;
    validate_ellipsis_singleton_bindings(&suite)?;
    let mut exception_hierarchy = ExceptionHierarchy::from_suite(&suite)?;
    let mut functions = BTreeMap::new();
    for (statement_index, statement) in suite.iter().enumerate() {
        match statement {
            statement if statement_index == 0 && is_inert_string_statement(statement) => {}
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import.module.as_ref().is_some_and(|name| {
                        matches!(name.as_str(), "nagini_contracts.contracts" | "typing")
                    }) => {}
            ast::Stmt::FunctionDef(function) => {
                if !function.decorator_list.iter().any(
                    |decorator| matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "ContractOnly"),
                ) || !function.decorator_list.iter().all(
                    |decorator| matches!(decorator, ast::Expr::Name(name) if matches!(name.id.as_str(), "ContractOnly" | "Pure")),
                ) {
                    return failure(
                        "frontend.python.external.decorator-required",
                        format!(
                            "external function {:?} must use only @ContractOnly and optional @Pure",
                            function.name
                        ),
                    );
                }
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
                        "frontend.python.external.signature-unsupported",
                        format!(
                            "external function {:?} has an unsupported signature",
                            function.name
                        ),
                    );
                }
                let mut executable_start = 0;
                let mut preconditions = Vec::new();
                let mut postconditions = Vec::new();
                let mut exceptional_postconditions = Vec::new();
                let return_sort = annotation_sort(function.returns.as_deref())?;
                for (index, body_statement) in function.body.iter().enumerate() {
                    if index == 0 && is_inert_string_statement(body_statement) {
                        executable_start = 1;
                    } else if let Some(expression) = contract_requires(body_statement) {
                        preconditions.push(expression.clone());
                        executable_start = index + 1;
                    } else if let Some(postcondition) =
                        contract_ensures(body_statement, &return_sort)?
                    {
                        postconditions.push(postcondition);
                        executable_start = index + 1;
                    } else if let Some((exception_type, expression)) =
                        contract_exsures(body_statement, &exception_hierarchy)?
                    {
                        exceptional_postconditions.push((exception_type, expression.clone()));
                        executable_start = index + 1;
                    } else {
                        break;
                    }
                }
                let executable = &function.body[executable_start..];
                let contract_only_body = matches!(executable, [ast::Stmt::Pass(_)])
                    || matches!(
                        executable,
                        [ast::Stmt::Expr(statement)]
                            if matches!(statement.value.as_ref(), ast::Expr::Constant(constant) if constant.value == ast::Constant::Ellipsis)
                    );
                if !contract_only_body {
                    return failure(
                        "frontend.python.external.body-not-contract-only",
                        format!(
                            "external function {:?} must end in exactly pass or ellipsis",
                            function.name
                        ),
                    );
                }
                let (positional_parameters, keyword_only_parameters, var_args, keyword_args) =
                    inline_signature(&function.args)?;
                let summary = InlineFunction {
                    positional_parameters,
                    keyword_only_parameters,
                    var_args,
                    keyword_args,
                    return_sort,
                    preconditions,
                    postconditions,
                    exceptional_postconditions,
                    expression: None,
                    modular_call: true,
                    pure: function.decorator_list.iter().any(
                        |decorator| matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "Pure"),
                    ),
                    ghost: false,
                    captured_environment: Some(BTreeMap::new()),
                    scalar_identity_result: None,
                };
                if functions
                    .insert(function.name.to_string(), summary)
                    .is_some()
                {
                    return failure(
                        "frontend.python.external.duplicate-function",
                        format!("duplicate external function {:?}", function.name),
                    );
                }
            }
            ast::Stmt::ClassDef(class)
                if exception_hierarchy
                    .parents
                    .contains_key(class.name.as_str()) => {}
            _ => {
                return failure(
                    "frontend.python.external.module-statement-unsupported",
                    format!("unsupported external contract statement: {statement:?}"),
                );
            }
        }
    }
    if functions.is_empty() {
        return failure(
            "frontend.python.external.empty-module",
            "external contract module contains no @ContractOnly functions",
        );
    }
    exception_hierarchy.assign_unowned_origin(module);
    let module_contract = ImportedContractModule {
        module: module.to_owned(),
        functions,
        exception_hierarchy,
    };
    validate_external_contract_module(&module_contract)?;
    Ok(module_contract)
}

/// Return the non-builtin modules imported through the supported contract-call syntax.
///
/// Source-module composition deliberately starts with absolute `from module import symbol`
/// edges. Plain imports and relative imports refuse until attribute/module initialization
/// semantics are represented rather than guessed.
pub fn source_contract_imports(source: &str, path: &str) -> Result<Vec<String>, ContractFailure> {
    let bindings = source_contract_import_bindings(source, path)?;
    Ok(bindings
        .into_iter()
        .map(|binding| binding.module)
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect())
}

pub(crate) fn source_contract_import_requests(
    source: &str,
    path: &str,
) -> Result<Vec<SourceContractImportRequest>, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    let mut requests = BTreeSet::new();
    for statement in &suite {
        match statement {
            ast::Stmt::Import(_) => {
                return failure(
                    "frontend.python.contract-import.plain-import-unsupported",
                    format!(
                        "source {path:?} uses plain import; contract composition requires explicit from-import bindings"
                    ),
                );
            }
            ast::Stmt::ImportFrom(import) => {
                let module = import.module.as_ref().ok_or_else(|| ContractFailure {
                    code: "frontend.python.contract-import.module-missing",
                    message: format!("source {path:?} has an import without a module name"),
                })?;
                let relative_level = import.level.map_or(0, |level| level.to_u32());
                if relative_level == 0
                    && matches!(
                        module.as_str(),
                        "nagini_contracts.contracts" | "typing" | "dataclasses"
                    )
                {
                    continue;
                }
                requests.insert(SourceContractImportRequest {
                    module: module.to_string(),
                    relative_level,
                    imported_names: import
                        .names
                        .iter()
                        .map(|alias| {
                            (
                                alias.name.to_string(),
                                alias.asname.as_ref().map(ToString::to_string),
                            )
                        })
                        .collect(),
                });
            }
            _ => {}
        }
    }
    Ok(requests.into_iter().collect())
}

pub fn source_contract_import_bindings(
    source: &str,
    path: &str,
) -> Result<Vec<ContractImportBinding>, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    let mut bindings = Vec::new();
    for statement in &suite {
        match statement {
            ast::Stmt::Import(_) => {
                return failure(
                    "frontend.python.contract-import.plain-import-unsupported",
                    format!(
                        "source {path:?} uses plain import; contract composition requires explicit from-import bindings"
                    ),
                );
            }
            ast::Stmt::ImportFrom(import) => {
                let module = import.module.as_ref().ok_or_else(|| ContractFailure {
                    code: "frontend.python.contract-import.module-missing",
                    message: format!("source {path:?} has an import without a module name"),
                })?;
                if import.level.is_some_and(|level| level != 0_u32)
                    || !matches!(
                        module.as_str(),
                        "nagini_contracts.contracts" | "typing" | "dataclasses"
                    )
                {
                    for alias in &import.names {
                        let imported_name = alias.name.to_string();
                        let local_name = alias
                            .asname
                            .as_ref()
                            .map_or_else(|| imported_name.clone(), ToString::to_string);
                        bindings.push(ContractImportBinding {
                            module: module.to_string(),
                            imported_name,
                            local_name,
                        });
                    }
                }
            }
            _ => {}
        }
    }
    Ok(bindings)
}

/// Verify every function body in a source-owned module and only then export opaque modular
/// summaries for its callers.
pub fn verify_and_export_source_contract_module(
    source: &str,
    path: &str,
    module: &str,
    imported_modules: &[ImportedContractModule],
) -> Result<(ContractVerification, ImportedContractModule), ContractFailure> {
    if module.is_empty()
        || module
            .split('.')
            .any(|part| part.is_empty() || !is_python_identifier(part))
    {
        return failure(
            "frontend.python.contract-import.module-invalid",
            format!("source module name {module:?} is not a dotted Python identifier"),
        );
    }
    let verification = verify_contract_module_internal(
        source,
        path,
        &[],
        imported_modules,
        None,
        false,
        ModuleIdentity::imported(module, path),
    )?;
    if !verification.passed {
        return failure(
            "frontend.python.contract-import.source-module-refuted",
            format!(
                "source module {module:?} cannot supply contracts because at least one body obligation was refuted"
            ),
        );
    }
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    let mut exception_hierarchy = resolve_exception_hierarchy(&suite, imported_modules)?;
    exception_hierarchy.assign_unowned_origin(module);
    let type_comments = collect_scalar_type_comments(source)?;
    let declarations = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => Some(function),
            _ => None,
        })
        .collect::<Vec<_>>();
    let folded_predicates = closed_module_folded_int_update(&suite)
        .map(|shape| BTreeSet::from([shape.predicate]))
        .unwrap_or_default();
    let mut module_functions = build_inline_functions(
        &declarations,
        &exception_hierarchy,
        None,
        &folded_predicates,
    )?;
    install_scalar_int_subclass_constructors(&suite, &mut module_functions)?;
    let imported_by_name = imported_modules
        .iter()
        .map(|imported| (imported.module.as_str(), imported))
        .collect::<BTreeMap<_, _>>();
    for statement in &suite {
        let ast::Stmt::ImportFrom(import) = statement else {
            continue;
        };
        let Some(imported) = import
            .module
            .as_ref()
            .and_then(|name| imported_by_name.get(name.as_str()))
        else {
            continue;
        };
        for alias in &import.names {
            let imported_name = alias.name.as_str();
            if imported_name == "*" {
                for (exported_name, summary) in &imported.functions {
                    if exported_name.starts_with('_') {
                        continue;
                    }
                    if module_functions
                        .insert(exported_name.clone(), summary.clone())
                        .is_some()
                    {
                        return failure(
                            "frontend.python.contract-import.import-collision",
                            format!("star import shadows source function {exported_name:?}"),
                        );
                    }
                }
                continue;
            }
            let local_name = alias
                .asname
                .as_ref()
                .map_or(imported_name, |name| name.as_str());
            if let Some(summary) = imported.functions.get(imported_name)
                && module_functions
                    .insert(local_name.to_owned(), summary.clone())
                    .is_some()
            {
                return failure(
                    "frontend.python.contract-import.import-collision",
                    format!("contract import shadows source function {local_name:?}"),
                );
            }
        }
    }
    let module_globals = derive_immutable_module_globals(
        &suite,
        ModuleDerivationContext {
            source,
            path,
            functions: &module_functions,
            type_comments: &type_comments,
            exception_hierarchy: &exception_hierarchy,
            conformance_mode: false,
            identity: &ModuleIdentity::imported(module, path),
        },
    )?;
    validate_module_list_mutation_records(&module_globals)?;
    if module_globals.initialization_failure.is_some() {
        return failure(
            "frontend.python.contract-import.source-module-refuted",
            format!(
                "source module {module:?} cannot supply contracts because module initialization was refuted"
            ),
        );
    }
    let global_environment = module_globals.values;
    let mut functions = BTreeMap::new();
    for statement in &suite {
        let ast::Stmt::FunctionDef(function) = statement else {
            continue;
        };
        let mut preconditions = Vec::new();
        let mut postconditions = Vec::new();
        let mut exceptional_postconditions = Vec::new();
        let return_sort = annotation_sort(function.returns.as_deref())?;
        for (index, body_statement) in function.body.iter().enumerate() {
            if index == 0 && is_inert_string_statement(body_statement) {
                continue;
            } else if let Some(expression) = contract_requires(body_statement) {
                preconditions.push(expression.clone());
            } else if let Some(postcondition) = contract_ensures(body_statement, &return_sort)? {
                postconditions.push(postcondition);
            } else if contract_decreases(body_statement)? {
            } else if let Some((exception_type, expression)) =
                contract_exsures(body_statement, &exception_hierarchy)?
            {
                exceptional_postconditions.push((exception_type, expression.clone()));
            } else {
                break;
            }
        }
        let (positional_parameters, keyword_only_parameters, var_args, keyword_args) =
            inline_signature(&function.args)?;
        let summary = InlineFunction {
            positional_parameters,
            keyword_only_parameters,
            var_args,
            keyword_args,
            return_sort,
            preconditions,
            postconditions,
            exceptional_postconditions,
            expression: None,
            modular_call: true,
            pure: function.decorator_list.iter().any(
                |decorator| matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "Pure"),
            ),
            ghost: function.decorator_list.iter().any(
                |decorator| matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "Ghost"),
            ),
            captured_environment: Some(global_environment.clone()),
            scalar_identity_result: None,
        };
        if functions
            .insert(function.name.to_string(), summary)
            .is_some()
        {
            return failure(
                "frontend.python.contract-import.duplicate-function",
                format!("duplicate source export {:?}", function.name),
            );
        }
    }
    Ok((
        verification,
        ImportedContractModule {
            module: module.to_owned(),
            functions,
            exception_hierarchy,
        },
    ))
}

fn validate_external_contract_module(
    module: &ImportedContractModule,
) -> Result<(), ContractFailure> {
    let type_comments = BTreeMap::new();
    let globals = BTreeMap::new();
    for (function_name, summary) in &module.functions {
        let environment = summary
            .positional_parameters
            .iter()
            .chain(summary.keyword_only_parameters.iter())
            .map(|parameter| {
                (
                    parameter.name.clone(),
                    Term::Variable {
                        name: format!(
                            "external::{}::{function_name}::{}",
                            module.module, parameter.name
                        ),
                        sort: parameter.sort.clone(),
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let lowerer = ExpressionLowerer {
            functions: &module.functions,
            globals: &globals,
            type_comments: &type_comments,
            call_stack: vec![function_name.clone()],
            exception_hierarchy: &module.exception_hierarchy,
            conformance_mode: false,
        };
        for precondition in &summary.preconditions {
            for clause in lowerer.lower_specification_clauses(
                precondition,
                &environment,
                None,
                "external precondition",
            )? {
                ensure_boolean(&clause, "external precondition")?;
            }
        }
        let result = match &summary.return_sort {
            Sort::Unit => Term::Unit,
            sort => Term::Variable {
                name: format!("external::{}::{function_name}::Result", module.module),
                sort: sort.clone(),
            },
        };
        for postcondition in &summary.postconditions {
            for clause in lowerer.lower_postcondition_clauses(
                postcondition,
                &environment,
                &result,
                "external postcondition",
            )? {
                ensure_boolean(&clause, "external postcondition")?;
            }
        }
        for (_, postcondition) in &summary.exceptional_postconditions {
            for clause in lowerer.lower_specification_clauses(
                postcondition,
                &environment,
                None,
                "external exceptional postcondition",
            )? {
                ensure_boolean(&clause, "external exceptional postcondition")?;
            }
        }
    }
    Ok(())
}

fn is_python_identifier(value: &str) -> bool {
    let mut characters = value.chars();
    characters
        .next()
        .is_some_and(|character| character == '_' || character.is_alphabetic())
        && characters.all(|character| character == '_' || character.is_alphanumeric())
}

fn collect_scalar_type_comments(
    source: &str,
) -> Result<BTreeMap<u32, ScalarTypeComment>, ContractFailure> {
    let mut comments = BTreeMap::new();
    for token in lex(source, Mode::Module) {
        let Ok((Tok::Comment(comment), range)) = token else {
            continue;
        };
        let comment = comment.trim_start_matches('#').trim_start();
        let Some(annotation) = comment.strip_prefix("type:") else {
            continue;
        };
        let annotation = annotation.trim();
        if annotation.starts_with("ignore") {
            continue;
        }
        let sort = scalar_type_comment_sort(annotation)?;
        let byte_offset = u32::from(range.start());
        let line = source_location(source, byte_offset).0;
        if comments.insert(line, sort).is_some() {
            return failure(
                "frontend.python.contracts.type-comment-duplicate",
                format!("multiple scalar type comments occur on line {line}"),
            );
        }
    }
    Ok(comments)
}

fn collect_assignment_lines(
    statements: &[ast::Stmt],
    source: &str,
    lines: &mut std::collections::BTreeSet<u32>,
) {
    for statement in statements {
        match statement {
            ast::Stmt::Assign(assignment) => {
                lines.insert(source_location(source, assignment.range.start().into()).0);
            }
            ast::Stmt::FunctionDef(function) => {
                collect_assignment_lines(&function.body, source, lines);
            }
            ast::Stmt::AsyncFunctionDef(function) => {
                collect_assignment_lines(&function.body, source, lines);
            }
            ast::Stmt::ClassDef(class) => {
                collect_assignment_lines(&class.body, source, lines);
            }
            ast::Stmt::If(branch) => {
                collect_assignment_lines(&branch.body, source, lines);
                collect_assignment_lines(&branch.orelse, source, lines);
            }
            ast::Stmt::While(loop_statement) => {
                collect_assignment_lines(&loop_statement.body, source, lines);
                collect_assignment_lines(&loop_statement.orelse, source, lines);
            }
            ast::Stmt::For(loop_statement) => {
                if loop_statement.type_comment.is_some() {
                    lines.insert(source_location(source, loop_statement.range.start().into()).0);
                }
                collect_assignment_lines(&loop_statement.body, source, lines);
                collect_assignment_lines(&loop_statement.orelse, source, lines);
            }
            ast::Stmt::Try(try_statement) => {
                collect_assignment_lines(&try_statement.body, source, lines);
                collect_assignment_lines(&try_statement.orelse, source, lines);
                collect_assignment_lines(&try_statement.finalbody, source, lines);
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    collect_assignment_lines(&handler.body, source, lines);
                }
            }
            _ => {}
        }
    }
}

fn build_inline_functions(
    declarations: &[&ast::StmtFunctionDef],
    exception_hierarchy: &ExceptionHierarchy,
    selected_symbols: Option<&BTreeSet<String>>,
    folded_predicates: &BTreeSet<String>,
) -> Result<BTreeMap<String, InlineFunction>, ContractFailure> {
    let mut functions = BTreeMap::new();
    for function in declarations {
        let pure = function.decorator_list.iter().any(
            |decorator| matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "Pure"),
        );
        let opaque = function.decorator_list.iter().any(
            |decorator| matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "Opaque"),
        );
        if !function.decorator_list.iter().all(|decorator| {
            matches!(decorator, ast::Expr::Name(name)
                if matches!(name.id.as_str(), "Pure" | "Ghost" | "Opaque")
                    || (name.id.as_str() == "Predicate"
                        && folded_predicates.contains(function.name.as_str())))
        }) {
            return failure(
                "frontend.python.contracts.decorator-unsupported",
                format!("function {:?} uses an unsupported decorator", function.name),
            );
        }
        if opaque && !pure {
            return failure(
                "frontend.python.contracts.opaque-requires-pure",
                format!("opaque function {:?} must also be pure", function.name),
            );
        }
        let mut executable_start = 0;
        let mut preconditions = Vec::new();
        let mut postconditions = Vec::new();
        let mut exceptional_postconditions = Vec::new();
        let return_sort = annotation_sort(function.returns.as_deref())?;
        for (index, statement) in function.body.iter().enumerate() {
            if index == 0 && is_inert_string_statement(statement) {
                executable_start = 1;
            } else if let Some(expression) = contract_requires(statement) {
                preconditions.push(expression.clone());
                executable_start = index + 1;
            } else if let Some(postcondition) = contract_ensures(statement, &return_sort)? {
                postconditions.push(postcondition);
                executable_start = index + 1;
            } else if contract_decreases(statement)? {
                executable_start = index + 1;
            } else if let Some((exception_type, expression)) =
                contract_exsures(statement, exception_hierarchy)?
            {
                exceptional_postconditions.push((exception_type, expression.clone()));
                executable_start = index + 1;
            } else {
                break;
            }
        }
        let executable = &function.body[executable_start..];
        let (expression, mut modular_call) = match executable {
            [ast::Stmt::Return(return_statement)] => {
                (return_statement.value.as_deref().cloned(), false)
            }
            [] if return_sort == Sort::Unit => (None, false),
            [ast::Stmt::Pass(_)] if return_sort == Sort::Unit => (None, false),
            _ => (None, true),
        };
        if selected_symbols.is_some_and(|selected| !selected.contains(function.name.as_str())) {
            modular_call = true;
        }
        if opaque {
            modular_call = true;
        }
        let (positional_parameters, keyword_only_parameters, var_args, keyword_args) =
            inline_signature(&function.args)?;
        let summary = InlineFunction {
            positional_parameters,
            keyword_only_parameters,
            var_args,
            keyword_args,
            return_sort,
            preconditions,
            postconditions,
            exceptional_postconditions,
            expression,
            modular_call,
            pure,
            ghost: function.decorator_list.iter().any(
                |decorator| matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "Ghost"),
            ),
            captured_environment: None,
            scalar_identity_result: None,
        };
        if functions
            .insert(function.name.to_string(), summary)
            .is_some()
        {
            return failure(
                "frontend.python.contracts.duplicate-function",
                format!("duplicate source function {:?}", function.name),
            );
        }
    }
    Ok(functions)
}

#[allow(clippy::too_many_arguments)]
fn lower_function(
    function: &ast::StmtFunctionDef,
    path: &str,
    source: &str,
    inline_functions: &BTreeMap<String, InlineFunction>,
    type_comments: &BTreeMap<u32, ScalarTypeComment>,
    global_environment: &BTreeMap<String, Term>,
    exception_hierarchy: &ExceptionHierarchy,
    conformance_mode: bool,
) -> Result<LoweredFunction, ContractFailure> {
    if !function
        .decorator_list
        .iter()
        .all(|decorator| matches!(decorator, ast::Expr::Name(name) if matches!(name.id.as_str(), "Pure" | "Ghost" | "Opaque")))
        || !function.type_params.is_empty()
    {
        return failure(
            "frontend.python.contracts.signature-unsupported",
            format!("function {:?} has an unsupported signature", function.name),
        );
    }
    if let Some(var_args) = function.args.vararg.as_deref() {
        validate_variadic_positional_uses(&function.body, var_args.arg.as_str())?;
    }
    let parameter_names = function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .chain(function.args.kwonlyargs.iter())
        .map(|argument| argument.def.arg.as_str())
        .chain(
            function
                .args
                .vararg
                .iter()
                .map(|argument| argument.arg.as_str()),
        )
        .chain(
            function
                .args
                .kwarg
                .iter()
                .map(|argument| argument.arg.as_str()),
        )
        .collect::<std::collections::BTreeSet<_>>();
    let mut modified_names = std::collections::BTreeSet::new();
    collect_modified_names(&function.body, &mut modified_names);
    let global_names = function_global_binding_names(&function.body);
    for global_name in &global_names {
        modified_names.remove(global_name);
    }
    let mut called_names = std::collections::BTreeSet::new();
    collect_called_names(&function.body, &mut called_names);
    if let Some(shadowed) = inline_functions.keys().find(|name| {
        called_names.contains(name.as_str())
            && (parameter_names.contains(name.as_str()) || modified_names.contains(name.as_str()))
    }) {
        return failure(
            "frontend.python.contracts.callable-shadowed",
            format!(
                "function {:?} shadows callable {shadowed:?}; static call resolution would be ambiguous",
                function.name
            ),
        );
    }
    const CANONICAL_HELPERS: [&str; 11] = [
        "Acc",
        "Forall",
        "Implies",
        "Result",
        "ResultT",
        "len",
        "list_pred",
        "range",
        "sorted",
        "str",
        "sum",
    ];
    if let Some(shadowed) = CANONICAL_HELPERS.iter().find(|name| {
        called_names.contains(**name)
            && (parameter_names.contains(**name)
                || modified_names.contains(**name)
                || (!matches!(**name, "sorted" | "sum") && inline_functions.contains_key(**name))
                || global_environment.contains_key(**name))
    }) {
        return failure(
            "frontend.python.contracts.canonical-helper-shadowed",
            format!(
                "function {:?} shadows canonical contract helper {shadowed:?}",
                function.name
            ),
        );
    }
    if called_names.contains("sorted")
        && !inline_functions.contains_key("sorted")
        && !global_environment.contains_key("sorted")
    {
        reject_sorted_calls_in_repeated_regions(&function.body, function)?;
    }
    let mut environment = global_environment.clone();
    let mut identities = BTreeMap::new();
    for local_name in &modified_names {
        environment.remove(local_name);
    }
    for argument in function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .chain(function.args.kwonlyargs.iter())
    {
        let sort = annotation_sort(argument.def.annotation.as_deref())?;
        let argument_name = argument.def.arg.to_string();
        let ellipsis_typed = matches!(argument.def.annotation.as_deref(),
            Some(ast::Expr::Name(name)) if name.id.as_str() == "EllipsisType");
        if matches!(sort, Sort::List(_)) {
            identities.insert(
                argument_name.clone(),
                PythonObjectIdentity::FunctionInput(argument_name.clone()),
            );
        } else if ellipsis_typed {
            identities.insert(
                argument_name.clone(),
                PythonObjectIdentity::EllipsisSingleton,
            );
        }
        environment.insert(
            argument_name,
            if ellipsis_typed {
                ellipsis_singleton()
            } else {
                Term::Variable {
                    name: format!("{}::{}", function.name, argument.def.arg),
                    sort,
                }
            },
        );
    }
    if let Some(argument) = function.args.vararg.as_deref() {
        let element_sort = annotation_sort(argument.annotation.as_deref())?;
        environment.insert(
            argument.arg.to_string(),
            Term::Variable {
                name: format!("{}::{}", function.name, argument.arg),
                sort: Sort::List(Box::new(element_sort)),
            },
        );
    }
    if let Some(argument) = function.args.kwarg.as_deref() {
        let value_sort = annotation_sort(argument.annotation.as_deref())?;
        environment.insert(
            argument.arg.to_string(),
            Term::Variable {
                name: format!("{}::{}", function.name, argument.arg),
                sort: Sort::Dict(Box::new(Sort::String), Box::new(value_sort)),
            },
        );
    }
    let return_sort = annotation_sort(function.returns.as_deref())?;
    let lowerer = ExpressionLowerer {
        functions: inline_functions,
        globals: global_environment,
        type_comments,
        call_stack: vec![function.name.to_string()],
        exception_hierarchy,
        conformance_mode,
    };
    let summary = inline_functions
        .get(function.name.as_str())
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.function-summary-missing",
            message: format!(
                "function {:?} has no source-bound call signature",
                function.name
            ),
        })?;
    lowerer.lower_call_signature(summary)?;
    let mut assumptions = Vec::new();
    let mut postconditions = Vec::new();
    let mut exceptional_postconditions = Vec::new();
    let mut specification_safety = Vec::new();
    let mut obligations = Vec::new();
    let mut executable_started = false;
    let mut executable_index = function.body.len();

    for (index, statement) in function.body.iter().enumerate() {
        if index == 0 && is_inert_string_statement(statement) {
            continue;
        }
        if matches!(statement, ast::Stmt::Global(_)) {
            // `global` is a compile-time scope declaration, not an executable action. It may
            // precede contracts without making those contracts late.
            continue;
        }
        if let Some(expression) = contract_requires(statement) {
            if executable_started {
                return failure(
                    "frontend.python.contracts.late-contract",
                    format!(
                        "function {:?} declares Requires after executable code",
                        function.name
                    ),
                );
            }
            let mut guards = Vec::new();
            collect_runtime_exception_guards(
                expression,
                &lowerer,
                &environment,
                None,
                Term::Bool { value: true },
                &mut guards,
            )?;
            for (guard_index, guard) in guards.into_iter().enumerate() {
                let offset = statement_offset(statement);
                specification_safety.push(Obligation {
                    id: format!(
                        "{}:precondition-safety:{index}:{guard_index}",
                        function.name
                    ),
                    expectation: ObligationExpectation::Prove,
                    assumptions: assumptions.clone(),
                    conclusion: Term::Implies {
                        left: Box::new(guard.evaluation_condition),
                        right: Box::new(guard.condition),
                    },
                    path: path.to_owned(),
                    byte_offset: offset,
                    line: source_location(source, offset).0,
                    column: source_location(source, offset).1,
                });
            }
            let precondition = lowerer.lower(expression, &environment, None)?;
            ensure_boolean(&precondition, "function precondition")?;
            assumptions.push(precondition);
            continue;
        }
        if let Some(postcondition) = contract_ensures(statement, &return_sort)? {
            if executable_started {
                return failure(
                    "frontend.python.contracts.late-contract",
                    format!(
                        "function {:?} declares Ensures after executable code",
                        function.name
                    ),
                );
            }
            postconditions.push((postcondition, statement_offset(statement)));
            continue;
        }
        if contract_decreases(statement)? {
            if executable_started {
                return failure(
                    "frontend.python.contracts.late-contract",
                    format!(
                        "function {:?} declares Decreases after executable code",
                        function.name
                    ),
                );
            }
            continue;
        }
        if let Some((exception_type, expression)) =
            contract_exsures(statement, exception_hierarchy)?
        {
            if executable_started {
                return failure(
                    "frontend.python.contracts.late-contract",
                    format!(
                        "function {:?} declares Exsures after executable code",
                        function.name
                    ),
                );
            }
            exceptional_postconditions.push((
                exception_type,
                expression.clone(),
                statement_offset(statement),
            ));
            continue;
        }
        if !executable_started {
            executable_started = true;
            executable_index = index;
        }
    }

    validate_statement_shapes(&function.body[executable_index..], function, &lowerer)?;

    let initial_state = SymbolicState {
        environment,
        identities,
        assumptions,
    };
    let mut return_paths = Vec::new();
    let mut exceptional_paths = Vec::new();
    let active = execute_statements(
        &function.body[executable_index..],
        vec![initial_state],
        function,
        &lowerer,
        &return_sort,
        path,
        source,
        &mut obligations,
        &mut return_paths,
        &mut exceptional_paths,
    )?;
    if return_sort == Sort::Unit {
        for state in active {
            return_paths.push(ReturnPath {
                state,
                value: Term::Unit,
                byte_offset: function.range.end().into(),
            });
        }
    } else {
        let totality_kind = if function.decorator_list.iter().any(
            |decorator| matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "Pure"),
        ) {
            "pure-path"
        } else {
            "runtime-path"
        };
        for (path_index, state) in active.into_iter().enumerate() {
            let byte_offset = function.range.start().into();
            obligations.push(Obligation {
                id: format!(
                    "{}:function-totality:{totality_kind}:{path_index}",
                    function.name
                ),
                expectation: ObligationExpectation::Prove,
                assumptions: state.assumptions,
                conclusion: Term::Bool { value: false },
                path: path.to_owned(),
                byte_offset,
                line: source_location(source, byte_offset).0,
                column: source_location(source, byte_offset).1,
            });
        }
    }
    for (condition_index, (postcondition, offset)) in postconditions.into_iter().enumerate() {
        for (path_index, returned) in return_paths.iter().enumerate() {
            let mut clauses = lowerer.lower_postcondition_clauses(
                &postcondition,
                &returned.state.environment,
                &returned.value,
                "function postcondition",
            )?;
            let conclusion = clauses
                .pop()
                .expect("specification clauses always end with the original predicate");
            for (guard_index, safety) in clauses.into_iter().enumerate() {
                specification_safety.push(Obligation {
                    id: format!(
                        "{}:postcondition-safety:{condition_index}:path:{path_index}:{guard_index}",
                        function.name
                    ),
                    expectation: ObligationExpectation::Prove,
                    assumptions: returned.state.assumptions.clone(),
                    conclusion: safety,
                    path: path.to_owned(),
                    byte_offset: offset,
                    line: source_location(source, offset).0,
                    column: source_location(source, offset).1,
                });
            }
            ensure_boolean(&conclusion, "postcondition")?;
            let location = if offset == 0 {
                returned.byte_offset
            } else {
                offset
            };
            obligations.push(Obligation {
                id: format!(
                    "{}:postcondition:{condition_index}:path:{path_index}",
                    function.name
                ),
                expectation: ObligationExpectation::Prove,
                assumptions: returned.state.assumptions.clone(),
                conclusion,
                path: path.to_owned(),
                byte_offset: location,
                line: source_location(source, location).0,
                column: source_location(source, location).1,
            });
        }
    }
    for (path_index, raised) in exceptional_paths.iter().enumerate() {
        let matching = exceptional_postconditions
            .iter()
            .enumerate()
            .filter(|(_, (declared, _, _))| {
                lowerer
                    .exception_hierarchy
                    .matches(declared, &raised.exception_type)
            })
            .collect::<Vec<_>>();
        if matching.is_empty() {
            let location = if raised.application_precondition {
                raised.byte_offset
            } else {
                function.range.start().into()
            };
            obligations.push(Obligation {
                id: format!(
                    "{}:exception-undeclared:{}:{}path:{path_index}",
                    function.name,
                    raised.exception_type,
                    if raised.application_precondition {
                        "application-precondition:"
                    } else {
                        ""
                    }
                ),
                expectation: ObligationExpectation::Prove,
                assumptions: raised.state.assumptions.clone(),
                conclusion: Term::Bool { value: false },
                path: path.to_owned(),
                byte_offset: location,
                line: source_location(source, location).0,
                column: source_location(source, location).1,
            });
            continue;
        }
        for (condition_index, (_, postcondition, offset)) in matching {
            let mut clauses = lowerer.lower_specification_clauses(
                postcondition,
                &raised.state.environment,
                None,
                "function exceptional postcondition",
            )?;
            let conclusion = clauses
                .pop()
                .expect("specification clauses always end with the original predicate");
            for (guard_index, safety) in clauses.into_iter().enumerate() {
                specification_safety.push(Obligation {
                    id: format!(
                        "{}:exception-postcondition-safety:{condition_index}:path:{path_index}:{guard_index}",
                        function.name
                    ),
                    expectation: ObligationExpectation::Prove,
                    assumptions: raised.state.assumptions.clone(),
                    conclusion: safety,
                    path: path.to_owned(),
                    byte_offset: *offset,
                    line: source_location(source, *offset).0,
                    column: source_location(source, *offset).1,
                });
            }
            ensure_boolean(&conclusion, "exceptional postcondition")?;
            obligations.push(Obligation {
                id: format!(
                    "{}:exception-postcondition:{condition_index}:path:{path_index}",
                    function.name
                ),
                expectation: ObligationExpectation::Prove,
                assumptions: raised.state.assumptions.clone(),
                conclusion,
                path: path.to_owned(),
                byte_offset: *offset,
                line: source_location(source, *offset).0,
                column: source_location(source, *offset).1,
            });
        }
    }
    if obligations.is_empty() && specification_safety.is_empty() {
        let byte_offset = function.range.start().into();
        obligations.push(Obligation {
            id: format!("{}:function-totality:complete", function.name),
            expectation: ObligationExpectation::Prove,
            assumptions: Vec::new(),
            conclusion: Term::Bool { value: true },
            path: path.to_owned(),
            byte_offset,
            line: source_location(source, byte_offset).0,
            column: source_location(source, byte_offset).1,
        });
    }
    Ok(LoweredFunction {
        specification_safety,
        obligations,
    })
}

fn validate_statement_shapes(
    statements: &[ast::Stmt],
    function: &ast::StmtFunctionDef,
    lowerer: &ExpressionLowerer<'_>,
) -> Result<(), ContractFailure> {
    for statement in statements {
        match statement {
            ast::Stmt::Global(_) => {}
            ast::Stmt::Assign(assignment) if assignment.targets.len() == 1 => {
                if !matches!(&assignment.targets[0], ast::Expr::Name(_)) {
                    return unsupported_statement(function, statement);
                }
                if matches!(&assignment.targets[0], ast::Expr::Name(name)
                    if function_global_binding_names(&function.body).contains(name.id.as_str()))
                    && !is_static_module_global_write_value(&assignment.value)
                {
                    return failure(
                        "frontend.python.contracts.global-write-value-unsupported",
                        format!(
                            "function {:?} writes a module global from an expression that may have effects or exceptional exits",
                            function.name
                        ),
                    );
                }
                validate_expression_shape(&assignment.value, lowerer)?;
            }
            ast::Stmt::AnnAssign(assignment) => {
                if !matches!(assignment.target.as_ref(), ast::Expr::Name(_))
                    || assignment.value.is_none()
                {
                    return unsupported_statement(function, statement);
                }
                annotation_sort(Some(&assignment.annotation))?;
                validate_expression_shape(
                    assignment
                        .value
                        .as_deref()
                        .expect("initialized annotation checked"),
                    lowerer,
                )?;
            }
            ast::Stmt::AugAssign(assignment) => {
                if !matches!(assignment.target.as_ref(), ast::Expr::Name(_))
                    || !matches!(
                        assignment.op,
                        ast::Operator::Add | ast::Operator::Sub | ast::Operator::Mult
                    )
                {
                    return unsupported_statement(function, statement);
                }
                validate_expression_shape(&assignment.value, lowerer)?;
            }
            ast::Stmt::Assert(assertion) => {
                validate_expression_shape(&assertion.test, lowerer)?;
                if assertion.msg.is_some() {
                    return unsupported_statement(function, statement);
                }
            }
            ast::Stmt::Expr(expression_statement)
                if contract_assertion(expression_statement.value.as_ref()).is_some() =>
            {
                validate_expression_shape(
                    contract_assertion(expression_statement.value.as_ref())
                        .expect("contract assertion recognized"),
                    lowerer,
                )?;
            }
            ast::Stmt::Expr(expression_statement)
                if contract_refutation(expression_statement.value.as_ref()).is_some() =>
            {
                validate_expression_shape(
                    contract_refutation(expression_statement.value.as_ref())
                        .expect("contract refutation recognized"),
                    lowerer,
                )?;
            }
            ast::Stmt::Expr(expression_statement)
                if lowerer
                    .source_call(expression_statement.value.as_ref())
                    .is_some() =>
            {
                validate_expression_shape(expression_statement.value.as_ref(), lowerer)?;
            }
            statement if is_inert_string_statement(statement) => {}
            ast::Stmt::Pass(_) => {}
            ast::Stmt::Raise(raise_statement) => {
                raised_exception_type(raise_statement, lowerer.exception_hierarchy)?;
            }
            ast::Stmt::If(branch) => {
                validate_expression_shape(&branch.test, lowerer)?;
                validate_statement_shapes(&branch.body, function, lowerer)?;
                validate_statement_shapes(&branch.orelse, function, lowerer)?;
            }
            ast::Stmt::While(loop_statement) => {
                validate_expression_shape(&loop_statement.test, lowerer)?;
                let invariant_count = loop_statement
                    .body
                    .iter()
                    .take_while(|nested| contract_invariant(nested).is_some())
                    .count();
                if invariant_count == 0 {
                    return failure(
                        "frontend.python.contracts.loop-invariant-missing",
                        format!(
                            "while loop in {:?} requires at least one leading Invariant(...) contract",
                            function.name
                        ),
                    );
                }
                for invariant in &loop_statement.body[..invariant_count] {
                    validate_expression_shape(
                        contract_invariant(invariant).expect("invariant prefix checked"),
                        lowerer,
                    )?;
                }
                validate_statement_shapes(
                    &loop_statement.body[invariant_count..],
                    function,
                    lowerer,
                )?;
                validate_statement_shapes(&loop_statement.orelse, function, lowerer)?;
            }
            ast::Stmt::For(loop_statement) => {
                if !finite_for_target_is_supported(&loop_statement.target) {
                    return failure(
                        "frontend.python.contracts.for-target-unsupported",
                        "finite for-loop targets require names or exact tuple/list unpacking",
                    );
                }
                if let Some(annotation) = loop_statement.type_comment.as_deref() {
                    scalar_type_comment_sort(annotation)?;
                }
                validate_expression_shape(&loop_statement.iter, lowerer)?;
                let invariant_count = loop_statement
                    .body
                    .iter()
                    .take_while(|nested| contract_invariant(nested).is_some())
                    .count();
                for invariant in &loop_statement.body[..invariant_count] {
                    validate_expression_shape(
                        contract_invariant(invariant).expect("invariant prefix checked"),
                        lowerer,
                    )?;
                }
                validate_statement_shapes(
                    &loop_statement.body[invariant_count..],
                    function,
                    lowerer,
                )?;
                validate_statement_shapes(&loop_statement.orelse, function, lowerer)?;
            }
            ast::Stmt::Try(try_statement) => {
                if !try_statement.finalbody.is_empty() {
                    return failure(
                        "frontend.python.contracts.try-finally-unsupported",
                        "finally requires abrupt-completion precedence rules that are not yet in the scalar fragment",
                    );
                }
                validate_statement_shapes(&try_statement.body, function, lowerer)?;
                validate_statement_shapes(&try_statement.orelse, function, lowerer)?;
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    match handler.type_.as_deref() {
                        None => {}
                        Some(ast::Expr::Name(name)) => ensure_supported_exception_type(
                            lowerer.exception_hierarchy,
                            name.id.as_str(),
                        )?,
                        Some(_) => {
                            return failure(
                                "frontend.python.contracts.exception-handler-type-unsupported",
                                "exception handlers require one direct exception class",
                            );
                        }
                    }
                    validate_statement_shapes(&handler.body, function, lowerer)?;
                }
            }
            ast::Stmt::Return(return_statement) => {
                if let Some(expression) = return_statement.value.as_deref() {
                    validate_expression_shape(expression, lowerer)?;
                }
            }
            _ => return unsupported_statement(function, statement),
        }
    }
    Ok(())
}

fn validate_expression_shape(
    expression: &ast::Expr,
    lowerer: &ExpressionLowerer<'_>,
) -> Result<(), ContractFailure> {
    match expression {
        ast::Expr::Name(_) => Ok(()),
        ast::Expr::Constant(constant)
            if matches!(
                constant.value,
                ast::Constant::Bool(_)
                    | ast::Constant::Int(_)
                    | ast::Constant::Str(_)
                    | ast::Constant::Bytes(_)
                    | ast::Constant::None
                    | ast::Constant::Ellipsis
            ) =>
        {
            Ok(())
        }
        ast::Expr::BoolOp(operation) => {
            for value in &operation.values {
                validate_expression_shape(value, lowerer)?;
            }
            Ok(())
        }
        ast::Expr::IfExp(conditional) => {
            validate_expression_shape(&conditional.test, lowerer)?;
            validate_expression_shape(&conditional.body, lowerer)?;
            validate_expression_shape(&conditional.orelse, lowerer)
        }
        ast::Expr::BinOp(operation)
            if matches!(
                operation.op,
                ast::Operator::Add
                    | ast::Operator::Sub
                    | ast::Operator::Mult
                    | ast::Operator::Pow
                    | ast::Operator::Mod
            ) =>
        {
            validate_expression_shape(&operation.left, lowerer)?;
            validate_expression_shape(&operation.right, lowerer)
        }
        ast::Expr::UnaryOp(operation)
            if matches!(
                operation.op,
                ast::UnaryOp::Not | ast::UnaryOp::USub | ast::UnaryOp::UAdd
            ) =>
        {
            validate_expression_shape(&operation.operand, lowerer)
        }
        ast::Expr::Compare(comparison)
            if !comparison.ops.is_empty()
                && comparison.ops.len() == comparison.comparators.len()
                && comparison.ops.iter().all(|operator| {
                    matches!(
                        operator,
                        ast::CmpOp::Eq
                            | ast::CmpOp::NotEq
                            | ast::CmpOp::Lt
                            | ast::CmpOp::LtE
                            | ast::CmpOp::Gt
                            | ast::CmpOp::GtE
                            | ast::CmpOp::In
                            | ast::CmpOp::NotIn
                            | ast::CmpOp::Is
                            | ast::CmpOp::IsNot
                    )
                }) =>
        {
            validate_expression_shape(&comparison.left, lowerer)?;
            for comparator in &comparison.comparators {
                validate_expression_shape(comparator, lowerer)?;
            }
            Ok(())
        }
        ast::Expr::Call(call) => {
            if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Forall") {
                if let Some((_, predicate, _)) = typed_integer_forall(call) {
                    return validate_expression_shape(predicate, lowerer);
                }
                if looks_like_typed_integer_forall(call) {
                    return failure(
                        "frontend.python.contracts.quantifier-trigger-unsupported",
                        "typed Forall requires nonempty lists of read-only trigger expressions and one unannotated integer binder",
                    );
                }
                let Some((collection, _, predicate)) = finite_literal_forall(call) else {
                    return unsupported_expression(expression);
                };
                validate_expression_shape(collection, lowerer)?;
                return validate_expression_shape(predicate, lowerer);
            }
            let supported = match call.func.as_ref() {
                ast::Expr::Name(name) => match name.id.as_str() {
                    "Result" => call.args.is_empty() && call.keywords.is_empty(),
                    "ResultT" => {
                        call.args.len() == 1
                            && call.keywords.is_empty()
                            && annotation_sort(call.args.first()).is_ok()
                    }
                    "Acc" => call.args.len() == 1 && call.keywords.is_empty(),
                    "Implies" => call.args.len() == 2 && call.keywords.is_empty(),
                    "len" | "list_pred" | "ToSeq" => {
                        call.args.len() == 1 && call.keywords.is_empty()
                    }
                    "sorted" => {
                        lowerer.sorted_builtin_call(expression).is_some()
                            || lowerer.functions.contains_key("sorted")
                    }
                    "sum" => {
                        lowerer.sum_builtin_call(expression).is_some()
                            || lowerer.functions.contains_key("sum")
                    }
                    "enumerate" => {
                        lowerer.enumerate_builtin_call(expression).is_some()
                            || lowerer.functions.contains_key("enumerate")
                    }
                    "abs" => call.args.len() == 1 && call.keywords.is_empty(),
                    "min" | "max" => !call.args.is_empty() && call.keywords.is_empty(),
                    "range" => {
                        (1..=3).contains(&call.args.len())
                            && call.keywords.is_empty()
                            && call
                                .args
                                .iter()
                                .all(|argument| constant_tuple_index(argument).is_some())
                    }
                    "str" => call.args.len() == 1 && call.keywords.is_empty(),
                    "type" => call.args.len() == 1 && call.keywords.is_empty(),
                    "isinstance" => {
                        call.args.len() == 2
                            && call.keywords.is_empty()
                            && matches!(
                                &call.args[1],
                                ast::Expr::Name(expected)
                                    if expected.id.as_str() == "str"
                                        || expected.id.as_str() == "EllipsisType"
                                        || lowerer
                                            .exception_hierarchy
                                            .supports(expected.id.as_str())
                            )
                    }
                    "Reveal" => {
                        call.args.len() == 1
                            && call.keywords.is_empty()
                            && revealed_source_call(expression).is_some()
                    }
                    function_name => lowerer.functions.contains_key(function_name),
                },
                ast::Expr::Attribute(attribute) => {
                    (attribute.attr.as_str() == "format" && call.keywords.is_empty())
                        || (attribute.attr.as_str() == "join"
                            && call.args.len() == 1
                            && call.keywords.is_empty())
                        || (attribute.attr.as_str() == "keys"
                            && call.args.is_empty()
                            && call.keywords.is_empty())
                }
                _ => false,
            };
            if !supported {
                return unsupported_expression(expression);
            }
            if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "ResultT")
            {
                return Ok(());
            }
            for argument in &call.args {
                if let ast::Expr::Starred(starred) = argument {
                    validate_expression_shape(&starred.value, lowerer)?;
                } else {
                    validate_expression_shape(argument, lowerer)?;
                }
            }
            for keyword in &call.keywords {
                validate_expression_shape(&keyword.value, lowerer)?;
            }
            Ok(())
        }
        ast::Expr::JoinedStr(joined) => {
            for value in &joined.values {
                match value {
                    ast::Expr::Constant(constant)
                        if matches!(constant.value, ast::Constant::Str(_)) => {}
                    ast::Expr::FormattedValue(formatted)
                        if formatted.format_spec.is_none()
                            && formatted.conversion == ast::ConversionFlag::None =>
                    {
                        validate_expression_shape(&formatted.value, lowerer)?;
                    }
                    _ => return unsupported_expression(value),
                }
            }
            Ok(())
        }
        ast::Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                validate_expression_shape(element, lowerer)?;
            }
            Ok(())
        }
        ast::Expr::List(list) => {
            for element in &list.elts {
                validate_expression_shape(element, lowerer)?;
            }
            Ok(())
        }
        ast::Expr::Set(set) => {
            for element in &set.elts {
                validate_expression_shape(element, lowerer)?;
            }
            Ok(())
        }
        ast::Expr::ListComp(comprehension) => validate_comprehension_shape(
            &comprehension.generators,
            &comprehension.elt,
            None,
            lowerer,
        ),
        ast::Expr::SetComp(comprehension) => validate_comprehension_shape(
            &comprehension.generators,
            &comprehension.elt,
            None,
            lowerer,
        ),
        ast::Expr::DictComp(comprehension) => validate_comprehension_shape(
            &comprehension.generators,
            &comprehension.key,
            Some(&comprehension.value),
            lowerer,
        ),
        ast::Expr::Dict(dictionary) => {
            for key in &dictionary.keys {
                let Some(key) = key.as_ref() else {
                    return failure(
                        "frontend.python.contracts.dict-unpack-unsupported",
                        "finite dictionary literals do not support ** unpacking",
                    );
                };
                validate_expression_shape(key, lowerer)?;
            }
            for value in &dictionary.values {
                validate_expression_shape(value, lowerer)?;
            }
            Ok(())
        }
        ast::Expr::Subscript(subscript) => {
            validate_expression_shape(&subscript.value, lowerer)?;
            validate_expression_shape(&subscript.slice, lowerer)
        }
        ast::Expr::Slice(slice) => {
            for bound in [&slice.lower, &slice.upper, &slice.step]
                .into_iter()
                .filter_map(|bound| bound.as_deref())
            {
                validate_expression_shape(bound, lowerer)?;
            }
            Ok(())
        }
        _ => unsupported_expression(expression),
    }
}

fn validate_comprehension_shape(
    generators: &[ast::Comprehension],
    mapped: &ast::Expr,
    second_mapped: Option<&ast::Expr>,
    lowerer: &ExpressionLowerer<'_>,
) -> Result<(), ContractFailure> {
    let [generator] = generators else {
        return failure(
            "frontend.python.contracts.comprehension-generator-count",
            "comprehensions require exactly one generator",
        );
    };
    if generator.is_async {
        return failure(
            "frontend.python.contracts.comprehension-async-unsupported",
            "async comprehensions are outside the scalar proof fragment",
        );
    }
    if !matches!(&generator.target, ast::Expr::Name(_)) {
        return failure(
            "frontend.python.contracts.comprehension-target-unsupported",
            "comprehensions require one direct local-name target",
        );
    }
    if !matches!(&generator.iter, ast::Expr::Name(_)) {
        return failure(
            "frontend.python.contracts.comprehension-iterable-expression-unsupported",
            "the comprehension iterable must be a read-only local List value",
        );
    }
    validate_expression_shape(&generator.iter, lowerer)?;
    if !comprehension_expression_is_pure_total(mapped)
        || second_mapped.is_some_and(|value| !comprehension_expression_is_pure_total(value))
    {
        return failure(
            "frontend.python.contracts.comprehension-mapper-effect-unsupported",
            "comprehension outputs must be total, side-effect-free primitive expressions",
        );
    }
    for filter in &generator.ifs {
        if !comprehension_expression_is_pure_total(filter) {
            return failure(
                "frontend.python.contracts.comprehension-filter-effect-unsupported",
                "comprehension filters must be total, side-effect-free primitive expressions",
            );
        }
    }
    Ok(())
}

fn comprehension_expression_is_pure_total(expression: &ast::Expr) -> bool {
    match expression {
        ast::Expr::Name(_) => true,
        ast::Expr::Constant(constant) => matches!(
            constant.value,
            ast::Constant::Bool(_)
                | ast::Constant::Int(_)
                | ast::Constant::Str(_)
                | ast::Constant::Bytes(_)
        ),
        ast::Expr::BoolOp(operation) => operation
            .values
            .iter()
            .all(comprehension_expression_is_pure_total),
        ast::Expr::IfExp(conditional) => {
            comprehension_expression_is_pure_total(&conditional.test)
                && comprehension_expression_is_pure_total(&conditional.body)
                && comprehension_expression_is_pure_total(&conditional.orelse)
        }
        ast::Expr::BinOp(operation) => {
            matches!(
                operation.op,
                ast::Operator::Add | ast::Operator::Sub | ast::Operator::Mult | ast::Operator::Mod
            ) && comprehension_expression_is_pure_total(&operation.left)
                && comprehension_expression_is_pure_total(&operation.right)
                && (operation.op != ast::Operator::Mod
                    || matches!(
                        operation.right.as_ref(),
                        ast::Expr::Constant(ast::ExprConstant {
                            value: ast::Constant::Int(value),
                            ..
                        }) if value.to_string().parse::<u64>().is_ok_and(|value| value > 0)
                    ))
        }
        ast::Expr::UnaryOp(operation) => {
            matches!(
                operation.op,
                ast::UnaryOp::Not | ast::UnaryOp::USub | ast::UnaryOp::UAdd
            ) && comprehension_expression_is_pure_total(&operation.operand)
        }
        ast::Expr::Compare(comparison) => {
            !comparison.ops.is_empty()
                && comparison.ops.len() == comparison.comparators.len()
                && comparison.ops.iter().all(|operator| {
                    matches!(
                        operator,
                        ast::CmpOp::Eq
                            | ast::CmpOp::NotEq
                            | ast::CmpOp::Lt
                            | ast::CmpOp::LtE
                            | ast::CmpOp::Gt
                            | ast::CmpOp::GtE
                    )
                })
                && comprehension_expression_is_pure_total(&comparison.left)
                && comparison
                    .comparators
                    .iter()
                    .all(comprehension_expression_is_pure_total)
        }
        _ => false,
    }
}

fn collect_function_local_bindings(statements: &[ast::Stmt], bindings: &mut BTreeSet<String>) {
    for statement in statements {
        match statement {
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    if let ast::Expr::Name(name) = target {
                        bindings.insert(name.id.to_string());
                    }
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                if let ast::Expr::Name(name) = assignment.target.as_ref() {
                    bindings.insert(name.id.to_string());
                }
            }
            ast::Stmt::AugAssign(assignment) => {
                if let ast::Expr::Name(name) = assignment.target.as_ref() {
                    bindings.insert(name.id.to_string());
                }
            }
            ast::Stmt::If(branch) => {
                collect_function_local_bindings(&branch.body, bindings);
                collect_function_local_bindings(&branch.orelse, bindings);
            }
            ast::Stmt::While(loop_statement) => {
                collect_function_local_bindings(&loop_statement.body, bindings);
                collect_function_local_bindings(&loop_statement.orelse, bindings);
            }
            ast::Stmt::For(loop_statement) => {
                collect_finite_for_target_bindings(&loop_statement.target, bindings);
                collect_function_local_bindings(&loop_statement.body, bindings);
                collect_function_local_bindings(&loop_statement.orelse, bindings);
            }
            ast::Stmt::Try(try_statement) => {
                collect_function_local_bindings(&try_statement.body, bindings);
                collect_function_local_bindings(&try_statement.orelse, bindings);
                collect_function_local_bindings(&try_statement.finalbody, bindings);
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    if let Some(name) = &handler.name {
                        bindings.insert(name.to_string());
                    }
                    collect_function_local_bindings(&handler.body, bindings);
                }
            }
            _ => {}
        }
    }
}

fn function_local_binding_names(statements: &[ast::Stmt]) -> BTreeSet<String> {
    let mut bindings = BTreeSet::new();
    collect_function_local_bindings(statements, &mut bindings);
    for global in function_global_binding_names(statements) {
        bindings.remove(&global);
    }
    bindings
}

fn function_global_binding_names(statements: &[ast::Stmt]) -> BTreeSet<String> {
    let mut bindings = BTreeSet::new();
    collect_function_global_bindings(statements, &mut bindings);
    bindings
}

fn collect_function_global_bindings(statements: &[ast::Stmt], bindings: &mut BTreeSet<String>) {
    for statement in statements {
        match statement {
            ast::Stmt::Global(declaration) => {
                bindings.extend(declaration.names.iter().map(ToString::to_string));
            }
            ast::Stmt::If(branch) => {
                collect_function_global_bindings(&branch.body, bindings);
                collect_function_global_bindings(&branch.orelse, bindings);
            }
            ast::Stmt::While(loop_statement) => {
                collect_function_global_bindings(&loop_statement.body, bindings);
                collect_function_global_bindings(&loop_statement.orelse, bindings);
            }
            ast::Stmt::For(loop_statement) => {
                collect_function_global_bindings(&loop_statement.body, bindings);
                collect_function_global_bindings(&loop_statement.orelse, bindings);
            }
            ast::Stmt::Try(try_statement) => {
                collect_function_global_bindings(&try_statement.body, bindings);
                collect_function_global_bindings(&try_statement.orelse, bindings);
                collect_function_global_bindings(&try_statement.finalbody, bindings);
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    collect_function_global_bindings(&handler.body, bindings);
                }
            }
            _ => {}
        }
    }
}

fn is_static_module_global_write_value(expression: &ast::Expr) -> bool {
    match expression {
        ast::Expr::Name(_) | ast::Expr::Constant(_) => true,
        ast::Expr::Tuple(tuple) => tuple.elts.iter().all(is_static_module_global_write_value),
        ast::Expr::List(list) => list.elts.iter().all(is_static_module_global_write_value),
        _ => false,
    }
}

fn module_global_permission(name: &str) -> Term {
    Term::Variable {
        name: format!("module-global-permission::{name}"),
        sort: Sort::Bool,
    }
}

fn finite_for_target_is_supported(target: &ast::Expr) -> bool {
    match target {
        ast::Expr::Name(_) => true,
        ast::Expr::Tuple(tuple) => {
            !tuple.elts.is_empty()
                && tuple
                    .elts
                    .iter()
                    .filter(|element| matches!(element, ast::Expr::Starred(_)))
                    .count()
                    <= 1
                && tuple.elts.iter().all(finite_for_target_is_supported)
        }
        ast::Expr::List(list) => {
            !list.elts.is_empty()
                && list
                    .elts
                    .iter()
                    .filter(|element| matches!(element, ast::Expr::Starred(_)))
                    .count()
                    <= 1
                && list.elts.iter().all(finite_for_target_is_supported)
        }
        ast::Expr::Starred(starred) => matches!(starred.value.as_ref(), ast::Expr::Name(_)),
        _ => false,
    }
}

fn collect_finite_for_target_bindings(target: &ast::Expr, bindings: &mut BTreeSet<String>) {
    match target {
        ast::Expr::Name(name) => {
            bindings.insert(name.id.to_string());
        }
        ast::Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                collect_finite_for_target_bindings(element, bindings);
            }
        }
        ast::Expr::List(list) => {
            for element in &list.elts {
                collect_finite_for_target_bindings(element, bindings);
            }
        }
        ast::Expr::Starred(starred) => {
            collect_finite_for_target_bindings(&starred.value, bindings);
        }
        _ => {}
    }
}

/// Collect names whose evaluation is unconditional once the containing statement begins.
///
/// Conditional-expression arms, later boolean operands, and later comparison operands are
/// deliberately excluded. Turning those reads into unconditional definedness obligations would
/// reject valid Python programs whose short-circuit condition makes an undefined arm unreachable.
/// Those richer guarded reads remain on the existing fail-closed expression boundary.
fn collect_unconditional_expression_reads(expression: &ast::Expr, names: &mut BTreeSet<String>) {
    match expression {
        ast::Expr::Name(name) => {
            names.insert(name.id.to_string());
        }
        ast::Expr::BoolOp(operation) => {
            if let Some(first) = operation.values.first() {
                collect_unconditional_expression_reads(first, names);
            }
        }
        ast::Expr::IfExp(conditional) => {
            collect_unconditional_expression_reads(&conditional.test, names);
        }
        ast::Expr::BinOp(operation) => {
            collect_unconditional_expression_reads(&operation.left, names);
            collect_unconditional_expression_reads(&operation.right, names);
        }
        ast::Expr::UnaryOp(operation) => {
            collect_unconditional_expression_reads(&operation.operand, names);
        }
        ast::Expr::Compare(comparison) => {
            collect_unconditional_expression_reads(&comparison.left, names);
            if let Some(first) = comparison.comparators.first() {
                collect_unconditional_expression_reads(first, names);
            }
        }
        ast::Expr::Call(call) => {
            collect_unconditional_expression_reads(&call.func, names);
            for argument in &call.args {
                collect_unconditional_expression_reads(argument, names);
            }
            for keyword in &call.keywords {
                collect_unconditional_expression_reads(&keyword.value, names);
            }
        }
        ast::Expr::Attribute(attribute) => {
            collect_unconditional_expression_reads(&attribute.value, names);
        }
        ast::Expr::Subscript(subscript) => {
            collect_unconditional_expression_reads(&subscript.value, names);
            collect_unconditional_expression_reads(&subscript.slice, names);
        }
        ast::Expr::Starred(starred) => {
            collect_unconditional_expression_reads(&starred.value, names);
        }
        ast::Expr::List(list) => {
            for element in &list.elts {
                collect_unconditional_expression_reads(element, names);
            }
        }
        ast::Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                collect_unconditional_expression_reads(element, names);
            }
        }
        ast::Expr::Set(set) => {
            for element in &set.elts {
                collect_unconditional_expression_reads(element, names);
            }
        }
        ast::Expr::Dict(dictionary) => {
            for key in dictionary.keys.iter().flatten() {
                collect_unconditional_expression_reads(key, names);
            }
            for value in &dictionary.values {
                collect_unconditional_expression_reads(value, names);
            }
        }
        ast::Expr::JoinedStr(joined) => {
            for value in &joined.values {
                collect_unconditional_expression_reads(value, names);
            }
        }
        ast::Expr::FormattedValue(formatted) => {
            collect_unconditional_expression_reads(&formatted.value, names);
            if let Some(specification) = formatted.format_spec.as_deref() {
                collect_unconditional_expression_reads(specification, names);
            }
        }
        ast::Expr::Slice(slice) => {
            if let Some(lower) = slice.lower.as_deref() {
                collect_unconditional_expression_reads(lower, names);
            }
            if let Some(upper) = slice.upper.as_deref() {
                collect_unconditional_expression_reads(upper, names);
            }
            if let Some(step) = slice.step.as_deref() {
                collect_unconditional_expression_reads(step, names);
            }
        }
        _ => {}
    }
}

fn statement_unconditional_read_names(statement: &ast::Stmt) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let expression = match statement {
        ast::Stmt::Assign(assignment) => Some(assignment.value.as_ref()),
        ast::Stmt::AnnAssign(assignment) => assignment.value.as_deref(),
        ast::Stmt::AugAssign(assignment) => {
            collect_unconditional_expression_reads(&assignment.target, &mut names);
            Some(assignment.value.as_ref())
        }
        ast::Stmt::Assert(assertion) => Some(assertion.test.as_ref()),
        ast::Stmt::Expr(expression) => Some(expression.value.as_ref()),
        ast::Stmt::Return(returned) => returned.value.as_deref(),
        ast::Stmt::Raise(raised) => {
            if let Some(cause) = raised.cause.as_deref() {
                collect_unconditional_expression_reads(cause, &mut names);
            }
            raised.exc.as_deref()
        }
        ast::Stmt::If(branch) => Some(branch.test.as_ref()),
        ast::Stmt::While(loop_statement) => Some(loop_statement.test.as_ref()),
        ast::Stmt::For(loop_statement) => Some(loop_statement.iter.as_ref()),
        _ => None,
    };
    if let Some(expression) = expression {
        collect_unconditional_expression_reads(expression, &mut names);
    }
    names
}

#[allow(clippy::too_many_arguments)]
fn retain_states_with_defined_local_reads(
    statement: &ast::Stmt,
    states: Vec<SymbolicState>,
    local_bindings: &BTreeSet<String>,
    function: &ast::StmtFunctionDef,
    path: &str,
    source: &str,
    obligations: &mut Vec<Obligation>,
) -> Vec<SymbolicState> {
    let read_locals = statement_unconditional_read_names(statement)
        .into_iter()
        .filter(|name| local_bindings.contains(name))
        .collect::<Vec<_>>();
    if read_locals.is_empty() {
        return states;
    }
    let byte_offset = u32::from(statement.range().start());
    let mut retained = Vec::with_capacity(states.len());
    for state in states {
        let missing = read_locals
            .iter()
            .filter(|name| !state.environment.contains_key(name.as_str()))
            .collect::<Vec<_>>();
        if missing.is_empty() {
            retained.push(state);
            continue;
        }
        for name in missing {
            obligations.push(Obligation {
                id: format!(
                    "{}:undefined-local:{}:{}:path:{}",
                    function.name,
                    name,
                    byte_offset,
                    obligations.len()
                ),
                expectation: ObligationExpectation::Prove,
                assumptions: state.assumptions.clone(),
                conclusion: Term::Bool { value: false },
                path: path.to_owned(),
                byte_offset,
                line: source_location(source, byte_offset).0,
                column: source_location(source, byte_offset).1,
            });
        }
        // Reading an undefined local raises before this statement can produce a normal successor.
    }
    retained
}

#[allow(clippy::too_many_arguments)]
fn retain_states_with_module_write_permission(
    statement: &ast::Stmt,
    states: Vec<SymbolicState>,
    global_names: &BTreeSet<String>,
    function: &ast::StmtFunctionDef,
    path: &str,
    source: &str,
    obligations: &mut Vec<Obligation>,
) -> Result<Vec<SymbolicState>, ContractFailure> {
    let ast::Stmt::Assign(assignment) = statement else {
        return Ok(states);
    };
    let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
        return Ok(states);
    };
    if !global_names.contains(target.id.as_str()) {
        return Ok(states);
    }
    let byte_offset = u32::from(target.range.start());
    let permission = module_global_permission(target.id.as_str());
    let mut retained = Vec::with_capacity(states.len());
    for state in states {
        let obligation = Obligation {
            id: format!(
                "{}:field-write-permission:{}:{}:path:{}",
                function.name,
                target.id,
                byte_offset,
                obligations.len()
            ),
            expectation: ObligationExpectation::Prove,
            assumptions: state.assumptions.clone(),
            conclusion: permission.clone(),
            path: path.to_owned(),
            byte_offset,
            line: source_location(source, byte_offset).0,
            column: source_location(source, byte_offset).1,
        };
        let satisfied = discharge(&obligation)
            .map_err(|message| ContractFailure {
                code: "solver.translation-failed",
                message,
            })?
            .satisfied();
        obligations.push(obligation);
        if satisfied {
            retained.push(state);
        }
        // A failed permission check has no normal successor, so later writes on that path cannot
        // manufacture duplicate diagnostics.
    }
    Ok(retained)
}

#[allow(clippy::too_many_arguments)]
fn retain_states_with_module_read_permission(
    statement: &ast::Stmt,
    states: Vec<SymbolicState>,
    global_names: &BTreeSet<String>,
    function: &ast::StmtFunctionDef,
    path: &str,
    source: &str,
    obligations: &mut Vec<Obligation>,
) -> Result<Vec<SymbolicState>, ContractFailure> {
    let read_globals = statement_unconditional_read_names(statement)
        .into_iter()
        .filter(|name| global_names.contains(name))
        .collect::<Vec<_>>();
    if read_globals.is_empty() {
        return Ok(states);
    }
    let byte_offset = u32::from(statement.range().start());
    let mut retained = Vec::with_capacity(states.len());
    for state in states {
        let mut all_satisfied = true;
        for name in &read_globals {
            let obligation = Obligation {
                id: format!(
                    "{}:assignment-read-permission:{}:{}:path:{}",
                    function.name,
                    name,
                    byte_offset,
                    obligations.len()
                ),
                expectation: ObligationExpectation::Prove,
                assumptions: state.assumptions.clone(),
                conclusion: module_global_permission(name),
                path: path.to_owned(),
                byte_offset,
                line: source_location(source, byte_offset).0,
                column: source_location(source, byte_offset).1,
            };
            all_satisfied &= discharge(&obligation)
                .map_err(|message| ContractFailure {
                    code: "solver.translation-failed",
                    message,
                })?
                .satisfied();
            obligations.push(obligation);
        }
        if all_satisfied {
            retained.push(state);
        }
        // A failed read cannot produce a normal successor for the containing statement.
    }
    Ok(retained)
}

#[allow(clippy::too_many_arguments)]
fn execute_statements(
    statements: &[ast::Stmt],
    mut states: Vec<SymbolicState>,
    function: &ast::StmtFunctionDef,
    lowerer: &ExpressionLowerer<'_>,
    return_sort: &Sort,
    path: &str,
    source: &str,
    obligations: &mut Vec<Obligation>,
    return_paths: &mut Vec<ReturnPath>,
    exceptional_paths: &mut Vec<ExceptionalPath>,
) -> Result<Vec<SymbolicState>, ContractFailure> {
    let local_bindings = function_local_binding_names(&function.body);
    let global_names = function_global_binding_names(&function.body);
    for statement in statements {
        if states.is_empty() {
            break;
        }
        states = retain_states_with_defined_local_reads(
            statement,
            std::mem::take(&mut states),
            &local_bindings,
            function,
            path,
            source,
            obligations,
        );
        if states.is_empty() {
            break;
        }
        states = retain_states_with_module_read_permission(
            statement,
            std::mem::take(&mut states),
            &global_names,
            function,
            path,
            source,
            obligations,
        )?;
        if states.is_empty() {
            break;
        }
        states = retain_states_with_module_write_permission(
            statement,
            std::mem::take(&mut states),
            &global_names,
            function,
            path,
            source,
            obligations,
        )?;
        if states.is_empty() {
            break;
        }
        match statement {
            ast::Stmt::Global(_) => {}
            ast::Stmt::Assign(assignment)
                if assignment.targets.len() == 1
                    && lowerer.enumerate_builtin_call(&assignment.value).is_some() =>
            {
                states = prepare_runtime_expression_states(
                    &assignment.value,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let ast::Expr::Name(target) = &assignment.targets[0] else {
                    return unsupported_statement(function, statement);
                };
                let call = lowerer
                    .enumerate_builtin_call(&assignment.value)
                    .expect("guard established canonical enumerate call");
                let byte_offset = u32::from(call.range.start());
                let declared_sort = assignment_type_sort(assignment, lowerer, source)?;
                for state in &mut states {
                    let result_name = format!(
                        "{}::enumerate-result:{byte_offset}:{}",
                        function.name, target.id
                    );
                    let effects =
                        lowerer.enumerate_call_effects(call, &state.environment, &result_name)?;
                    let value = match &declared_sort {
                        Some(expected) => coerce_to_type_comment(
                            effects.value.clone(),
                            expected,
                            "type-commented enumerate assignment",
                        )?,
                        None => effects.value.clone(),
                    };
                    apply_source_call_effects(
                        state,
                        effects,
                        function,
                        path,
                        source,
                        byte_offset,
                        obligations,
                        exceptional_paths,
                    );
                    state.identities.insert(
                        target.id.to_string(),
                        PythonObjectIdentity::Fresh(byte_offset),
                    );
                    state.environment.insert(target.id.to_string(), value);
                }
            }
            ast::Stmt::Assign(assignment)
                if assignment.targets.len() == 1
                    && lowerer.sorted_builtin_call(&assignment.value).is_some() =>
            {
                states = prepare_runtime_expression_states(
                    &assignment.value,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let ast::Expr::Name(target) = &assignment.targets[0] else {
                    return unsupported_statement(function, statement);
                };
                let call = lowerer
                    .sorted_builtin_call(&assignment.value)
                    .expect("guard established canonical sorted call");
                let byte_offset = u32::from(call.range.start());
                let declared_sort = assignment_type_sort(assignment, lowerer, source)?;
                for state in &mut states {
                    let result_name = format!(
                        "{}::sorted-result:{byte_offset}:{}",
                        function.name, target.id
                    );
                    let effects =
                        lowerer.sorted_call_effects(call, &state.environment, &result_name)?;
                    let value = match &declared_sort {
                        Some(expected) => coerce_to_type_comment(
                            effects.value.clone(),
                            expected,
                            "type-commented sorted assignment",
                        )?,
                        None => effects.value.clone(),
                    };
                    apply_source_call_effects(
                        state,
                        effects,
                        function,
                        path,
                        source,
                        byte_offset,
                        obligations,
                        exceptional_paths,
                    );
                    state.identities.insert(
                        target.id.to_string(),
                        PythonObjectIdentity::Fresh(byte_offset),
                    );
                    state.environment.insert(target.id.to_string(), value);
                }
            }
            ast::Stmt::Assign(assignment)
                if assignment.targets.len() == 1
                    && lowerer.contract_source_call(&assignment.value).is_some() =>
            {
                states = prepare_runtime_expression_states(
                    &assignment.value,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let ast::Expr::Name(target) = &assignment.targets[0] else {
                    return unsupported_statement(function, statement);
                };
                let call = lowerer
                    .contract_source_call(&assignment.value)
                    .expect("guard established contracted source call");
                let byte_offset = u32::from(call.range.start());
                let declared_sort = assignment_type_sort(assignment, lowerer, source)?;
                for state in &mut states {
                    let result_name = format!(
                        "{}::call-result:{byte_offset}:{}",
                        function.name,
                        obligations.len()
                    );
                    let effects = lowerer.source_call_effects(
                        call,
                        &state.environment,
                        None,
                        &result_name,
                    )?;
                    let value = match &declared_sort {
                        Some(expected) => coerce_to_type_comment(
                            effects.value.clone(),
                            expected,
                            "type-commented source call assignment",
                        )?,
                        None => effects.value.clone(),
                    };
                    apply_source_call_effects(
                        state,
                        effects.clone(),
                        function,
                        path,
                        source,
                        byte_offset,
                        obligations,
                        exceptional_paths,
                    );
                    state.identities.remove(target.id.as_str());
                    state.environment.insert(target.id.to_string(), value);
                }
            }
            ast::Stmt::Assign(assignment) if assignment.targets.len() == 1 => {
                states = prepare_runtime_expression_states(
                    &assignment.value,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let ast::Expr::Name(target) = &assignment.targets[0] else {
                    return unsupported_statement(function, statement);
                };
                let declared_sort = assignment_type_sort(assignment, lowerer, source)?;
                for state in &mut states {
                    let object_identity = python_object_identity(
                        &assignment.value,
                        &state.environment,
                        &state.identities,
                    );
                    let value = match &declared_sort {
                        Some(expected) => lower_type_commented_expression(
                            lowerer,
                            &assignment.value,
                            &state.environment,
                            None,
                            expected,
                            "type-commented assignment",
                        )?,
                        None => lowerer.lower(&assignment.value, &state.environment, None)?,
                    };
                    if let Some(object_identity) = object_identity {
                        state
                            .identities
                            .insert(target.id.to_string(), object_identity);
                    } else {
                        state.identities.remove(target.id.as_str());
                    }
                    state.environment.insert(target.id.to_string(), value);
                }
            }
            ast::Stmt::AnnAssign(assignment)
                if assignment
                    .value
                    .as_deref()
                    .and_then(|value| lowerer.sorted_builtin_call(value))
                    .is_some() =>
            {
                let ast::Expr::Name(target) = assignment.target.as_ref() else {
                    return unsupported_statement(function, statement);
                };
                let value_expression = assignment
                    .value
                    .as_deref()
                    .expect("guard established initialized sorted assignment");
                states = prepare_runtime_expression_states(
                    value_expression,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let call = lowerer
                    .sorted_builtin_call(value_expression)
                    .expect("guard established canonical sorted call");
                let expected_sort = annotation_sort(Some(&assignment.annotation))?;
                let byte_offset = u32::from(call.range.start());
                for state in &mut states {
                    let result_name = format!(
                        "{}::sorted-result:{byte_offset}:{}",
                        function.name, target.id
                    );
                    let effects =
                        lowerer.sorted_call_effects(call, &state.environment, &result_name)?;
                    let value = coerce_to_sort(
                        effects.value.clone(),
                        &expected_sort,
                        "annotated sorted assignment",
                    )?;
                    apply_source_call_effects(
                        state,
                        effects,
                        function,
                        path,
                        source,
                        byte_offset,
                        obligations,
                        exceptional_paths,
                    );
                    state.identities.insert(
                        target.id.to_string(),
                        PythonObjectIdentity::Fresh(byte_offset),
                    );
                    state.environment.insert(target.id.to_string(), value);
                }
            }
            ast::Stmt::AnnAssign(assignment)
                if assignment
                    .value
                    .as_deref()
                    .and_then(|value| lowerer.contract_source_call(value))
                    .is_some() =>
            {
                let ast::Expr::Name(target) = assignment.target.as_ref() else {
                    return unsupported_statement(function, statement);
                };
                let value_expression = assignment
                    .value
                    .as_deref()
                    .expect("guard established initialized annotated assignment");
                states = prepare_runtime_expression_states(
                    value_expression,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let call = lowerer
                    .contract_source_call(value_expression)
                    .expect("guard established contracted source call");
                let expected_sort = annotation_sort(Some(&assignment.annotation))?;
                let byte_offset = u32::from(call.range.start());
                for state in &mut states {
                    let result_name = format!(
                        "{}::call-result:{byte_offset}:{}",
                        function.name,
                        obligations.len()
                    );
                    let effects = lowerer.source_call_effects(
                        call,
                        &state.environment,
                        None,
                        &result_name,
                    )?;
                    let value = coerce_to_sort(
                        effects.value.clone(),
                        &expected_sort,
                        "annotated source call assignment",
                    )?;
                    apply_source_call_effects(
                        state,
                        effects,
                        function,
                        path,
                        source,
                        byte_offset,
                        obligations,
                        exceptional_paths,
                    );
                    state.identities.remove(target.id.as_str());
                    state.environment.insert(target.id.to_string(), value);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                let ast::Expr::Name(target) = assignment.target.as_ref() else {
                    return unsupported_statement(function, statement);
                };
                let value_expression =
                    assignment.value.as_deref().ok_or_else(|| ContractFailure {
                        code: "frontend.python.contracts.uninitialized-local",
                        message: format!(
                            "function {:?} declares uninitialized local {:?}",
                            function.name, target.id
                        ),
                    })?;
                states = prepare_runtime_expression_states(
                    value_expression,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let expected_sort = annotation_sort(Some(&assignment.annotation))?;
                for state in &mut states {
                    let object_identity = python_object_identity(
                        value_expression,
                        &state.environment,
                        &state.identities,
                    );
                    let value = lowerer.lower_expected(
                        value_expression,
                        &state.environment,
                        None,
                        &expected_sort,
                        "annotated assignment",
                    )?;
                    if let Some(object_identity) = object_identity {
                        state
                            .identities
                            .insert(target.id.to_string(), object_identity);
                    } else {
                        state.identities.remove(target.id.as_str());
                    }
                    state.environment.insert(target.id.to_string(), value);
                }
            }
            ast::Stmt::AugAssign(assignment) => {
                let ast::Expr::Name(target) = assignment.target.as_ref() else {
                    return unsupported_statement(function, statement);
                };
                states = prepare_runtime_expression_states(
                    &assignment.value,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                for state in &mut states {
                    let left = state
                        .environment
                        .get(target.id.as_str())
                        .cloned()
                        .ok_or_else(|| ContractFailure {
                            code: "frontend.python.name.unresolved",
                            message: format!(
                                "augmented assignment reads undefined {:?}",
                                target.id
                            ),
                        })?;
                    let left = coerce_python_int(left, "augmented assignment target")?;
                    let right = coerce_python_int(
                        lowerer.lower(&assignment.value, &state.environment, None)?,
                        "augmented assignment value",
                    )?;
                    let (left, right) = (Box::new(left), Box::new(right));
                    let value = match assignment.op {
                        ast::Operator::Add => Term::Add { left, right },
                        ast::Operator::Sub => Term::Subtract { left, right },
                        ast::Operator::Mult => Term::Multiply { left, right },
                        _ => return unsupported_statement(function, statement),
                    };
                    state.environment.insert(target.id.to_string(), value);
                }
            }
            ast::Stmt::Assert(assertion) => {
                states = prepare_runtime_expression_states(
                    &assertion.test,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                for state in &mut states {
                    let conclusion = lower_proven_object_identity(
                        &assertion.test,
                        lowerer,
                        &state.environment,
                        &state.identities,
                    )?
                    .map(Ok)
                    .unwrap_or_else(|| lowerer.lower(&assertion.test, &state.environment, None))?;
                    ensure_boolean(&conclusion, "assertion")?;
                    let byte_offset = assertion.range.start().into();
                    obligations.push(Obligation {
                        id: format!(
                            "{}:assert:{}:path:{}",
                            function.name,
                            u32::from(assertion.range.start()),
                            obligations.len()
                        ),
                        expectation: ObligationExpectation::Prove,
                        assumptions: state.assumptions.clone(),
                        conclusion: conclusion.clone(),
                        path: path.to_owned(),
                        byte_offset,
                        line: source_location(source, byte_offset).0,
                        column: source_location(source, byte_offset).1,
                    });
                    state.assumptions.push(conclusion);
                }
            }
            ast::Stmt::Expr(expression_statement)
                if contract_assertion(expression_statement.value.as_ref()).is_some() =>
            {
                let expression = contract_assertion(expression_statement.value.as_ref())
                    .expect("guard established contract assertion");
                states = prepare_runtime_expression_states(
                    expression,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let pure = function.decorator_list.iter().any(
                    |decorator| matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "Pure"),
                );
                let byte_offset = if pure {
                    function.range.start().into()
                } else {
                    expression_statement.range.start().into()
                };
                for state in &mut states {
                    let conclusion = lower_proven_object_identity(
                        expression,
                        lowerer,
                        &state.environment,
                        &state.identities,
                    )?
                    .map(Ok)
                    .unwrap_or_else(|| lowerer.lower(expression, &state.environment, None))?;
                    ensure_boolean(&conclusion, "Assert argument")?;
                    obligations.push(Obligation {
                        id: format!(
                            "{}:{}:{}:path:{}",
                            function.name,
                            if pure { "pure-assert" } else { "assert" },
                            u32::from(expression_statement.range.start()),
                            obligations.len()
                        ),
                        expectation: ObligationExpectation::Prove,
                        assumptions: state.assumptions.clone(),
                        conclusion: conclusion.clone(),
                        path: path.to_owned(),
                        byte_offset,
                        line: source_location(source, byte_offset).0,
                        column: source_location(source, byte_offset).1,
                    });
                    state.assumptions.push(conclusion);
                }
            }
            ast::Stmt::Expr(expression_statement)
                if contract_refutation(expression_statement.value.as_ref()).is_some() =>
            {
                let expression = contract_refutation(expression_statement.value.as_ref())
                    .expect("guard established contract refutation");
                states = prepare_runtime_expression_states(
                    expression,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let byte_offset = expression_statement.range.start().into();
                for state in &states {
                    let conclusion = lower_proven_object_identity(
                        expression,
                        lowerer,
                        &state.environment,
                        &state.identities,
                    )?
                    .map(Ok)
                    .unwrap_or_else(|| lowerer.lower(expression, &state.environment, None))?;
                    ensure_boolean(&conclusion, "Refute argument")?;
                    obligations.push(Obligation {
                        id: format!(
                            "{}:refute:{}:path:{}",
                            function.name,
                            u32::from(expression_statement.range.start()),
                            obligations.len()
                        ),
                        expectation: ObligationExpectation::Refute,
                        assumptions: state.assumptions.clone(),
                        conclusion,
                        path: path.to_owned(),
                        byte_offset,
                        line: source_location(source, byte_offset).0,
                        column: source_location(source, byte_offset).1,
                    });
                }
            }
            ast::Stmt::Expr(expression_statement)
                if lowerer
                    .source_call(expression_statement.value.as_ref())
                    .is_some() =>
            {
                states = prepare_runtime_expression_states(
                    expression_statement.value.as_ref(),
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let call = lowerer
                    .source_call(expression_statement.value.as_ref())
                    .expect("guard established source call");
                let byte_offset = expression_statement.range.start().into();
                for state in &mut states {
                    let result_name = format!(
                        "{}::call-result:{byte_offset}:{}",
                        function.name,
                        obligations.len()
                    );
                    let effects = lowerer.source_call_effects(
                        call,
                        &state.environment,
                        None,
                        &result_name,
                    )?;
                    apply_source_call_effects(
                        state,
                        effects,
                        function,
                        path,
                        source,
                        byte_offset,
                        obligations,
                        exceptional_paths,
                    );
                }
            }
            statement if is_inert_string_statement(statement) => {}
            ast::Stmt::Pass(_) => {}
            ast::Stmt::Raise(raise_statement) => {
                let exception_type =
                    raised_exception_type(raise_statement, lowerer.exception_hierarchy)?;
                let byte_offset = u32::from(raise_statement.range.start());
                for state in std::mem::take(&mut states) {
                    exceptional_paths.push(ExceptionalPath {
                        state,
                        exception_type: exception_type.clone(),
                        byte_offset,
                        application_precondition: false,
                    });
                }
            }
            ast::Stmt::If(branch) => {
                states = prepare_runtime_expression_states(
                    &branch.test,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let incoming = std::mem::take(&mut states);
                let mut outgoing = Vec::new();
                for state in incoming {
                    let condition = coerce_truthy(
                        lowerer.lower(&branch.test, &state.environment, None)?,
                        "if condition",
                    )?;

                    let mut then_state = state.clone();
                    then_state.assumptions.push(condition.clone());
                    outgoing.extend(execute_statements(
                        &branch.body,
                        vec![then_state],
                        function,
                        lowerer,
                        return_sort,
                        path,
                        source,
                        obligations,
                        return_paths,
                        exceptional_paths,
                    )?);

                    let mut else_state = state;
                    else_state.assumptions.push(Term::Not {
                        value: Box::new(condition),
                    });
                    outgoing.extend(execute_statements(
                        &branch.orelse,
                        vec![else_state],
                        function,
                        lowerer,
                        return_sort,
                        path,
                        source,
                        obligations,
                        return_paths,
                        exceptional_paths,
                    )?);
                }
                states = outgoing;
            }
            ast::Stmt::While(loop_statement) => {
                states = execute_while(
                    loop_statement,
                    std::mem::take(&mut states),
                    function,
                    lowerer,
                    return_sort,
                    path,
                    source,
                    obligations,
                    return_paths,
                    exceptional_paths,
                )?;
            }
            ast::Stmt::For(loop_statement) => {
                states = execute_finite_for(
                    loop_statement,
                    std::mem::take(&mut states),
                    function,
                    lowerer,
                    return_sort,
                    path,
                    source,
                    obligations,
                    return_paths,
                    exceptional_paths,
                )?;
            }
            ast::Stmt::Try(try_statement) => {
                states = execute_try(
                    try_statement,
                    std::mem::take(&mut states),
                    function,
                    lowerer,
                    return_sort,
                    path,
                    source,
                    obligations,
                    return_paths,
                    exceptional_paths,
                )?;
            }
            ast::Stmt::Return(return_statement)
                if return_statement
                    .value
                    .as_deref()
                    .and_then(|value| lowerer.sorted_builtin_call(value))
                    .is_some() =>
            {
                let expression = return_statement
                    .value
                    .as_deref()
                    .expect("guard established sorted return value");
                states = prepare_runtime_expression_states(
                    expression,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let call = lowerer
                    .sorted_builtin_call(expression)
                    .expect("guard established canonical sorted call");
                let byte_offset = u32::from(call.range.start());
                for mut state in std::mem::take(&mut states) {
                    let result_name =
                        format!("{}::sorted-result:{byte_offset}:return", function.name);
                    let effects =
                        lowerer.sorted_call_effects(call, &state.environment, &result_name)?;
                    let value =
                        coerce_to_sort(effects.value.clone(), return_sort, "sorted return")?;
                    apply_source_call_effects(
                        &mut state,
                        effects,
                        function,
                        path,
                        source,
                        byte_offset,
                        obligations,
                        exceptional_paths,
                    );
                    return_paths.push(ReturnPath {
                        state,
                        value,
                        byte_offset: return_statement.range.start().into(),
                    });
                }
            }
            ast::Stmt::Return(return_statement)
                if return_statement
                    .value
                    .as_deref()
                    .and_then(|value| lowerer.contract_source_call(value))
                    .is_some() =>
            {
                let expression = return_statement
                    .value
                    .as_deref()
                    .expect("guard established return value");
                states = prepare_runtime_expression_states(
                    expression,
                    std::mem::take(&mut states),
                    lowerer,
                    exceptional_paths,
                )?;
                let call = lowerer
                    .contract_source_call(expression)
                    .expect("guard established contracted source call");
                let byte_offset = u32::from(call.range.start());
                for mut state in std::mem::take(&mut states) {
                    let result_name = format!(
                        "{}::call-result:{byte_offset}:{}",
                        function.name,
                        obligations.len()
                    );
                    let effects = lowerer.source_call_effects(
                        call,
                        &state.environment,
                        None,
                        &result_name,
                    )?;
                    let value =
                        coerce_to_sort(effects.value.clone(), return_sort, "function return")?;
                    apply_source_call_effects(
                        &mut state,
                        effects,
                        function,
                        path,
                        source,
                        byte_offset,
                        obligations,
                        exceptional_paths,
                    );
                    return_paths.push(ReturnPath {
                        state,
                        value,
                        byte_offset: return_statement.range.start().into(),
                    });
                }
            }
            ast::Stmt::Return(return_statement) => {
                if let Some(expression) = return_statement.value.as_deref() {
                    states = prepare_runtime_expression_states(
                        expression,
                        std::mem::take(&mut states),
                        lowerer,
                        exceptional_paths,
                    )?;
                }
                for state in std::mem::take(&mut states) {
                    let value = match return_statement.value.as_deref() {
                        Some(expression) => lowerer.lower_expected(
                            expression,
                            &state.environment,
                            None,
                            return_sort,
                            "function return",
                        )?,
                        None => Term::Unit,
                    };
                    let value = coerce_to_sort(value, return_sort, "function return")?;
                    return_paths.push(ReturnPath {
                        state,
                        value,
                        byte_offset: return_statement.range.start().into(),
                    });
                }
            }
            _ => return unsupported_statement(function, statement),
        }
    }
    Ok(states)
}

#[allow(clippy::too_many_arguments)]
fn execute_finite_for(
    loop_statement: &ast::StmtFor,
    incoming: Vec<SymbolicState>,
    function: &ast::StmtFunctionDef,
    lowerer: &ExpressionLowerer<'_>,
    return_sort: &Sort,
    path: &str,
    source: &str,
    obligations: &mut Vec<Obligation>,
    return_paths: &mut Vec<ReturnPath>,
    exceptional_paths: &mut Vec<ExceptionalPath>,
) -> Result<Vec<SymbolicState>, ContractFailure> {
    let declared_sort = loop_statement
        .type_comment
        .as_deref()
        .map(scalar_type_comment_sort)
        .transpose()?;
    let incoming = prepare_runtime_expression_states(
        &loop_statement.iter,
        incoming,
        lowerer,
        exceptional_paths,
    )?;
    let mut outgoing = Vec::new();
    for state in incoming {
        let iterable = lowerer.lower(&loop_statement.iter, &state.environment, None)?;
        match lower_to_sequence(iterable.clone()) {
            Ok(Term::List { values, .. }) => {
                let mut current = vec![state];
                let invariant_count = loop_statement
                    .body
                    .iter()
                    .take_while(|statement| contract_invariant(statement).is_some())
                    .count();
                let invariant_statements = &loop_statement.body[..invariant_count];
                let loop_body = &loop_statement.body[invariant_count..];
                for (iteration, value) in values.into_iter().enumerate() {
                    let value = match &declared_sort {
                        Some(expected) => {
                            coerce_to_type_comment(value, expected, "for target type comment")?
                        }
                        None => value,
                    };
                    for active in &mut current {
                        bind_finite_for_target(
                            &loop_statement.target,
                            value.clone(),
                            &mut active.environment,
                            &mut active.identities,
                        )?;
                    }
                    prove_for_invariants(
                        invariant_statements,
                        &mut current,
                        function,
                        lowerer,
                        path,
                        source,
                        obligations,
                        if iteration == 0 {
                            "invariant-establishment"
                        } else {
                            "invariant-preservation"
                        },
                    )?;
                    current = execute_statements(
                        loop_body,
                        current,
                        function,
                        lowerer,
                        return_sort,
                        path,
                        source,
                        obligations,
                        return_paths,
                        exceptional_paths,
                    )?;
                    if current.is_empty() {
                        break;
                    }
                }
                outgoing.extend(execute_statements(
                    &loop_statement.orelse,
                    current,
                    function,
                    lowerer,
                    return_sort,
                    path,
                    source,
                    obligations,
                    return_paths,
                    exceptional_paths,
                )?);
            }
            _ if matches!(
                iterable.sort().map_err(type_failure)?,
                Sort::List(_) | Sort::VariadicTuple(_)
            ) && matches!(loop_statement.target.as_ref(), ast::Expr::Name(_)) =>
            {
                outgoing.extend(execute_symbolic_list_for(
                    loop_statement,
                    state,
                    iterable,
                    declared_sort.as_ref(),
                    function,
                    lowerer,
                    return_sort,
                    path,
                    source,
                    obligations,
                    return_paths,
                    exceptional_paths,
                )?);
            }
            _ if matches!(
                iterable.sort().map_err(type_failure)?,
                Sort::List(_) | Sort::VariadicTuple(_)
            ) =>
            {
                return failure(
                    "frontend.python.contracts.symbolic-for-unpacking-unsupported",
                    "symbolic sequence iteration requires a direct name target; tuple unpacking needs a concrete iteration value",
                );
            }
            _ => {
                return failure(
                    "frontend.python.contracts.for-iterable-not-finite",
                    "for loops require a statically known finite sequence or an immutable homogeneous List value",
                );
            }
        }
    }
    Ok(outgoing)
}

fn bind_finite_for_target(
    target: &ast::Expr,
    value: Term,
    environment: &mut BTreeMap<String, Term>,
    identities: &mut BTreeMap<String, PythonObjectIdentity>,
) -> Result<(), ContractFailure> {
    match target {
        ast::Expr::Name(name) => {
            environment.insert(name.id.to_string(), value);
            identities.remove(name.id.as_str());
            Ok(())
        }
        ast::Expr::Tuple(ast::ExprTuple { elts: targets, .. })
        | ast::Expr::List(ast::ExprList { elts: targets, .. }) => {
            let (values, variadic_element_sort) = match value {
                Term::Tuple { values } => (values, None),
                Term::VariadicTuple {
                    element_sort,
                    values,
                } => (values, Some(element_sort)),
                _ => {
                    return failure(
                        "frontend.python.contracts.for-target-value-type",
                        "sequence-unpacking for target requires a concrete tuple iteration value",
                    );
                }
            };
            let starred = targets
                .iter()
                .position(|target| matches!(target, ast::Expr::Starred(_)));
            if starred.is_none() && targets.len() != values.len() {
                return failure(
                    "frontend.python.contracts.for-target-arity",
                    format!(
                        "sequence-unpacking for target has {} names but the iteration value has {} elements",
                        targets.len(),
                        values.len()
                    ),
                );
            }
            let required = targets.len().saturating_sub(usize::from(starred.is_some()));
            if values.len() < required {
                return failure(
                    "frontend.python.contracts.for-target-arity",
                    format!(
                        "starred sequence-unpacking target requires at least {required} values, found {}",
                        values.len()
                    ),
                );
            }
            if let Some(starred_position) = starred {
                let suffix_count = targets.len() - starred_position - 1;
                for (nested_target, nested_value) in targets[..starred_position]
                    .iter()
                    .zip(values[..starred_position].iter().cloned())
                {
                    bind_finite_for_target(nested_target, nested_value, environment, identities)?;
                }
                let captured_end = values.len() - suffix_count;
                let captured = values[starred_position..captured_end].to_vec();
                let element_sort = match variadic_element_sort {
                    Some(sort) => sort,
                    None => {
                        let Some(first) = captured.first() else {
                            return failure(
                                "frontend.python.contracts.for-target-star-empty-type-unsupported",
                                "an empty starred target capture from a fixed tuple requires an element-type context",
                            );
                        };
                        let sort = first.sort().map_err(type_failure)?;
                        if captured
                            .iter()
                            .any(|value| value.sort().map_or(true, |actual| actual != sort))
                        {
                            return failure(
                                "frontend.python.contracts.for-target-star-heterogeneous-unsupported",
                                "a starred target capture requires one homogeneous List element sort",
                            );
                        }
                        sort
                    }
                };
                let ast::Expr::Starred(starred_target) = &targets[starred_position] else {
                    unreachable!("starred target position came from this exact target")
                };
                bind_finite_for_target(
                    &starred_target.value,
                    Term::List {
                        element_sort,
                        values: captured,
                    },
                    environment,
                    identities,
                )?;
                for (nested_target, nested_value) in targets[starred_position + 1..]
                    .iter()
                    .zip(values[captured_end..].iter().cloned())
                {
                    bind_finite_for_target(nested_target, nested_value, environment, identities)?;
                }
            } else {
                for (nested_target, nested_value) in targets.iter().zip(values) {
                    bind_finite_for_target(nested_target, nested_value, environment, identities)?;
                }
            }
            Ok(())
        }
        _ => failure(
            "frontend.python.contracts.for-target-unsupported",
            "finite for-loop targets require names or exact tuple/list unpacking",
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn prove_for_invariants(
    invariant_statements: &[ast::Stmt],
    states: &mut [SymbolicState],
    function: &ast::StmtFunctionDef,
    lowerer: &ExpressionLowerer<'_>,
    path: &str,
    source: &str,
    obligations: &mut Vec<Obligation>,
    obligation_kind: &str,
) -> Result<(), ContractFailure> {
    for state in states {
        for invariant_statement in invariant_statements {
            let expression = contract_invariant(invariant_statement)
                .expect("invariant slice contains only invariant statements");
            let byte_offset = statement_offset(invariant_statement);
            for (clause_index, conclusion) in lowerer
                .lower_specification_clauses(
                    expression,
                    &state.environment,
                    None,
                    "for loop invariant",
                )?
                .into_iter()
                .enumerate()
            {
                ensure_boolean(&conclusion, "for loop invariant")?;
                obligations.push(Obligation {
                    id: format!(
                        "{}:{obligation_kind}:{}:clause:{clause_index}:path:{}",
                        function.name,
                        byte_offset,
                        obligations.len()
                    ),
                    expectation: ObligationExpectation::Prove,
                    assumptions: state.assumptions.clone(),
                    conclusion: conclusion.clone(),
                    path: path.to_owned(),
                    byte_offset,
                    line: source_location(source, byte_offset).0,
                    column: source_location(source, byte_offset).1,
                });
                // Like a modular call precondition, a loop invariant is checked and then
                // assumed. This prevents one failed invariant from manufacturing cascaded
                // body diagnostics while retaining the original failed obligation.
                state.assumptions.push(conclusion);
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn execute_symbolic_list_for(
    loop_statement: &ast::StmtFor,
    mut state: SymbolicState,
    iterable: Term,
    declared_sort: Option<&ScalarTypeComment>,
    function: &ast::StmtFunctionDef,
    lowerer: &ExpressionLowerer<'_>,
    return_sort: &Sort,
    path: &str,
    source: &str,
    obligations: &mut Vec<Obligation>,
    return_paths: &mut Vec<ReturnPath>,
    exceptional_paths: &mut Vec<ExceptionalPath>,
) -> Result<Vec<SymbolicState>, ContractFailure> {
    let ast::Expr::Name(iterable_name) = loop_statement.iter.as_ref() else {
        return failure(
            "frontend.python.contracts.symbolic-for-iterable-expression-unsupported",
            "symbolic List iteration requires one stable direct local-name iterable",
        );
    };
    let ast::Expr::Name(target) = loop_statement.target.as_ref() else {
        unreachable!("for target shape is checked before symbolic execution");
    };
    let invariant_count = loop_statement
        .body
        .iter()
        .take_while(|statement| contract_invariant(statement).is_some())
        .count();
    let invariant_statements = &loop_statement.body[..invariant_count];
    let loop_body = &loop_statement.body[invariant_count..];

    let aliases = state
        .environment
        .iter()
        .filter(|(_, value)| **value == iterable)
        .map(|(name, _)| name.clone())
        .collect::<BTreeSet<_>>();
    validate_symbolic_for_region(loop_body, &aliases, function)?;
    let mut modified = BTreeSet::new();
    collect_modified_names(loop_body, &mut modified);
    if let Some(alias) = modified.iter().find(|name| aliases.contains(*name)) {
        return failure(
            "frontend.python.contracts.symbolic-for-iterable-mutation-unsupported",
            format!(
                "symbolic loop in {:?} may rebind or mutate iterable alias {alias:?}",
                function.name
            ),
        );
    }
    if aliases.contains(target.id.as_str()) {
        return failure(
            "frontend.python.contracts.symbolic-for-target-aliases-iterable",
            format!(
                "symbolic loop target {:?} aliases iterable {:?}",
                target.id, iterable_name.id
            ),
        );
    }

    prove_for_invariants(
        invariant_statements,
        std::slice::from_mut(&mut state),
        function,
        lowerer,
        path,
        source,
        obligations,
        "invariant-establishment",
    )?;

    let SymbolicState {
        environment: mut head_environment,
        identities: mut head_identities,
        assumptions: retained_assumptions,
    } = state;
    for name in &modified {
        head_identities.remove(name);
        if name == target.id.as_str() {
            continue;
        }
        if let Some(previous) = head_environment.get(name) {
            let sort = previous.sort().map_err(type_failure)?;
            head_environment.insert(
                name.clone(),
                Term::Variable {
                    name: format!(
                        "{}::for-loop:{}::{name}",
                        function.name,
                        u32::from(loop_statement.range.start())
                    ),
                    sort,
                },
            );
        }
    }

    let mut invariant_terms = Vec::new();
    for invariant_statement in invariant_statements {
        let expression = contract_invariant(invariant_statement)
            .expect("invariant slice contains only invariant statements");
        for term in lowerer.lower_specification_clauses(
            expression,
            &head_environment,
            None,
            "for loop invariant",
        )? {
            ensure_boolean(&term, "for loop invariant")?;
            invariant_terms.push(term);
        }
    }
    let mut head_assumptions = retained_assumptions;
    head_assumptions.extend(invariant_terms);

    let index = Term::Variable {
        name: format!(
            "{}::for-index:{}",
            function.name,
            u32::from(loop_statement.range.start())
        ),
        sort: Sort::Int,
    };
    let (length, element) = match iterable.sort().map_err(type_failure)? {
        Sort::List(_) => (
            Term::ListLength {
                value: Box::new(iterable.clone()),
            },
            Term::ListGet {
                list: Box::new(iterable),
                index: Box::new(index.clone()),
            },
        ),
        Sort::VariadicTuple(_) => (
            Term::VariadicTupleLength {
                value: Box::new(iterable.clone()),
            },
            Term::VariadicTupleGet {
                tuple: Box::new(iterable),
                index: Box::new(index.clone()),
            },
        ),
        _ => unreachable!("symbolic sequence loop sort was checked by its caller"),
    };
    let domain = Term::And {
        values: vec![
            Term::GreaterEqual {
                left: Box::new(index.clone()),
                right: Box::new(Term::Int { value: 0 }),
            },
            Term::Less {
                left: Box::new(index.clone()),
                right: Box::new(length),
            },
        ],
    };
    let element = match declared_sort {
        Some(expected) => coerce_to_type_comment(element, expected, "for target type comment")?,
        None => element,
    };
    let mut preservation_environment = head_environment.clone();
    preservation_environment.insert(target.id.to_string(), element);
    let mut preservation_identities = head_identities.clone();
    preservation_identities.remove(target.id.as_str());
    let mut preservation_assumptions = head_assumptions.clone();
    preservation_assumptions.push(domain);
    let mut body_exceptions = Vec::new();
    let mut body_returns = Vec::new();
    let mut preserved_states = execute_statements(
        loop_body,
        vec![SymbolicState {
            environment: preservation_environment,
            identities: preservation_identities,
            assumptions: preservation_assumptions,
        }],
        function,
        lowerer,
        return_sort,
        path,
        source,
        obligations,
        &mut body_returns,
        &mut body_exceptions,
    )?;
    if !body_returns.is_empty() {
        return failure(
            "frontend.python.contracts.symbolic-for-abrupt-completion-unsupported",
            "return from a symbolic List loop body requires a quantified control-flow rule",
        );
    }
    if !body_exceptions.is_empty() {
        return failure(
            "frontend.python.contracts.symbolic-for-body-exception-unsupported",
            "a symbolic List loop body may produce an exceptional path that is not invariant-modeled",
        );
    }
    prove_for_invariants(
        invariant_statements,
        &mut preserved_states,
        function,
        lowerer,
        path,
        source,
        obligations,
        "invariant-preservation",
    )?;

    // A symbolic List may be empty, so Python does not guarantee that the target is bound at
    // natural exit. Removing it makes any post-loop target read fail closed.
    head_environment.remove(target.id.as_str());
    head_identities.remove(target.id.as_str());
    execute_statements(
        &loop_statement.orelse,
        vec![SymbolicState {
            environment: head_environment,
            identities: head_identities,
            assumptions: head_assumptions,
        }],
        function,
        lowerer,
        return_sort,
        path,
        source,
        obligations,
        return_paths,
        exceptional_paths,
    )
}

#[allow(clippy::too_many_arguments)]
fn execute_try(
    try_statement: &ast::StmtTry,
    incoming: Vec<SymbolicState>,
    function: &ast::StmtFunctionDef,
    lowerer: &ExpressionLowerer<'_>,
    return_sort: &Sort,
    path: &str,
    source: &str,
    obligations: &mut Vec<Obligation>,
    return_paths: &mut Vec<ReturnPath>,
    exceptional_paths: &mut Vec<ExceptionalPath>,
) -> Result<Vec<SymbolicState>, ContractFailure> {
    if !try_statement.finalbody.is_empty() {
        return failure(
            "frontend.python.contracts.try-finally-unsupported",
            "finally requires abrupt-completion precedence rules that are not yet in the scalar fragment",
        );
    }
    let mut local_exceptions = Vec::new();
    let normal = execute_statements(
        &try_statement.body,
        incoming,
        function,
        lowerer,
        return_sort,
        path,
        source,
        obligations,
        return_paths,
        &mut local_exceptions,
    )?;
    let mut outgoing = execute_statements(
        &try_statement.orelse,
        normal,
        function,
        lowerer,
        return_sort,
        path,
        source,
        obligations,
        return_paths,
        exceptional_paths,
    )?;
    for raised in local_exceptions {
        let mut selected_handler = None;
        for handler in &try_statement.handlers {
            let ast::ExceptHandler::ExceptHandler(handler) = handler;
            let catches = match handler.type_.as_deref() {
                None => true,
                Some(ast::Expr::Name(name)) => {
                    ensure_supported_exception_type(lowerer.exception_hierarchy, name.id.as_str())?;
                    lowerer
                        .exception_hierarchy
                        .matches(name.id.as_str(), &raised.exception_type)
                }
                Some(_) => {
                    return failure(
                        "frontend.python.contracts.exception-handler-type-unsupported",
                        "exception handlers require one direct built-in exception class",
                    );
                }
            };
            if catches {
                selected_handler = Some(handler);
                break;
            }
        }
        if let Some(handler) = selected_handler {
            let binding = handler.name.as_ref().map(ToString::to_string);
            let mut handler_state = raised.state;
            if let Some(binding) = &binding {
                handler_state.environment.insert(
                    binding.clone(),
                    Term::NominalReference {
                        name: format!(
                            "{}::handler:{}::raised:{}::{binding}",
                            function.name,
                            u32::from(handler.range.start()),
                            raised.byte_offset
                        ),
                        class: raised.exception_type.clone(),
                    },
                );
            }
            let return_start = return_paths.len();
            let exception_start = exceptional_paths.len();
            let mut handler_outgoing = execute_statements(
                &handler.body,
                vec![handler_state],
                function,
                lowerer,
                return_sort,
                path,
                source,
                obligations,
                return_paths,
                exceptional_paths,
            )?;
            if let Some(binding) = &binding {
                for state in &mut handler_outgoing {
                    state.environment.remove(binding);
                }
                for returned in &mut return_paths[return_start..] {
                    returned.state.environment.remove(binding);
                }
                for escaped in &mut exceptional_paths[exception_start..] {
                    escaped.state.environment.remove(binding);
                }
            }
            outgoing.extend(handler_outgoing);
        } else {
            exceptional_paths.push(raised);
        }
    }
    Ok(outgoing)
}

#[allow(clippy::too_many_arguments)]
fn apply_source_call_effects(
    state: &mut SymbolicState,
    effects: SourceCallEffects,
    function: &ast::StmtFunctionDef,
    path: &str,
    source: &str,
    byte_offset: u32,
    obligations: &mut Vec<Obligation>,
    exceptional_paths: &mut Vec<ExceptionalPath>,
) {
    let precondition_label = match effects.precondition_failure {
        CallPreconditionFailure::Assertion => "call-precondition",
        CallPreconditionFailure::InsufficientPermission => "call-permission-precondition",
    };
    for (index, conclusion) in effects.preconditions.into_iter().enumerate() {
        obligations.push(Obligation {
            id: format!(
                "{}:{precondition_label}:{byte_offset}:{index}:path:{}",
                function.name,
                obligations.len()
            ),
            expectation: ObligationExpectation::Prove,
            assumptions: state.assumptions.clone(),
            conclusion: conclusion.clone(),
            path: path.to_owned(),
            byte_offset,
            line: source_location(source, byte_offset).0,
            column: source_location(source, byte_offset).1,
        });
        // Nagini's call rule checks and then exhales the precondition. Assuming it afterward
        // avoids cascading diagnostics while preserving the failed obligation above.
        state.assumptions.push(conclusion);
    }
    for (exception_type, conditions) in effects.exceptional_postconditions {
        let mut exceptional_state = state.clone();
        exceptional_state.assumptions.extend(conditions);
        exceptional_paths.push(ExceptionalPath {
            state: exceptional_state,
            exception_type,
            byte_offset,
            application_precondition: false,
        });
    }
    // The callee's separately verified postconditions are the only facts imported into the
    // caller. Non-Unit results are fresh symbolic values, so implementation details cannot leak
    // across this modular call boundary.
    state.assumptions.extend(effects.postconditions);
}

#[allow(clippy::too_many_arguments)]
fn execute_while(
    loop_statement: &ast::StmtWhile,
    incoming: Vec<SymbolicState>,
    function: &ast::StmtFunctionDef,
    lowerer: &ExpressionLowerer<'_>,
    return_sort: &Sort,
    path: &str,
    source: &str,
    obligations: &mut Vec<Obligation>,
    return_paths: &mut Vec<ReturnPath>,
    exceptional_paths: &mut Vec<ExceptionalPath>,
) -> Result<Vec<SymbolicState>, ContractFailure> {
    let invariant_count = loop_statement
        .body
        .iter()
        .take_while(|statement| contract_invariant(statement).is_some())
        .count();
    if invariant_count == 0 {
        return failure(
            "frontend.python.contracts.loop-invariant-missing",
            format!(
                "while loop in {:?} requires at least one leading Invariant(...) contract",
                function.name
            ),
        );
    }
    let invariant_statements = &loop_statement.body[..invariant_count];
    let loop_body = &loop_statement.body[invariant_count..];
    let mut modified = std::collections::BTreeSet::new();
    collect_modified_names(loop_body, &mut modified);
    let mut outgoing = Vec::new();

    for (state_index, state) in incoming.into_iter().enumerate() {
        for invariant_statement in invariant_statements {
            let expression = contract_invariant(invariant_statement)
                .expect("leading invariant count established invariant statement");
            let byte_offset = statement_offset(invariant_statement);
            for (clause_index, conclusion) in lowerer
                .lower_specification_clauses(
                    expression,
                    &state.environment,
                    None,
                    "loop invariant",
                )?
                .into_iter()
                .enumerate()
            {
                ensure_boolean(&conclusion, "loop invariant")?;
                obligations.push(Obligation {
                    id: format!(
                        "{}:invariant-establishment:{}:clause:{clause_index}:path:{}",
                        function.name,
                        byte_offset,
                        obligations.len()
                    ),
                    expectation: ObligationExpectation::Prove,
                    assumptions: state.assumptions.clone(),
                    conclusion,
                    path: path.to_owned(),
                    byte_offset,
                    line: source_location(source, byte_offset).0,
                    column: source_location(source, byte_offset).1,
                });
            }
        }

        let SymbolicState {
            environment: mut head_environment,
            identities: mut head_identities,
            assumptions: retained_assumptions,
        } = state;
        for name in &modified {
            head_identities.remove(name);
            if let Some(previous) = head_environment.get(name) {
                let sort = previous.sort().map_err(type_failure)?;
                head_environment.insert(
                    name.clone(),
                    Term::Variable {
                        name: format!(
                            "{}::loop:{}:path:{state_index}::{name}",
                            function.name,
                            u32::from(loop_statement.range.start())
                        ),
                        sort,
                    },
                );
            }
        }
        let mut invariant_terms = Vec::new();
        for invariant_statement in invariant_statements {
            let expression = contract_invariant(invariant_statement)
                .expect("leading invariant count established invariant statement");
            let byte_offset = statement_offset(invariant_statement);
            for term in lowerer.lower_specification_clauses(
                expression,
                &head_environment,
                None,
                "loop invariant",
            )? {
                ensure_boolean(&term, "loop invariant")?;
                invariant_terms.push((term, byte_offset));
            }
        }
        let mut head_assumptions = retained_assumptions;
        head_assumptions.extend(invariant_terms.iter().map(|(term, _)| term.clone()));
        let mut prepared_heads = prepare_runtime_expression_states(
            &loop_statement.test,
            vec![SymbolicState {
                environment: head_environment,
                identities: head_identities,
                assumptions: head_assumptions,
            }],
            lowerer,
            exceptional_paths,
        )?;
        let prepared_head = prepared_heads
            .pop()
            .expect("one loop-head state produces one normal condition state");
        let condition = coerce_truthy(
            lowerer.lower(&loop_statement.test, &prepared_head.environment, None)?,
            "while condition",
        )?;

        let mut preservation = SymbolicState {
            environment: prepared_head.environment.clone(),
            identities: prepared_head.identities.clone(),
            assumptions: prepared_head.assumptions.clone(),
        };
        preservation.assumptions.push(condition.clone());
        let preserved_states = execute_statements(
            loop_body,
            vec![preservation],
            function,
            lowerer,
            return_sort,
            path,
            source,
            obligations,
            return_paths,
            exceptional_paths,
        )?;
        for preserved in preserved_states {
            for invariant_statement in invariant_statements {
                let expression = contract_invariant(invariant_statement)
                    .expect("leading invariant count established invariant statement");
                let byte_offset = statement_offset(invariant_statement);
                for (clause_index, conclusion) in lowerer
                    .lower_specification_clauses(
                        expression,
                        &preserved.environment,
                        None,
                        "loop invariant",
                    )?
                    .into_iter()
                    .enumerate()
                {
                    ensure_boolean(&conclusion, "preserved loop invariant")?;
                    obligations.push(Obligation {
                        id: format!(
                            "{}:invariant-preservation:{}:clause:{clause_index}:path:{}",
                            function.name,
                            byte_offset,
                            obligations.len()
                        ),
                        expectation: ObligationExpectation::Prove,
                        assumptions: preserved.assumptions.clone(),
                        conclusion,
                        path: path.to_owned(),
                        byte_offset,
                        line: source_location(source, byte_offset).0,
                        column: source_location(source, byte_offset).1,
                    });
                }
            }
        }

        let mut exit_state = SymbolicState {
            environment: prepared_head.environment,
            identities: prepared_head.identities,
            assumptions: prepared_head.assumptions,
        };
        exit_state.assumptions.push(Term::Not {
            value: Box::new(condition),
        });
        outgoing.extend(execute_statements(
            &loop_statement.orelse,
            vec![exit_state],
            function,
            lowerer,
            return_sort,
            path,
            source,
            obligations,
            return_paths,
            exceptional_paths,
        )?);
    }
    Ok(outgoing)
}

fn raised_exception_type(
    statement: &ast::StmtRaise,
    exception_hierarchy: &ExceptionHierarchy,
) -> Result<String, ContractFailure> {
    if statement.cause.is_some() {
        return failure(
            "frontend.python.contracts.raise-cause-unsupported",
            "exception chaining requires an explicit effect rule",
        );
    }
    let expression = statement.exc.as_deref().ok_or_else(|| ContractFailure {
        code: "frontend.python.contracts.bare-reraise-unsupported",
        message: "bare raise is valid only in a modeled exception handler".to_owned(),
    })?;
    let exception_type = match expression {
        ast::Expr::Name(name) => name.id.as_str(),
        ast::Expr::Call(call) if call.args.is_empty() && call.keywords.is_empty() => {
            let ast::Expr::Name(name) = call.func.as_ref() else {
                return failure(
                    "frontend.python.contracts.raise-expression-unsupported",
                    "raised exception constructor must be a direct class name",
                );
            };
            name.id.as_str()
        }
        _ => {
            return failure(
                "frontend.python.contracts.raise-expression-unsupported",
                "the scalar exception fragment supports a direct built-in exception class or zero-argument constructor",
            );
        }
    };
    ensure_supported_exception_type(exception_hierarchy, exception_type)?;
    Ok(exception_type.to_owned())
}

fn contract_invariant(statement: &ast::Stmt) -> Option<&ast::Expr> {
    let ast::Stmt::Expr(expression_statement) = statement else {
        return None;
    };
    let ast::Expr::Call(call) = expression_statement.value.as_ref() else {
        return None;
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return None;
    };
    if name.id.as_str() == "Invariant" && call.args.len() == 1 && call.keywords.is_empty() {
        Some(&call.args[0])
    } else {
        None
    }
}

fn collect_modified_names(
    statements: &[ast::Stmt],
    modified: &mut std::collections::BTreeSet<String>,
) {
    for statement in statements {
        match statement {
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    if let ast::Expr::Name(name) = target {
                        modified.insert(name.id.to_string());
                    }
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                if let ast::Expr::Name(name) = assignment.target.as_ref() {
                    modified.insert(name.id.to_string());
                }
            }
            ast::Stmt::AugAssign(assignment) => {
                if let ast::Expr::Name(name) = assignment.target.as_ref() {
                    modified.insert(name.id.to_string());
                }
            }
            ast::Stmt::If(branch) => {
                collect_modified_names(&branch.body, modified);
                collect_modified_names(&branch.orelse, modified);
            }
            ast::Stmt::While(nested) => {
                collect_modified_names(&nested.body, modified);
                collect_modified_names(&nested.orelse, modified);
            }
            ast::Stmt::For(nested) => {
                if let ast::Expr::Name(target) = nested.target.as_ref() {
                    modified.insert(target.id.to_string());
                }
                collect_modified_names(&nested.body, modified);
                collect_modified_names(&nested.orelse, modified);
            }
            ast::Stmt::Try(try_statement) => {
                collect_modified_names(&try_statement.body, modified);
                collect_modified_names(&try_statement.orelse, modified);
                collect_modified_names(&try_statement.finalbody, modified);
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    if let Some(name) = &handler.name {
                        modified.insert(name.to_string());
                    }
                    collect_modified_names(&handler.body, modified);
                }
            }
            _ => {}
        }
    }
}

fn validate_symbolic_for_region(
    statements: &[ast::Stmt],
    aliases: &BTreeSet<String>,
    function: &ast::StmtFunctionDef,
) -> Result<(), ContractFailure> {
    let mut called = BTreeSet::new();
    collect_called_names(statements, &mut called);
    if called.contains("Previous") {
        return failure(
            "frontend.python.contracts.symbolic-for-previous-unsupported",
            format!(
                "symbolic List loop in {:?} cannot use Previous(...) without a loop-history model",
                function.name
            ),
        );
    }
    for statement in statements {
        match statement {
            ast::Stmt::Break(_) | ast::Stmt::Continue(_) | ast::Stmt::Return(_) => {
                return failure(
                    "frontend.python.contracts.symbolic-for-abrupt-completion-unsupported",
                    format!(
                        "symbolic List loop in {:?} contains break, continue, or return",
                        function.name
                    ),
                );
            }
            ast::Stmt::Raise(_) | ast::Stmt::Try(_) => {
                return failure(
                    "frontend.python.contracts.symbolic-for-body-exception-unsupported",
                    format!(
                        "symbolic List loop in {:?} contains explicit exceptional control flow",
                        function.name
                    ),
                );
            }
            ast::Stmt::Assign(assignment) => {
                if assignment.targets.iter().any(|target| {
                    matches!(target, ast::Expr::Name(name) if aliases.contains(name.id.as_str()))
                }) || expression_carries_alias(&assignment.value, aliases)
                {
                    return symbolic_for_alias_escape(function);
                }
                reject_symbolic_for_alias_calls(&assignment.value, aliases, function)?;
            }
            ast::Stmt::AnnAssign(assignment) => {
                if matches!(assignment.target.as_ref(), ast::Expr::Name(name) if aliases.contains(name.id.as_str()))
                    || assignment
                        .value
                        .as_deref()
                        .is_some_and(|value| expression_carries_alias(value, aliases))
                {
                    return symbolic_for_alias_escape(function);
                }
                if let Some(value) = assignment.value.as_deref() {
                    reject_symbolic_for_alias_calls(value, aliases, function)?;
                }
            }
            ast::Stmt::AugAssign(assignment) => {
                if matches!(assignment.target.as_ref(), ast::Expr::Name(name) if aliases.contains(name.id.as_str()))
                {
                    return symbolic_for_alias_escape(function);
                }
                reject_symbolic_for_alias_calls(&assignment.value, aliases, function)?;
            }
            ast::Stmt::Assert(assertion) => {
                reject_symbolic_for_alias_calls(&assertion.test, aliases, function)?
            }
            ast::Stmt::Expr(expression) => {
                reject_symbolic_for_alias_calls(&expression.value, aliases, function)?
            }
            ast::Stmt::If(branch) => {
                reject_symbolic_for_alias_calls(&branch.test, aliases, function)?;
                validate_symbolic_for_region(&branch.body, aliases, function)?;
                validate_symbolic_for_region(&branch.orelse, aliases, function)?;
            }
            ast::Stmt::While(loop_statement) => {
                reject_symbolic_for_alias_calls(&loop_statement.test, aliases, function)?;
                validate_symbolic_for_region(&loop_statement.body, aliases, function)?;
                validate_symbolic_for_region(&loop_statement.orelse, aliases, function)?;
            }
            ast::Stmt::For(loop_statement) => {
                if matches!(loop_statement.target.as_ref(), ast::Expr::Name(name) if aliases.contains(name.id.as_str()))
                {
                    return symbolic_for_alias_escape(function);
                }
                reject_symbolic_for_alias_calls(&loop_statement.iter, aliases, function)?;
                validate_symbolic_for_region(&loop_statement.body, aliases, function)?;
                validate_symbolic_for_region(&loop_statement.orelse, aliases, function)?;
            }
            ast::Stmt::Pass(_) => {}
            _ => {}
        }
    }
    Ok(())
}

fn symbolic_for_alias_escape<T>(function: &ast::StmtFunctionDef) -> Result<T, ContractFailure> {
    failure(
        "frontend.python.contracts.symbolic-for-iterable-alias-escape",
        format!(
            "symbolic List loop in {:?} may expose, rebind, or mutate the iterated List through an alias",
            function.name
        ),
    )
}

fn expression_carries_alias(expression: &ast::Expr, aliases: &BTreeSet<String>) -> bool {
    match expression {
        ast::Expr::Name(name) => aliases.contains(name.id.as_str()),
        ast::Expr::IfExp(conditional) => {
            expression_carries_alias(&conditional.body, aliases)
                || expression_carries_alias(&conditional.orelse, aliases)
        }
        ast::Expr::BoolOp(operation) => operation
            .values
            .iter()
            .any(|value| expression_carries_alias(value, aliases)),
        ast::Expr::Tuple(tuple) => tuple
            .elts
            .iter()
            .any(|value| expression_carries_alias(value, aliases)),
        ast::Expr::List(list) => list
            .elts
            .iter()
            .any(|value| expression_carries_alias(value, aliases)),
        ast::Expr::Dict(dictionary) => dictionary
            .keys
            .iter()
            .flatten()
            .chain(dictionary.values.iter())
            .any(|value| expression_carries_alias(value, aliases)),
        _ => false,
    }
}

fn reject_symbolic_for_alias_calls(
    expression: &ast::Expr,
    aliases: &BTreeSet<String>,
    function: &ast::StmtFunctionDef,
) -> Result<(), ContractFailure> {
    match expression {
        ast::Expr::Call(call) => {
            let arguments_carry_alias = call
                .args
                .iter()
                .chain(call.keywords.iter().map(|keyword| &keyword.value))
                .any(|argument| expression_contains_alias(argument, aliases));
            let observation = matches!(
                call.func.as_ref(),
                ast::Expr::Name(name)
                    if matches!(name.id.as_str(), "Acc" | "Forall" | "len" | "list_pred" | "ToSeq")
            );
            if arguments_carry_alias && !observation {
                return symbolic_for_alias_escape(function);
            }
            if matches!(call.func.as_ref(), ast::Expr::Attribute(attribute) if expression_contains_alias(&attribute.value, aliases))
            {
                return symbolic_for_alias_escape(function);
            }
            reject_symbolic_for_alias_calls(&call.func, aliases, function)?;
            for argument in &call.args {
                reject_symbolic_for_alias_calls(argument, aliases, function)?;
            }
            for keyword in &call.keywords {
                reject_symbolic_for_alias_calls(&keyword.value, aliases, function)?;
            }
        }
        ast::Expr::BoolOp(operation) => {
            for value in &operation.values {
                reject_symbolic_for_alias_calls(value, aliases, function)?;
            }
        }
        ast::Expr::IfExp(conditional) => {
            reject_symbolic_for_alias_calls(&conditional.test, aliases, function)?;
            reject_symbolic_for_alias_calls(&conditional.body, aliases, function)?;
            reject_symbolic_for_alias_calls(&conditional.orelse, aliases, function)?;
        }
        ast::Expr::BinOp(operation) => {
            reject_symbolic_for_alias_calls(&operation.left, aliases, function)?;
            reject_symbolic_for_alias_calls(&operation.right, aliases, function)?;
        }
        ast::Expr::UnaryOp(operation) => {
            reject_symbolic_for_alias_calls(&operation.operand, aliases, function)?
        }
        ast::Expr::Compare(comparison) => {
            reject_symbolic_for_alias_calls(&comparison.left, aliases, function)?;
            for comparator in &comparison.comparators {
                reject_symbolic_for_alias_calls(comparator, aliases, function)?;
            }
        }
        ast::Expr::Tuple(tuple) => {
            for value in &tuple.elts {
                reject_symbolic_for_alias_calls(value, aliases, function)?;
            }
        }
        ast::Expr::List(list) => {
            for value in &list.elts {
                reject_symbolic_for_alias_calls(value, aliases, function)?;
            }
        }
        ast::Expr::Dict(dictionary) => {
            for value in dictionary.keys.iter().flatten() {
                reject_symbolic_for_alias_calls(value, aliases, function)?;
            }
            for value in &dictionary.values {
                reject_symbolic_for_alias_calls(value, aliases, function)?;
            }
        }
        ast::Expr::Subscript(subscript) => {
            reject_symbolic_for_alias_calls(&subscript.value, aliases, function)?;
            reject_symbolic_for_alias_calls(&subscript.slice, aliases, function)?;
        }
        ast::Expr::Attribute(attribute) => {
            reject_symbolic_for_alias_calls(&attribute.value, aliases, function)?
        }
        _ => {}
    }
    Ok(())
}

fn expression_contains_alias(expression: &ast::Expr, aliases: &BTreeSet<String>) -> bool {
    match expression {
        ast::Expr::Name(name) => aliases.contains(name.id.as_str()),
        ast::Expr::Call(call) => {
            expression_contains_alias(&call.func, aliases)
                || call
                    .args
                    .iter()
                    .chain(call.keywords.iter().map(|keyword| &keyword.value))
                    .any(|argument| expression_contains_alias(argument, aliases))
        }
        ast::Expr::BoolOp(operation) => operation
            .values
            .iter()
            .any(|value| expression_contains_alias(value, aliases)),
        ast::Expr::IfExp(conditional) => {
            expression_contains_alias(&conditional.test, aliases)
                || expression_contains_alias(&conditional.body, aliases)
                || expression_contains_alias(&conditional.orelse, aliases)
        }
        ast::Expr::BinOp(operation) => {
            expression_contains_alias(&operation.left, aliases)
                || expression_contains_alias(&operation.right, aliases)
        }
        ast::Expr::UnaryOp(operation) => expression_contains_alias(&operation.operand, aliases),
        ast::Expr::Compare(comparison) => {
            expression_contains_alias(&comparison.left, aliases)
                || comparison
                    .comparators
                    .iter()
                    .any(|value| expression_contains_alias(value, aliases))
        }
        ast::Expr::Tuple(tuple) => tuple
            .elts
            .iter()
            .any(|value| expression_contains_alias(value, aliases)),
        ast::Expr::List(list) => list
            .elts
            .iter()
            .any(|value| expression_contains_alias(value, aliases)),
        ast::Expr::Dict(dictionary) => dictionary
            .keys
            .iter()
            .flatten()
            .chain(dictionary.values.iter())
            .any(|value| expression_contains_alias(value, aliases)),
        ast::Expr::Subscript(subscript) => {
            expression_contains_alias(&subscript.value, aliases)
                || expression_contains_alias(&subscript.slice, aliases)
        }
        ast::Expr::Attribute(attribute) => expression_contains_alias(&attribute.value, aliases),
        _ => false,
    }
}

fn collect_called_names(statements: &[ast::Stmt], called: &mut std::collections::BTreeSet<String>) {
    for statement in statements {
        match statement {
            ast::Stmt::Assign(assignment) => {
                collect_called_names_expression(&assignment.value, called)
            }
            ast::Stmt::AnnAssign(assignment) => {
                if let Some(value) = assignment.value.as_deref() {
                    collect_called_names_expression(value, called);
                }
            }
            ast::Stmt::AugAssign(assignment) => {
                collect_called_names_expression(&assignment.value, called)
            }
            ast::Stmt::Assert(assertion) => {
                collect_called_names_expression(&assertion.test, called)
            }
            ast::Stmt::Expr(expression) => {
                collect_called_names_expression(&expression.value, called)
            }
            ast::Stmt::Raise(raise_statement) => {
                if let Some(exception) = raise_statement.exc.as_deref() {
                    collect_called_names_expression(exception, called);
                }
                if let Some(cause) = raise_statement.cause.as_deref() {
                    collect_called_names_expression(cause, called);
                }
            }
            ast::Stmt::If(branch) => {
                collect_called_names_expression(&branch.test, called);
                collect_called_names(&branch.body, called);
                collect_called_names(&branch.orelse, called);
            }
            ast::Stmt::While(loop_statement) => {
                collect_called_names_expression(&loop_statement.test, called);
                collect_called_names(&loop_statement.body, called);
                collect_called_names(&loop_statement.orelse, called);
            }
            ast::Stmt::For(loop_statement) => {
                collect_called_names_expression(&loop_statement.iter, called);
                collect_called_names(&loop_statement.body, called);
                collect_called_names(&loop_statement.orelse, called);
            }
            ast::Stmt::Try(try_statement) => {
                collect_called_names(&try_statement.body, called);
                collect_called_names(&try_statement.orelse, called);
                collect_called_names(&try_statement.finalbody, called);
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    collect_called_names(&handler.body, called);
                }
            }
            ast::Stmt::Return(return_statement) => {
                if let Some(value) = return_statement.value.as_deref() {
                    collect_called_names_expression(value, called);
                }
            }
            _ => {}
        }
    }
}

fn ensure_canonical_identity_constructor_bindings(
    expression: &ast::Expr,
    shadowed_bindings: &BTreeSet<String>,
) -> Result<(), ContractFailure> {
    let mut called = BTreeSet::new();
    collect_called_names_expression(expression, &mut called);
    if let Some(shadowed) = ["range", "str"]
        .into_iter()
        .find(|name| called.contains(*name) && shadowed_bindings.contains(*name))
    {
        return failure(
            "frontend.python.contracts.identity-constructor-shadowed",
            format!(
                "module expression calls {shadowed:?} after that canonical constructor was shadowed"
            ),
        );
    }
    Ok(())
}

fn reject_sorted_calls_in_repeated_regions(
    statements: &[ast::Stmt],
    function: &ast::StmtFunctionDef,
) -> Result<(), ContractFailure> {
    for statement in statements {
        match statement {
            ast::Stmt::While(loop_statement) => {
                let mut called = BTreeSet::new();
                collect_called_names_expression(&loop_statement.test, &mut called);
                collect_called_names(&loop_statement.body, &mut called);
                collect_called_names(&loop_statement.orelse, &mut called);
                if called.contains("sorted") {
                    return failure(
                        "frontend.python.contracts.sorted-repeated-call-unsupported",
                        format!(
                            "function {:?} calls sorted from a loop; repeated fresh collection results require invocation-indexed symbolic identities",
                            function.name
                        ),
                    );
                }
            }
            ast::Stmt::For(loop_statement) => {
                let mut called = BTreeSet::new();
                collect_called_names_expression(&loop_statement.iter, &mut called);
                collect_called_names(&loop_statement.body, &mut called);
                collect_called_names(&loop_statement.orelse, &mut called);
                if called.contains("sorted") {
                    return failure(
                        "frontend.python.contracts.sorted-repeated-call-unsupported",
                        format!(
                            "function {:?} calls sorted from a loop; repeated fresh collection results require invocation-indexed symbolic identities",
                            function.name
                        ),
                    );
                }
            }
            ast::Stmt::If(branch) => {
                reject_sorted_calls_in_repeated_regions(&branch.body, function)?;
                reject_sorted_calls_in_repeated_regions(&branch.orelse, function)?;
            }
            ast::Stmt::Try(try_statement) => {
                reject_sorted_calls_in_repeated_regions(&try_statement.body, function)?;
                reject_sorted_calls_in_repeated_regions(&try_statement.orelse, function)?;
                reject_sorted_calls_in_repeated_regions(&try_statement.finalbody, function)?;
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    reject_sorted_calls_in_repeated_regions(&handler.body, function)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn collect_called_names_expression(
    expression: &ast::Expr,
    called: &mut std::collections::BTreeSet<String>,
) {
    match expression {
        ast::Expr::Call(call) => {
            if let ast::Expr::Name(name) = call.func.as_ref() {
                called.insert(name.id.to_string());
            } else {
                collect_called_names_expression(&call.func, called);
            }
            for argument in &call.args {
                if let ast::Expr::Starred(starred) = argument {
                    collect_called_names_expression(&starred.value, called);
                } else {
                    collect_called_names_expression(argument, called);
                }
            }
            for keyword in &call.keywords {
                collect_called_names_expression(&keyword.value, called);
            }
        }
        ast::Expr::BoolOp(operation) => {
            for value in &operation.values {
                collect_called_names_expression(value, called);
            }
        }
        ast::Expr::IfExp(conditional) => {
            collect_called_names_expression(&conditional.test, called);
            collect_called_names_expression(&conditional.body, called);
            collect_called_names_expression(&conditional.orelse, called);
        }
        ast::Expr::BinOp(operation) => {
            collect_called_names_expression(&operation.left, called);
            collect_called_names_expression(&operation.right, called);
        }
        ast::Expr::UnaryOp(operation) => {
            collect_called_names_expression(&operation.operand, called)
        }
        ast::Expr::Compare(comparison) => {
            collect_called_names_expression(&comparison.left, called);
            for comparator in &comparison.comparators {
                collect_called_names_expression(comparator, called);
            }
        }
        ast::Expr::JoinedStr(joined) => {
            for value in &joined.values {
                collect_called_names_expression(value, called);
            }
        }
        ast::Expr::FormattedValue(formatted) => {
            collect_called_names_expression(&formatted.value, called);
            if let Some(specification) = formatted.format_spec.as_deref() {
                collect_called_names_expression(specification, called);
            }
        }
        ast::Expr::Tuple(tuple) => {
            for value in &tuple.elts {
                collect_called_names_expression(value, called);
            }
        }
        ast::Expr::List(list) => {
            for value in &list.elts {
                collect_called_names_expression(value, called);
            }
        }
        ast::Expr::Subscript(subscript) => {
            collect_called_names_expression(&subscript.value, called);
            collect_called_names_expression(&subscript.slice, called);
        }
        ast::Expr::Attribute(attribute) => {
            collect_called_names_expression(&attribute.value, called)
        }
        ast::Expr::Lambda(lambda) => collect_called_names_expression(&lambda.body, called),
        _ => {}
    }
}

fn validate_variadic_positional_uses(
    statements: &[ast::Stmt],
    parameter: &str,
) -> Result<(), ContractFailure> {
    let mut unsafe_use = false;
    visit_variadic_statements(statements, parameter, &mut unsafe_use);
    if unsafe_use {
        failure(
            "frontend.python.contracts.varargs-operation-unsupported",
            format!(
                "variadic positional capture {parameter:?} is currently restricted to len(...) and indexing so its tuple semantics cannot be confused with the homogeneous sequence proof representation"
            ),
        )
    } else {
        Ok(())
    }
}

fn visit_variadic_statements(statements: &[ast::Stmt], parameter: &str, unsafe_use: &mut bool) {
    for statement in statements {
        match statement {
            ast::Stmt::AnnAssign(assignment) => {
                if let Some(value) = assignment.value.as_deref() {
                    visit_variadic_expression(value, parameter, false, unsafe_use);
                }
            }
            ast::Stmt::Assign(assignment) => {
                visit_variadic_expression(&assignment.value, parameter, false, unsafe_use)
            }
            ast::Stmt::AugAssign(assignment) => {
                visit_variadic_expression(&assignment.target, parameter, false, unsafe_use);
                visit_variadic_expression(&assignment.value, parameter, false, unsafe_use);
            }
            ast::Stmt::Assert(assertion) => {
                visit_variadic_expression(&assertion.test, parameter, false, unsafe_use)
            }
            ast::Stmt::Expr(expression) => {
                visit_variadic_expression(&expression.value, parameter, false, unsafe_use)
            }
            ast::Stmt::Raise(raise) => {
                if let Some(exception) = raise.exc.as_deref() {
                    visit_variadic_expression(exception, parameter, false, unsafe_use);
                }
                if let Some(cause) = raise.cause.as_deref() {
                    visit_variadic_expression(cause, parameter, false, unsafe_use);
                }
            }
            ast::Stmt::If(branch) => {
                visit_variadic_expression(&branch.test, parameter, false, unsafe_use);
                visit_variadic_statements(&branch.body, parameter, unsafe_use);
                visit_variadic_statements(&branch.orelse, parameter, unsafe_use);
            }
            ast::Stmt::While(loop_statement) => {
                visit_variadic_expression(&loop_statement.test, parameter, false, unsafe_use);
                visit_variadic_statements(&loop_statement.body, parameter, unsafe_use);
                visit_variadic_statements(&loop_statement.orelse, parameter, unsafe_use);
            }
            ast::Stmt::For(loop_statement) => {
                visit_variadic_expression(&loop_statement.target, parameter, false, unsafe_use);
                visit_variadic_expression(&loop_statement.iter, parameter, false, unsafe_use);
                visit_variadic_statements(&loop_statement.body, parameter, unsafe_use);
                visit_variadic_statements(&loop_statement.orelse, parameter, unsafe_use);
            }
            ast::Stmt::Try(try_statement) => {
                visit_variadic_statements(&try_statement.body, parameter, unsafe_use);
                visit_variadic_statements(&try_statement.orelse, parameter, unsafe_use);
                visit_variadic_statements(&try_statement.finalbody, parameter, unsafe_use);
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    visit_variadic_statements(&handler.body, parameter, unsafe_use);
                }
            }
            ast::Stmt::Return(return_statement) => {
                if let Some(value) = return_statement.value.as_deref() {
                    visit_variadic_expression(value, parameter, false, unsafe_use);
                }
            }
            _ => {}
        }
    }
}

fn visit_variadic_expression(
    expression: &ast::Expr,
    parameter: &str,
    direct_use_allowed: bool,
    unsafe_use: &mut bool,
) {
    match expression {
        ast::Expr::Name(name) if name.id.as_str() == parameter => {
            *unsafe_use |= !direct_use_allowed;
        }
        ast::Expr::Call(call)
            if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "len")
                && call.keywords.is_empty()
                && matches!(call.args.as_slice(), [ast::Expr::Name(name)] if name.id.as_str() == parameter) =>
            {}
        ast::Expr::Call(call) => {
            visit_variadic_expression(&call.func, parameter, false, unsafe_use);
            for argument in &call.args {
                visit_variadic_expression(argument, parameter, false, unsafe_use);
            }
            for keyword in &call.keywords {
                visit_variadic_expression(&keyword.value, parameter, false, unsafe_use);
            }
        }
        ast::Expr::Subscript(subscript) => {
            visit_variadic_expression(&subscript.value, parameter, true, unsafe_use);
            visit_variadic_expression(&subscript.slice, parameter, false, unsafe_use);
        }
        ast::Expr::BoolOp(operation) => {
            for value in &operation.values {
                visit_variadic_expression(value, parameter, false, unsafe_use);
            }
        }
        ast::Expr::ListComp(comprehension) => {
            visit_variadic_expression(&comprehension.elt, parameter, false, unsafe_use);
            visit_variadic_generators(&comprehension.generators, parameter, unsafe_use);
        }
        ast::Expr::SetComp(comprehension) => {
            visit_variadic_expression(&comprehension.elt, parameter, false, unsafe_use);
            visit_variadic_generators(&comprehension.generators, parameter, unsafe_use);
        }
        ast::Expr::DictComp(comprehension) => {
            visit_variadic_expression(&comprehension.key, parameter, false, unsafe_use);
            visit_variadic_expression(&comprehension.value, parameter, false, unsafe_use);
            visit_variadic_generators(&comprehension.generators, parameter, unsafe_use);
        }
        ast::Expr::IfExp(conditional) => {
            visit_variadic_expression(&conditional.test, parameter, false, unsafe_use);
            visit_variadic_expression(&conditional.body, parameter, false, unsafe_use);
            visit_variadic_expression(&conditional.orelse, parameter, false, unsafe_use);
        }
        ast::Expr::BinOp(operation) => {
            visit_variadic_expression(&operation.left, parameter, false, unsafe_use);
            visit_variadic_expression(&operation.right, parameter, false, unsafe_use);
        }
        ast::Expr::UnaryOp(operation) => {
            visit_variadic_expression(&operation.operand, parameter, false, unsafe_use)
        }
        ast::Expr::Compare(comparison) => {
            visit_variadic_expression(&comparison.left, parameter, false, unsafe_use);
            for comparator in &comparison.comparators {
                visit_variadic_expression(comparator, parameter, false, unsafe_use);
            }
        }
        ast::Expr::JoinedStr(joined) => {
            for value in &joined.values {
                visit_variadic_expression(value, parameter, false, unsafe_use);
            }
        }
        ast::Expr::FormattedValue(formatted) => {
            visit_variadic_expression(&formatted.value, parameter, false, unsafe_use);
            if let Some(specification) = formatted.format_spec.as_deref() {
                visit_variadic_expression(specification, parameter, false, unsafe_use);
            }
        }
        ast::Expr::Tuple(tuple) => {
            for value in &tuple.elts {
                visit_variadic_expression(value, parameter, false, unsafe_use);
            }
        }
        ast::Expr::List(list) => {
            for value in &list.elts {
                visit_variadic_expression(value, parameter, false, unsafe_use);
            }
        }
        ast::Expr::Dict(dictionary) => {
            for key in dictionary.keys.iter().flatten() {
                visit_variadic_expression(key, parameter, false, unsafe_use);
            }
            for value in &dictionary.values {
                visit_variadic_expression(value, parameter, false, unsafe_use);
            }
        }
        ast::Expr::Attribute(attribute) => {
            visit_variadic_expression(&attribute.value, parameter, false, unsafe_use)
        }
        ast::Expr::Starred(starred) => {
            visit_variadic_expression(&starred.value, parameter, false, unsafe_use)
        }
        ast::Expr::Slice(slice) => {
            for bound in [&slice.lower, &slice.upper, &slice.step]
                .into_iter()
                .filter_map(|bound| bound.as_deref())
            {
                visit_variadic_expression(bound, parameter, false, unsafe_use);
            }
        }
        ast::Expr::Lambda(lambda) => {
            visit_variadic_expression(&lambda.body, parameter, false, unsafe_use)
        }
        _ => {}
    }
}

fn visit_variadic_generators(
    generators: &[ast::Comprehension],
    parameter: &str,
    unsafe_use: &mut bool,
) {
    for generator in generators {
        visit_variadic_expression(&generator.target, parameter, false, unsafe_use);
        visit_variadic_expression(&generator.iter, parameter, false, unsafe_use);
        for filter in &generator.ifs {
            visit_variadic_expression(filter, parameter, false, unsafe_use);
        }
    }
}

fn prepare_runtime_expression_states(
    expression: &ast::Expr,
    incoming: Vec<SymbolicState>,
    lowerer: &ExpressionLowerer<'_>,
    exceptional_paths: &mut Vec<ExceptionalPath>,
) -> Result<Vec<SymbolicState>, ContractFailure> {
    let mut outgoing = Vec::with_capacity(incoming.len());
    for mut state in incoming {
        let mut guards = Vec::new();
        collect_runtime_exception_guards(
            expression,
            lowerer,
            &state.environment,
            None,
            Term::Bool { value: true },
            &mut guards,
        )?;
        for guard in guards {
            let mut failed = state.clone();
            failed.assumptions.push(guard.evaluation_condition.clone());
            failed.assumptions.push(Term::Not {
                value: Box::new(guard.condition.clone()),
            });
            exceptional_paths.push(ExceptionalPath {
                state: failed,
                exception_type: guard.exception_type.to_owned(),
                byte_offset: guard.byte_offset,
                application_precondition: true,
            });
            state.assumptions.push(Term::Implies {
                left: Box::new(guard.evaluation_condition),
                right: Box::new(guard.condition),
            });
        }
        outgoing.push(state);
    }
    Ok(outgoing)
}

fn collect_runtime_exception_guards(
    expression: &ast::Expr,
    lowerer: &ExpressionLowerer<'_>,
    environment: &BTreeMap<String, Term>,
    result: Option<&Term>,
    evaluation_condition: Term,
    guards: &mut Vec<RuntimeExceptionGuard>,
) -> Result<(), ContractFailure> {
    match expression {
        ast::Expr::Subscript(subscript) => {
            collect_runtime_exception_guards(
                &subscript.value,
                lowerer,
                environment,
                result,
                evaluation_condition.clone(),
                guards,
            )?;
            collect_runtime_exception_guards(
                &subscript.slice,
                lowerer,
                environment,
                result,
                evaluation_condition.clone(),
                guards,
            )?;
            if matches!(subscript.slice.as_ref(), ast::Expr::Slice(_)) {
                return Ok(());
            }
            let collection = lowerer.lower(&subscript.value, environment, result)?;
            if matches!(
                collection.sort().map_err(type_failure)?,
                Sort::List(_) | Sort::Bytes | Sort::Range | Sort::Tuple(_) | Sort::VariadicTuple(_)
            ) {
                let index = coerce_python_int(
                    lowerer.lower(&subscript.slice, environment, result)?,
                    "sequence index",
                )?;
                guards.push(RuntimeExceptionGuard {
                    condition: sequence_index_guard(collection, index)?,
                    evaluation_condition,
                    exception_type: "IndexError",
                    byte_offset: subscript.range.start().into(),
                });
            } else {
                match collection.sort().map_err(type_failure)? {
                    Sort::Dict(key_sort, _) => {
                        let key = coerce_to_sort(
                            lowerer.lower(&subscript.slice, environment, result)?,
                            &key_sort,
                            "dictionary lookup key",
                        )?;
                        guards.push(RuntimeExceptionGuard {
                            condition: Term::DictContains {
                                dict: Box::new(collection),
                                key: Box::new(key),
                            },
                            evaluation_condition,
                            exception_type: "KeyError",
                            byte_offset: subscript.range.start().into(),
                        });
                    }
                    Sort::FiniteDict(key_sort, _) => {
                        let key = coerce_to_sort(
                            lowerer.lower(&subscript.slice, environment, result)?,
                            &key_sort,
                            "dictionary lookup key",
                        )?;
                        let Term::FiniteDict { entries, .. } = collection else {
                            unreachable!("finite dictionary sort came from another term")
                        };
                        guards.push(RuntimeExceptionGuard {
                            condition: finite_dict_contains(&entries, &key),
                            evaluation_condition,
                            exception_type: "KeyError",
                            byte_offset: subscript.range.start().into(),
                        });
                    }
                    _ => {}
                }
            }
        }
        ast::Expr::BoolOp(operation) => {
            let mut operand_condition = evaluation_condition;
            for value in &operation.values {
                collect_runtime_exception_guards(
                    value,
                    lowerer,
                    environment,
                    result,
                    operand_condition.clone(),
                    guards,
                )?;
                let truthy = coerce_truthy(
                    lowerer.lower(value, environment, result)?,
                    "short-circuit operand",
                )?;
                let continues = match operation.op {
                    ast::BoolOp::And => truthy,
                    ast::BoolOp::Or => Term::Not {
                        value: Box::new(truthy),
                    },
                };
                operand_condition = Term::And {
                    values: vec![operand_condition, continues],
                };
            }
        }
        ast::Expr::IfExp(conditional) => {
            collect_runtime_exception_guards(
                &conditional.test,
                lowerer,
                environment,
                result,
                evaluation_condition.clone(),
                guards,
            )?;
            let condition = coerce_truthy(
                lowerer.lower(&conditional.test, environment, result)?,
                "conditional expression",
            )?;
            collect_runtime_exception_guards(
                &conditional.body,
                lowerer,
                environment,
                result,
                Term::And {
                    values: vec![evaluation_condition.clone(), condition.clone()],
                },
                guards,
            )?;
            collect_runtime_exception_guards(
                &conditional.orelse,
                lowerer,
                environment,
                result,
                Term::And {
                    values: vec![
                        evaluation_condition,
                        Term::Not {
                            value: Box::new(condition),
                        },
                    ],
                },
                guards,
            )?;
        }
        ast::Expr::BinOp(operation) => {
            collect_runtime_exception_guards(
                &operation.left,
                lowerer,
                environment,
                result,
                evaluation_condition.clone(),
                guards,
            )?;
            collect_runtime_exception_guards(
                &operation.right,
                lowerer,
                environment,
                result,
                evaluation_condition,
                guards,
            )?;
        }
        ast::Expr::UnaryOp(operation) => collect_runtime_exception_guards(
            &operation.operand,
            lowerer,
            environment,
            result,
            evaluation_condition,
            guards,
        )?,
        ast::Expr::Compare(comparison) => {
            collect_runtime_exception_guards(
                &comparison.left,
                lowerer,
                environment,
                result,
                evaluation_condition.clone(),
                guards,
            )?;
            let mut left = comparison.left.as_ref();
            let mut comparator_condition = evaluation_condition;
            for (position, (operator, comparator)) in comparison
                .ops
                .iter()
                .zip(&comparison.comparators)
                .enumerate()
            {
                collect_runtime_exception_guards(
                    comparator,
                    lowerer,
                    environment,
                    result,
                    comparator_condition.clone(),
                    guards,
                )?;
                if position + 1 < comparison.comparators.len() {
                    let relation = lowerer.lower_comparison_pair(
                        operator,
                        lowerer.lower(left, environment, result)?,
                        lowerer.lower(comparator, environment, result)?,
                        expression,
                    )?;
                    comparator_condition = Term::And {
                        values: vec![comparator_condition, relation],
                    };
                }
                left = comparator;
            }
        }
        ast::Expr::Call(call) => {
            if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "ResultT")
                && call.args.len() == 1
                && call.keywords.is_empty()
                && annotation_sort(call.args.first()).is_ok()
            {
                return Ok(());
            }
            if let Some((parameter, predicate, triggers)) = typed_integer_forall(call) {
                let ast::Expr::Call(implies) = predicate else {
                    return Ok(());
                };
                let binder = format!(
                    "{}::forall::{}::{parameter}",
                    lowerer.call_stack.join("::"),
                    u32::from(call.range.start())
                );
                let mut nested_environment = environment.clone();
                nested_environment.insert(
                    parameter.to_owned(),
                    Term::Variable {
                        name: binder,
                        sort: Sort::Int,
                    },
                );
                collect_runtime_exception_guards(
                    &implies.args[0],
                    lowerer,
                    &nested_environment,
                    result,
                    evaluation_condition.clone(),
                    guards,
                )?;
                let guard = lowerer.lower(&implies.args[0], &nested_environment, result)?;
                ensure_boolean(&guard, "Forall index guard")?;
                let quantified_evaluation = Term::And {
                    values: vec![evaluation_condition, guard],
                };
                collect_runtime_exception_guards(
                    &implies.args[1],
                    lowerer,
                    &nested_environment,
                    result,
                    quantified_evaluation.clone(),
                    guards,
                )?;
                for trigger in triggers {
                    collect_runtime_exception_guards(
                        trigger,
                        lowerer,
                        &nested_environment,
                        result,
                        quantified_evaluation.clone(),
                        guards,
                    )?;
                }
                return Ok(());
            }
            if looks_like_typed_integer_forall(call) {
                return Ok(());
            }
            if is_zero_step_range_call(call) {
                guards.push(RuntimeExceptionGuard {
                    condition: Term::Bool { value: false },
                    evaluation_condition: evaluation_condition.clone(),
                    exception_type: "ValueError",
                    byte_offset: call.range.start().into(),
                });
            }
            if let Some((collection, parameter, predicate)) = finite_literal_forall(call) {
                collect_runtime_exception_guards(
                    collection,
                    lowerer,
                    environment,
                    result,
                    evaluation_condition.clone(),
                    guards,
                )?;
                let values = lower_to_sequence(lowerer.lower(collection, environment, result)?)
                    .map_err(|_| ContractFailure {
                        code: "frontend.python.contracts.forall-symbolic-collection-unsupported",
                        message:
                            "Forall currently requires a statically known homogeneous list literal"
                                .to_owned(),
                    })?;
                let Term::List { values, .. } = values else {
                    return failure(
                        "frontend.python.contracts.forall-symbolic-collection-unsupported",
                        "Forall currently requires a statically known homogeneous list literal",
                    );
                };
                for value in values {
                    let mut nested_environment = environment.clone();
                    nested_environment.insert(parameter.to_owned(), value);
                    collect_runtime_exception_guards(
                        predicate,
                        lowerer,
                        &nested_environment,
                        result,
                        evaluation_condition.clone(),
                        guards,
                    )?;
                }
            } else {
                if let ast::Expr::Attribute(attribute) = call.func.as_ref() {
                    collect_runtime_exception_guards(
                        &attribute.value,
                        lowerer,
                        environment,
                        result,
                        evaluation_condition.clone(),
                        guards,
                    )?;
                }
                for argument in &call.args {
                    let argument = match argument {
                        ast::Expr::Starred(starred) => starred.value.as_ref(),
                        argument => argument,
                    };
                    collect_runtime_exception_guards(
                        argument,
                        lowerer,
                        environment,
                        result,
                        evaluation_condition.clone(),
                        guards,
                    )?;
                }
                for keyword in &call.keywords {
                    collect_runtime_exception_guards(
                        &keyword.value,
                        lowerer,
                        environment,
                        result,
                        evaluation_condition.clone(),
                        guards,
                    )?;
                }
            }
        }
        ast::Expr::JoinedStr(joined) => {
            for value in &joined.values {
                collect_runtime_exception_guards(
                    value,
                    lowerer,
                    environment,
                    result,
                    evaluation_condition.clone(),
                    guards,
                )?;
            }
        }
        ast::Expr::FormattedValue(formatted) => {
            collect_runtime_exception_guards(
                &formatted.value,
                lowerer,
                environment,
                result,
                evaluation_condition.clone(),
                guards,
            )?;
            if let Some(specification) = formatted.format_spec.as_deref() {
                collect_runtime_exception_guards(
                    specification,
                    lowerer,
                    environment,
                    result,
                    evaluation_condition,
                    guards,
                )?;
            }
        }
        ast::Expr::Tuple(tuple) => {
            for value in &tuple.elts {
                collect_runtime_exception_guards(
                    value,
                    lowerer,
                    environment,
                    result,
                    evaluation_condition.clone(),
                    guards,
                )?;
            }
        }
        ast::Expr::List(list) => {
            for value in &list.elts {
                collect_runtime_exception_guards(
                    value,
                    lowerer,
                    environment,
                    result,
                    evaluation_condition.clone(),
                    guards,
                )?;
            }
        }
        ast::Expr::Dict(dictionary) => {
            for key in dictionary.keys.iter().filter_map(Option::as_ref) {
                collect_runtime_exception_guards(
                    key,
                    lowerer,
                    environment,
                    result,
                    evaluation_condition.clone(),
                    guards,
                )?;
            }
            for value in &dictionary.values {
                collect_runtime_exception_guards(
                    value,
                    lowerer,
                    environment,
                    result,
                    evaluation_condition.clone(),
                    guards,
                )?;
            }
        }
        ast::Expr::Lambda(lambda) => collect_runtime_exception_guards(
            &lambda.body,
            lowerer,
            environment,
            result,
            evaluation_condition,
            guards,
        )?,
        _ => {}
    }
    Ok(())
}

fn sequence_index_guard(sequence: Term, index: Term) -> Result<Term, ContractFailure> {
    let length = sequence_length(&sequence)?;
    Ok(Term::And {
        values: vec![
            Term::GreaterEqual {
                left: Box::new(index.clone()),
                right: Box::new(Term::Negate {
                    value: Box::new(length.clone()),
                }),
            },
            Term::Less {
                left: Box::new(index),
                right: Box::new(length),
            },
        ],
    })
}

fn list_index_value(list: Term, index: Term) -> Term {
    if let Term::List {
        values,
        element_sort: _,
    } = &list
        && let Some(raw_index) = static_python_int_value(&index)
        && let Ok(length) = i64::try_from(values.len())
    {
        let length = i128::from(length);
        let raw_index = i128::from(raw_index);
        let normalized = if raw_index < 0 {
            length.checked_add(raw_index)
        } else {
            Some(raw_index)
        };
        if let Some(position) = normalized
            .filter(|position| *position >= 0 && *position < length)
            .and_then(|position| usize::try_from(position).ok())
        {
            return values[position].clone();
        }
    }
    let length = Term::ListLength {
        value: Box::new(list.clone()),
    };
    let normalized = Term::IfThenElse {
        condition: Box::new(Term::Less {
            left: Box::new(index.clone()),
            right: Box::new(Term::Int { value: 0 }),
        }),
        then_value: Box::new(Term::Add {
            left: Box::new(length),
            right: Box::new(index.clone()),
        }),
        else_value: Box::new(index),
    };
    Term::ListGet {
        list: Box::new(list),
        index: Box::new(normalized),
    }
}

fn variadic_tuple_index_value(tuple: Term, index: Term) -> Term {
    if let Term::VariadicTuple { values, .. } = &tuple
        && let Some(raw_index) = static_python_int_value(&index)
        && let Ok(length) = i64::try_from(values.len())
    {
        let length = i128::from(length);
        let raw_index = i128::from(raw_index);
        let normalized = if raw_index < 0 {
            length.checked_add(raw_index)
        } else {
            Some(raw_index)
        };
        if let Some(position) = normalized
            .filter(|position| *position >= 0 && *position < length)
            .and_then(|position| usize::try_from(position).ok())
        {
            return values[position].clone();
        }
    }
    let length = Term::VariadicTupleLength {
        value: Box::new(tuple.clone()),
    };
    let normalized = Term::IfThenElse {
        condition: Box::new(Term::Less {
            left: Box::new(index.clone()),
            right: Box::new(Term::Int { value: 0 }),
        }),
        then_value: Box::new(Term::Add {
            left: Box::new(length),
            right: Box::new(index.clone()),
        }),
        else_value: Box::new(index),
    };
    Term::VariadicTupleGet {
        tuple: Box::new(tuple),
        index: Box::new(normalized),
    }
}

fn dynamic_tuple_index_value(
    tuple: Term,
    elements: &[Sort],
    index: Term,
) -> Result<Term, ContractFailure> {
    let first_sort = elements.first().ok_or_else(|| ContractFailure {
        code: "frontend.python.contracts.tuple-index-dynamic-empty",
        message: "a dynamically indexed empty tuple has no result type".to_owned(),
    })?;
    let result_sort = if elements.iter().all(|element| element == first_sort) {
        first_sort.clone()
    } else if elements
        .iter()
        .all(|element| matches!(element, Sort::Bool | Sort::Int))
    {
        Sort::Int
    } else {
        return failure(
            "frontend.python.contracts.tuple-index-dynamic-heterogeneous",
            format!("dynamic tuple indexing requires one common result sort, found {elements:?}"),
        );
    };
    let length = i64::try_from(elements.len()).map_err(|_| ContractFailure {
        code: "frontend.python.contracts.tuple-length-overflow",
        message: "fixed tuple length exceeds the current i64 frontend".to_owned(),
    })?;
    let normalized = Term::IfThenElse {
        condition: Box::new(Term::Less {
            left: Box::new(index.clone()),
            right: Box::new(Term::Int { value: 0 }),
        }),
        then_value: Box::new(Term::Add {
            left: Box::new(Term::Int { value: length }),
            right: Box::new(index.clone()),
        }),
        else_value: Box::new(index),
    };
    let values = elements
        .iter()
        .enumerate()
        .map(|(position, _)| {
            coerce_to_sort(
                Term::TupleGet {
                    tuple: Box::new(tuple.clone()),
                    index: position,
                },
                &result_sort,
                "dynamic tuple element",
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut selected = values.first().expect("nonempty tuple was checked").clone();
    for (position, value) in values.into_iter().enumerate().rev() {
        selected = Term::IfThenElse {
            condition: Box::new(Term::Equal {
                left: Box::new(normalized.clone()),
                right: Box::new(Term::Int {
                    value: i64::try_from(position).expect("tuple length fits i64"),
                }),
            }),
            then_value: Box::new(value),
            else_value: Box::new(selected),
        };
    }
    selected.sort().map_err(type_failure)?;
    Ok(selected)
}

fn bytes_index_value(bytes: Term, index: Term) -> Term {
    let length = Term::BytesLength {
        value: Box::new(bytes.clone()),
    };
    let normalized = Term::IfThenElse {
        condition: Box::new(Term::Less {
            left: Box::new(index.clone()),
            right: Box::new(Term::Int { value: 0 }),
        }),
        then_value: Box::new(Term::Add {
            left: Box::new(length),
            right: Box::new(index.clone()),
        }),
        else_value: Box::new(index),
    };
    Term::BytesGet {
        bytes: Box::new(bytes),
        index: Box::new(normalized),
    }
}

fn sequence_length(sequence: &Term) -> Result<Term, ContractFailure> {
    if let Term::ListComprehension {
        source,
        filter: None,
        ..
    } = sequence
    {
        return sequence_length(source);
    }
    match sequence.sort().map_err(type_failure)? {
        Sort::List(_) => Ok(Term::ListLength {
            value: Box::new(sequence.clone()),
        }),
        Sort::Bytes => Ok(Term::BytesLength {
            value: Box::new(sequence.clone()),
        }),
        Sort::Range => match sequence {
            Term::Range { values } => Ok(Term::Int {
                value: i64::try_from(values.len()).map_err(|_| ContractFailure {
                    code: "frontend.python.contracts.sequence-length-overflow",
                    message: "range length exceeds the current i64 frontend".to_owned(),
                })?,
            }),
            _ => failure(
                "frontend.python.contracts.sequence-value-symbolic-unsupported",
                "range length currently requires a statically known value",
            ),
        },
        Sort::Tuple(elements) => Ok(Term::Int {
            value: i64::try_from(elements.len()).map_err(|_| ContractFailure {
                code: "frontend.python.contracts.tuple-length-overflow",
                message: "fixed tuple length exceeds the current i64 frontend".to_owned(),
            })?,
        }),
        Sort::VariadicTuple(_) => Ok(Term::VariadicTupleLength {
            value: Box::new(sequence.clone()),
        }),
        _ => failure(
            "frontend.python.contracts.sequence-value-symbolic-unsupported",
            "sequence length requires a fixed tuple, list, bytes, or statically known range value",
        ),
    }
}

fn instantiate_frontend_bound_term(
    term: &Term,
    binder: &str,
    replacement: &Term,
) -> Result<Term, ContractFailure> {
    fn unary(term: &Term, binder: &str, replacement: &Term) -> Result<Box<Term>, ContractFailure> {
        instantiate_frontend_bound_term(term, binder, replacement).map(Box::new)
    }
    fn binary(
        left: &Term,
        right: &Term,
        binder: &str,
        replacement: &Term,
    ) -> Result<(Box<Term>, Box<Term>), ContractFailure> {
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
        Term::And { values } => Term::And {
            values: values
                .iter()
                .map(|value| instantiate_frontend_bound_term(value, binder, replacement))
                .collect::<Result<_, _>>()?,
        },
        Term::Or { values } => Term::Or {
            values: values
                .iter()
                .map(|value| instantiate_frontend_bound_term(value, binder, replacement))
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
            return failure(
                "frontend.python.contracts.comprehension-term-escaped",
                "an unsupported term escaped the pure comprehension boundary",
            );
        }
    })
}

fn contract_assertion(expression: &ast::Expr) -> Option<&ast::Expr> {
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return None;
    };
    if name.id.as_str() == "Assert" && call.args.len() == 1 && call.keywords.is_empty() {
        Some(&call.args[0])
    } else {
        None
    }
}

fn contract_refutation(expression: &ast::Expr) -> Option<&ast::Expr> {
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return None;
    };
    if name.id.as_str() == "Refute" && call.args.len() == 1 && call.keywords.is_empty() {
        Some(&call.args[0])
    } else {
        None
    }
}

fn contract_requires(statement: &ast::Stmt) -> Option<&ast::Expr> {
    let ast::Stmt::Expr(expression_statement) = statement else {
        return None;
    };
    let ast::Expr::Call(call) = expression_statement.value.as_ref() else {
        return None;
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return None;
    };
    if name.id.as_str() != "Requires" || call.args.len() != 1 || !call.keywords.is_empty() {
        return None;
    }
    Some(&call.args[0])
}

fn contract_decreases(statement: &ast::Stmt) -> Result<bool, ContractFailure> {
    let ast::Stmt::Expr(expression_statement) = statement else {
        return Ok(false);
    };
    let ast::Expr::Call(call) = expression_statement.value.as_ref() else {
        return Ok(false);
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return Ok(false);
    };
    if name.id.as_str() != "Decreases" {
        return Ok(false);
    }
    if !call.keywords.is_empty()
        || call.args.len() != 1
        || constant_tuple_index(&call.args[0]).is_none_or(|value| value < 0)
    {
        return failure(
            "frontend.python.contracts.decreases-unsupported",
            "the nonrecursive scalar fragment accepts only a nonnegative integer-literal Decreases measure",
        );
    }
    Ok(true)
}

fn contract_ensures(
    statement: &ast::Stmt,
    return_sort: &Sort,
) -> Result<Option<ContractPostcondition>, ContractFailure> {
    let ast::Stmt::Expr(expression_statement) = statement else {
        return Ok(None);
    };
    let ast::Expr::Call(call) = expression_statement.value.as_ref() else {
        return Ok(None);
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return Ok(None);
    };
    if name.id.as_str() != "Ensures" {
        return Ok(None);
    }
    if !call.keywords.is_empty() || !matches!(call.args.len(), 1 | 2) {
        return failure(
            "frontend.python.contracts.ensures-arguments",
            "Ensures requires either one boolean expression or a result type and one-argument lambda",
        );
    }
    if call.args.len() == 1 {
        return Ok(Some(ContractPostcondition {
            expression: call.args[0].clone(),
            result_binder: None,
        }));
    }
    let declared_sort = annotation_sort(call.args.first())?;
    if &declared_sort != return_sort {
        return failure(
            "frontend.python.contracts.postcondition-lambda-result-type",
            format!(
                "typed Ensures declares result sort {declared_sort:?}, but the function returns {return_sort:?}"
            ),
        );
    }
    let ast::Expr::Lambda(lambda) = &call.args[1] else {
        return failure(
            "frontend.python.contracts.postcondition-lambda-required",
            "two-argument Ensures requires a one-argument lambda as its second argument",
        );
    };
    if !lambda.args.posonlyargs.is_empty()
        || lambda.args.args.len() != 1
        || lambda.args.vararg.is_some()
        || !lambda.args.kwonlyargs.is_empty()
        || lambda.args.kwarg.is_some()
        || lambda.args.args[0].default.is_some()
        || lambda.args.args[0].def.annotation.is_some()
    {
        return failure(
            "frontend.python.contracts.postcondition-lambda-signature",
            "typed Ensures requires exactly one unannotated positional lambda parameter",
        );
    }
    Ok(Some(ContractPostcondition {
        expression: lambda.body.as_ref().clone(),
        result_binder: Some(lambda.args.args[0].def.arg.to_string()),
    }))
}

fn contract_exsures<'a>(
    statement: &'a ast::Stmt,
    exception_hierarchy: &ExceptionHierarchy,
) -> Result<Option<(String, &'a ast::Expr)>, ContractFailure> {
    let ast::Stmt::Expr(expression_statement) = statement else {
        return Ok(None);
    };
    let ast::Expr::Call(call) = expression_statement.value.as_ref() else {
        return Ok(None);
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return Ok(None);
    };
    if name.id.as_str() != "Exsures" {
        return Ok(None);
    }
    if call.args.len() != 2 || !call.keywords.is_empty() {
        return failure(
            "frontend.python.contracts.exsures-arguments",
            "Exsures requires exactly an exception type and a boolean postcondition",
        );
    }
    let ast::Expr::Name(exception_type) = &call.args[0] else {
        return failure(
            "frontend.python.contracts.exsures-type-unsupported",
            "the scalar exception fragment requires a direct exception class name",
        );
    };
    ensure_supported_exception_type(exception_hierarchy, exception_type.id.as_str())?;
    Ok(Some((
        exception_type.id.to_string(),
        call.args.get(1).expect("Exsures arity checked"),
    )))
}

fn ensure_supported_exception_type(
    exception_hierarchy: &ExceptionHierarchy,
    exception_type: &str,
) -> Result<(), ContractFailure> {
    if exception_hierarchy.supports(exception_type) {
        Ok(())
    } else {
        failure(
            "frontend.python.contracts.exception-type-unresolved",
            format!(
                "exception type {exception_type:?} has no source-resolved hierarchy in the scalar fragment"
            ),
        )
    }
}

impl ExpressionLowerer<'_> {
    fn lower_postcondition_clauses(
        &self,
        postcondition: &ContractPostcondition,
        environment: &BTreeMap<String, Term>,
        result: &Term,
        context: &str,
    ) -> Result<Vec<Term>, ContractFailure> {
        if let Some(binder) = &postcondition.result_binder {
            let mut bound_environment = environment.clone();
            bound_environment.insert(binder.clone(), result.clone());
            self.lower_specification_clauses(
                &postcondition.expression,
                &bound_environment,
                Some(result),
                context,
            )
        } else {
            self.lower_specification_clauses(
                &postcondition.expression,
                environment,
                Some(result),
                context,
            )
        }
    }

    fn lower_specification_clauses(
        &self,
        expression: &ast::Expr,
        environment: &BTreeMap<String, Term>,
        result: Option<&Term>,
        _context: &str,
    ) -> Result<Vec<Term>, ContractFailure> {
        let mut guards = Vec::new();
        collect_runtime_exception_guards(
            expression,
            self,
            environment,
            result,
            Term::Bool { value: true },
            &mut guards,
        )?;
        let mut clauses = guards
            .into_iter()
            .map(|guard| Term::Implies {
                left: Box::new(guard.evaluation_condition),
                right: Box::new(guard.condition),
            })
            .collect::<Vec<_>>();
        clauses.push(self.lower(expression, environment, result)?);
        Ok(clauses)
    }

    fn lower_spec(
        &self,
        expression: &ast::Expr,
        environment: &BTreeMap<String, Term>,
        result: Option<&Term>,
        context: &str,
    ) -> Result<Term, ContractFailure> {
        if typed_integer_forall_expression_is_guarded(expression) {
            return failure(
                "frontend.python.contracts.specification-safety-bypass",
                format!(
                    "{context} contains guarded quantified indexing but was not lowered through the specification-safety channel"
                ),
            );
        }
        self.lower_guarded_spec(expression, environment, result, context)
    }

    fn lower_guarded_spec(
        &self,
        expression: &ast::Expr,
        environment: &BTreeMap<String, Term>,
        result: Option<&Term>,
        context: &str,
    ) -> Result<Term, ContractFailure> {
        let guarded_quantifier = matches!(expression, ast::Expr::Call(call)
            if typed_integer_forall_is_guarded(call));
        if contains_zero_step_range(expression)
            || (contains_dynamic_subscript(expression) && !guarded_quantifier)
        {
            return failure(
                "frontend.python.contracts.partial-operation-in-spec",
                format!(
                    "{context} contains a partial runtime operation; partial runtime operations require an explicit executable path"
                ),
            );
        }
        let term = self.lower(expression, environment, result)?;
        if term_contains_list_get(&term) && !guarded_quantifier {
            return failure(
                "frontend.python.contracts.partial-operation-in-spec",
                format!(
                    "{context} contains Python sequence indexing; partial runtime operations require an explicit executable path"
                ),
            );
        }
        Ok(term)
    }

    fn lower_expected(
        &self,
        expression: &ast::Expr,
        environment: &BTreeMap<String, Term>,
        result: Option<&Term>,
        expected: &Sort,
        context: &str,
    ) -> Result<Term, ContractFailure> {
        if let (ast::Expr::List(list), Sort::List(element_sort)) = (expression, expected) {
            let values = list
                .elts
                .iter()
                .map(|element| {
                    self.lower(element, environment, result)
                        .and_then(|value| coerce_to_sort(value, element_sort, "list element"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let term = Term::List {
                element_sort: (**element_sort).clone(),
                values,
            };
            term.sort().map_err(type_failure)?;
            return Ok(term);
        }
        if let (ast::Expr::Tuple(tuple), Sort::VariadicTuple(element_sort)) = (expression, expected)
        {
            let values = tuple
                .elts
                .iter()
                .map(|element| {
                    self.lower(element, environment, result).and_then(|value| {
                        coerce_to_sort(value, element_sort, "variadic tuple element")
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let term = Term::VariadicTuple {
                element_sort: (**element_sort).clone(),
                values,
            };
            term.sort().map_err(type_failure)?;
            return Ok(term);
        }
        coerce_to_sort(
            self.lower(expression, environment, result)?,
            expected,
            context,
        )
    }

    fn source_call<'a>(&self, expression: &'a ast::Expr) -> Option<&'a ast::ExprCall> {
        if let Some(call) = revealed_source_call(expression) {
            let ast::Expr::Name(name) = call.func.as_ref() else {
                return None;
            };
            return self
                .functions
                .contains_key(name.id.as_str())
                .then_some(call);
        }
        let ast::Expr::Call(call) = expression else {
            return None;
        };
        let ast::Expr::Name(name) = call.func.as_ref() else {
            return None;
        };
        self.functions
            .contains_key(name.id.as_str())
            .then_some(call)
    }

    fn sorted_builtin_call<'a>(&self, expression: &'a ast::Expr) -> Option<&'a ast::ExprCall> {
        if self.functions.contains_key("sorted") || self.globals.contains_key("sorted") {
            return None;
        }
        let ast::Expr::Call(call) = expression else {
            return None;
        };
        let ast::Expr::Name(name) = call.func.as_ref() else {
            return None;
        };
        (name.id.as_str() == "sorted" && call.args.len() == 1 && call.keywords.is_empty())
            .then_some(call)
    }

    fn sum_builtin_call<'a>(&self, expression: &'a ast::Expr) -> Option<&'a ast::ExprCall> {
        if self.functions.contains_key("sum") || self.globals.contains_key("sum") {
            return None;
        }
        let ast::Expr::Call(call) = expression else {
            return None;
        };
        let ast::Expr::Name(name) = call.func.as_ref() else {
            return None;
        };
        (name.id.as_str() == "sum" && call.args.len() == 1 && call.keywords.is_empty())
            .then_some(call)
    }

    fn enumerate_builtin_call<'a>(&self, expression: &'a ast::Expr) -> Option<&'a ast::ExprCall> {
        if self.functions.contains_key("enumerate") || self.globals.contains_key("enumerate") {
            return None;
        }
        let ast::Expr::Call(call) = expression else {
            return None;
        };
        let ast::Expr::Name(name) = call.func.as_ref() else {
            return None;
        };
        (name.id.as_str() == "enumerate"
            && (1..=2).contains(&call.args.len())
            && call.keywords.is_empty())
        .then_some(call)
    }

    fn enumerate_call_effects(
        &self,
        call: &ast::ExprCall,
        environment: &BTreeMap<String, Term>,
        _result_name: &str,
    ) -> Result<SourceCallEffects, ContractFailure> {
        let source = self.lower(&call.args[0], environment, None)?;
        let Sort::List(_) = source.sort().map_err(type_failure)? else {
            return failure(
                "frontend.python.contracts.enumerate-iterable-type-unsupported",
                "enumerate currently requires a homogeneous List value",
            );
        };
        let start = call.args.get(1).map_or_else(
            || Ok(Term::Int { value: 0 }),
            |expression| {
                self.lower(expression, environment, None)
                    .and_then(|value| coerce_python_int(value, "enumerate start"))
            },
        )?;
        let (value, preconditions) = match source {
            Term::List { values, .. } => {
                let pairs = values
                    .into_iter()
                    .enumerate()
                    .map(|(index, value)| {
                        let index = i64::try_from(index).map_err(|_| ContractFailure {
                            code: "frontend.python.integer.out-of-range",
                            message: "enumerate index exceeds the current i64 frontend".to_owned(),
                        })?;
                        Ok(Term::Tuple {
                            values: vec![
                                Term::Add {
                                    left: Box::new(start.clone()),
                                    right: Box::new(Term::Int { value: index }),
                                },
                                value,
                            ],
                        })
                    })
                    .collect::<Result<Vec<_>, ContractFailure>>()?;
                (Term::Tuple { values: pairs }, Vec::new())
            }
            Term::Variable { .. } => (
                // The failed precondition makes the normal successor unreachable. Keep a
                // well-sorted placeholder so no unsupported nested-sequence sort can hide the
                // actual application-precondition diagnostic.
                Term::Tuple { values: Vec::new() },
                vec![Term::Bool { value: false }],
            ),
            _ => {
                return failure(
                    "frontend.python.contracts.enumerate-iterable-representation-unsupported",
                    "enumerate requires either a concrete or symbolic homogeneous List value",
                );
            }
        };
        Ok(SourceCallEffects {
            value,
            preconditions,
            precondition_failure: CallPreconditionFailure::InsufficientPermission,
            postconditions: Vec::new(),
            exceptional_postconditions: Vec::new(),
        })
    }

    fn sorted_call_effects(
        &self,
        call: &ast::ExprCall,
        environment: &BTreeMap<String, Term>,
        result_name: &str,
    ) -> Result<SourceCallEffects, ContractFailure> {
        if let Some(function_name) = self.first_exceptional_sequence_argument_callee(&call.args[0])
        {
            return failure(
                "frontend.python.contracts.sorted-argument-exceptional-call-unsupported",
                format!(
                    "sorted argument reaches source call {function_name:?} with a declared exceptional outcome; the outcome must not be erased by the total builtin summary"
                ),
            );
        }
        let source = self.lower(&call.args[0], environment, None)?;
        let Sort::List(element_sort) = source.sort().map_err(type_failure)? else {
            return failure(
                "frontend.python.contracts.sorted-iterable-type-unsupported",
                "sorted currently requires a homogeneous List value",
            );
        };
        if !matches!(
            element_sort.as_ref(),
            Sort::Bool | Sort::Int | Sort::String | Sort::Bytes
        ) {
            return failure(
                "frontend.python.contracts.sorted-element-type-unsupported",
                format!(
                    "sorted requires elements with total built-in ordering, found {element_sort:?}"
                ),
            );
        }
        if element_sort.as_ref() == &Sort::Int {
            return Ok(SourceCallEffects {
                value: python_sequence_builtins::sorted(source)
                    .map_err(sequence_builtin_failure)?,
                preconditions: Vec::new(),
                precondition_failure: CallPreconditionFailure::Assertion,
                postconditions: Vec::new(),
                exceptional_postconditions: Vec::new(),
            });
        }
        let value = Term::Variable {
            name: result_name.to_owned(),
            sort: Sort::List(element_sort),
        };
        let postcondition = Term::Equal {
            left: Box::new(sequence_length(&value)?),
            right: Box::new(sequence_length(&source)?),
        };
        Ok(SourceCallEffects {
            value,
            preconditions: Vec::new(),
            precondition_failure: CallPreconditionFailure::Assertion,
            postconditions: vec![postcondition],
            exceptional_postconditions: Vec::new(),
        })
    }

    fn first_exceptional_sequence_argument_callee(&self, expression: &ast::Expr) -> Option<String> {
        let mut pending = BTreeSet::new();
        collect_called_names_expression(expression, &mut pending);
        let mut visited = BTreeSet::new();
        while let Some(function_name) = pending.pop_first() {
            let Some(summary) = self.functions.get(function_name.as_str()) else {
                continue;
            };
            if !summary.exceptional_postconditions.is_empty() {
                return Some(function_name);
            }
            if !visited.insert(function_name) {
                continue;
            }
            if let Some(expression) = &summary.expression {
                collect_called_names_expression(expression, &mut pending);
            }
        }
        None
    }

    fn contract_source_call<'a>(&self, expression: &'a ast::Expr) -> Option<&'a ast::ExprCall> {
        let revealed = revealed_source_call(expression).is_some();
        let call = self.source_call(expression)?;
        let ast::Expr::Name(name) = call.func.as_ref() else {
            return None;
        };
        let summary = &self.functions[name.id.as_str()];
        (revealed
            || summary.ghost
            || summary.modular_call
            || !summary.preconditions.is_empty()
            || !summary.postconditions.is_empty())
        .then_some(call)
    }

    fn source_call_effects(
        &self,
        call: &ast::ExprCall,
        environment: &BTreeMap<String, Term>,
        result: Option<&Term>,
        result_name: &str,
    ) -> Result<SourceCallEffects, ContractFailure> {
        let ast::Expr::Name(name) = call.func.as_ref() else {
            return unsupported_expression(&ast::Expr::Call(call.clone()));
        };
        let function_name = name.id.as_str();
        if self.call_stack.iter().any(|item| item == function_name) {
            return failure(
                "frontend.python.contracts.recursive-inline-call",
                format!("recursive source call {function_name:?} requires a termination contract"),
            );
        }
        let summary = &self.functions[function_name];
        if summary.ghost {
            return failure(
                "frontend.python.contracts.ghost-call-unsupported",
                format!(
                    "call to ghost function {function_name:?} requires an explicitly modeled ghost context"
                ),
            );
        }
        let callee_environment =
            self.bind_call_arguments(function_name, summary, call, environment, result)?;
        let mut call_stack = self.call_stack.clone();
        call_stack.push(function_name.to_owned());
        let nested = Self {
            functions: self.functions,
            globals: self.globals,
            type_comments: self.type_comments,
            call_stack,
            exception_hierarchy: self.exception_hierarchy,
            conformance_mode: self.conformance_mode,
        };
        let mut preconditions = Vec::new();
        for precondition in &summary.preconditions {
            let clauses = nested.lower_specification_clauses(
                precondition,
                &callee_environment,
                None,
                "source call precondition",
            )?;
            for clause in clauses {
                ensure_boolean(&clause, "source call precondition")?;
                preconditions.push(clause);
            }
        }
        let value = match &summary.return_sort {
            Sort::Unit => Term::Unit,
            sort => Term::Variable {
                name: result_name.to_owned(),
                sort: sort.clone(),
            },
        };
        let mut postconditions = Vec::new();
        for postcondition in &summary.postconditions {
            let clauses = nested.lower_postcondition_clauses(
                postcondition,
                &callee_environment,
                &value,
                "source call postcondition",
            )?;
            for clause in clauses {
                ensure_boolean(&clause, "source call postcondition")?;
                postconditions.push(clause);
            }
        }
        let mut exceptional_postconditions = BTreeMap::<String, Vec<Term>>::new();
        for (exception_type, postcondition) in &summary.exceptional_postconditions {
            let clauses = nested.lower_specification_clauses(
                postcondition,
                &callee_environment,
                None,
                "source call exceptional postcondition",
            )?;
            for clause in clauses {
                ensure_boolean(&clause, "source call exceptional postcondition")?;
                exceptional_postconditions
                    .entry(exception_type.clone())
                    .or_default()
                    .push(clause);
            }
        }
        Ok(SourceCallEffects {
            value,
            preconditions,
            precondition_failure: CallPreconditionFailure::Assertion,
            postconditions,
            exceptional_postconditions: exceptional_postconditions.into_iter().collect(),
        })
    }

    fn lower_comprehension_source(
        &self,
        generators: &[ast::Comprehension],
        environment: &BTreeMap<String, Term>,
        result: Option<&Term>,
        offset: u32,
    ) -> Result<LoweredComprehensionSource, ContractFailure> {
        let [generator] = generators else {
            return failure(
                "frontend.python.contracts.comprehension-generator-count",
                "comprehensions require exactly one generator",
            );
        };
        if generator.is_async {
            return failure(
                "frontend.python.contracts.comprehension-async-unsupported",
                "async comprehensions are outside the scalar proof fragment",
            );
        }
        let ast::Expr::Name(target) = &generator.target else {
            return failure(
                "frontend.python.contracts.comprehension-target-unsupported",
                "comprehensions require one direct local-name target",
            );
        };
        let ast::Expr::Name(_) = &generator.iter else {
            return failure(
                "frontend.python.contracts.comprehension-iterable-expression-unsupported",
                "the comprehension iterable must be a read-only local List value",
            );
        };
        if !generator
            .ifs
            .iter()
            .all(comprehension_expression_is_pure_total)
        {
            return failure(
                "frontend.python.contracts.comprehension-filter-effect-unsupported",
                "comprehension filters must be total, side-effect-free primitive expressions",
            );
        }
        let source = self.lower(&generator.iter, environment, result)?;
        let Sort::List(source_element) = source.sort().map_err(type_failure)? else {
            return failure(
                "frontend.python.contracts.comprehension-iterable-type",
                "comprehensions require a homogeneous read-only List source",
            );
        };
        if !matches!(
            *source_element,
            Sort::Bool | Sort::Int | Sort::String | Sort::Bytes
        ) {
            return failure(
                "frontend.python.contracts.comprehension-source-element-unsupported",
                format!(
                    "comprehension source elements require primitive value semantics, found {source_element:?}"
                ),
            );
        }
        let binder = format!(
            "{}::comprehension::{offset}::{}",
            self.call_stack.join("::"),
            target.id
        );
        let mut nested_environment = environment.clone();
        nested_environment.insert(
            target.id.to_string(),
            Term::Variable {
                name: binder.clone(),
                sort: (*source_element).clone(),
            },
        );
        let mut filters = Vec::with_capacity(generator.ifs.len());
        for filter in &generator.ifs {
            let filter = self.lower(filter, &nested_environment, result)?;
            ensure_boolean(&filter, "comprehension filter")?;
            filters.push(filter);
        }
        let filter = match filters.len() {
            0 => None,
            1 => filters.pop(),
            _ => Some(Term::And { values: filters }),
        };
        Ok((
            format!("{}::comprehension::{offset}", self.call_stack.join("::")),
            source,
            binder,
            *source_element,
            nested_environment,
            filter,
        ))
    }

    fn lower(
        &self,
        expression: &ast::Expr,
        environment: &BTreeMap<String, Term>,
        result: Option<&Term>,
    ) -> Result<Term, ContractFailure> {
        match expression {
            ast::Expr::Name(name) => {
                environment
                    .get(name.id.as_str())
                    .cloned()
                    .ok_or_else(|| ContractFailure {
                        code: "frontend.python.name.unresolved",
                        message: format!("unresolved symbolic name {:?}", name.id),
                    })
            }
            ast::Expr::Constant(constant) => match &constant.value {
                ast::Constant::Bool(value) => Ok(Term::Bool { value: *value }),
                ast::Constant::Int(value) => Ok(Term::Int {
                    value: value.to_string().parse().map_err(|_| ContractFailure {
                        code: "frontend.python.integer.out-of-range",
                        message: format!(
                            "integer literal {value} exceeds the current i64 frontend"
                        ),
                    })?,
                }),
                ast::Constant::Str(value) => Ok(Term::String {
                    value: value.clone(),
                }),
                ast::Constant::Bytes(values) => Ok(Term::Bytes {
                    values: values.clone(),
                }),
                ast::Constant::None => Ok(Term::Unit),
                ast::Constant::Ellipsis => Ok(ellipsis_singleton()),
                _ => unsupported_expression(expression),
            },
            ast::Expr::BoolOp(operation) => {
                let mut values = operation
                    .values
                    .iter()
                    .map(|value| self.lower(value, environment, result))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut selected = values.pop().ok_or_else(|| ContractFailure {
                    code: "frontend.python.contracts.boolop-empty",
                    message: "boolean operation has no operands".to_owned(),
                })?;
                while let Some(value) = values.pop() {
                    let condition = coerce_truthy(value.clone(), "short-circuit operand")?;
                    selected = match operation.op {
                        ast::BoolOp::And => select_python_value(condition, selected, value)?,
                        ast::BoolOp::Or => select_python_value(condition, value, selected)?,
                    };
                }
                Ok(selected)
            }
            ast::Expr::IfExp(conditional) => {
                let condition = coerce_truthy(
                    self.lower(&conditional.test, environment, result)?,
                    "conditional expression",
                )?;
                let then_value = self.lower(&conditional.body, environment, result)?;
                let else_value = self.lower(&conditional.orelse, environment, result)?;
                select_python_value(condition, then_value, else_value)
            }
            ast::Expr::BinOp(operation) => {
                let left = self.lower(&operation.left, environment, result)?;
                let right = self.lower(&operation.right, environment, result)?;
                let left_sort = left.sort().map_err(type_failure)?;
                let right_sort = right.sort().map_err(type_failure)?;
                if operation.op == ast::Operator::Add {
                    if left_sort == Sort::String && right_sort == Sort::String {
                        return Ok(Term::StringConcat {
                            values: vec![left, right],
                        });
                    }
                    if left_sort == Sort::Bytes && right_sort == Sort::Bytes {
                        return Ok(Term::BytesConcat {
                            values: vec![left, right],
                        });
                    }
                    if matches!(left_sort, Sort::List(_)) && matches!(right_sort, Sort::List(_)) {
                        return python_sequence_builtins::concatenate(left, right)
                            .map_err(sequence_builtin_failure);
                    }
                }
                if operation.op == ast::Operator::Mult {
                    if left_sort == Sort::Bytes && matches!(right_sort, Sort::Int | Sort::Bool) {
                        return lower_bytes_repeat(left, right);
                    }
                    if right_sort == Sort::Bytes && matches!(left_sort, Sort::Int | Sort::Bool) {
                        return lower_bytes_repeat(right, left);
                    }
                }
                if operation.op == ast::Operator::Pow {
                    return lower_nonnegative_integer_power(left, right);
                }
                if operation.op == ast::Operator::Mod {
                    let divisor = match &*operation.right {
                        ast::Expr::Constant(ast::ExprConstant {
                            value: ast::Constant::Int(value),
                            ..
                        }) => value.to_string().parse::<u64>().ok().filter(|value| *value > 0),
                        _ => None,
                    }
                    .ok_or_else(|| ContractFailure {
                        code: "frontend.python.contracts.modulo-divisor-unsupported",
                        message: "Python modulo requires a positive integer-literal divisor in the scalar fragment".to_owned(),
                    })?;
                    let left = coerce_python_int(left, "modulo dividend")?;
                    let divisor_i64 = i64::try_from(divisor).map_err(|_| ContractFailure {
                        code: "frontend.python.integer.out-of-range",
                        message: "modulo divisor exceeds the current i64 frontend".to_owned(),
                    })?;
                    return Ok(Term::Subtract {
                        left: Box::new(left.clone()),
                        right: Box::new(Term::Multiply {
                            left: Box::new(Term::FloorDivideByPositive {
                                value: Box::new(left),
                                divisor,
                            }),
                            right: Box::new(Term::Int { value: divisor_i64 }),
                        }),
                    });
                }
                let left = coerce_python_int(left, "arithmetic left operand")?;
                let right = coerce_python_int(right, "arithmetic right operand")?;
                let (left, right) = (Box::new(left), Box::new(right));
                match operation.op {
                    ast::Operator::Add => Ok(Term::Add { left, right }),
                    ast::Operator::Sub => Ok(Term::Subtract { left, right }),
                    ast::Operator::Mult => Ok(Term::Multiply { left, right }),
                    _ => unsupported_expression(expression),
                }
            }
            ast::Expr::UnaryOp(operation) => {
                let value = self.lower(&operation.operand, environment, result)?;
                match operation.op {
                    ast::UnaryOp::Not => {
                        let value = coerce_truthy(value, "not operand")?;
                        Ok(Term::Not {
                            value: Box::new(value),
                        })
                    }
                    ast::UnaryOp::USub => {
                        let value = coerce_python_int(value, "negation operand")?;
                        Ok(Term::Negate {
                            value: Box::new(value),
                        })
                    }
                    ast::UnaryOp::UAdd => coerce_python_int(value, "unary plus operand"),
                    _ => unsupported_expression(expression),
                }
            }
            ast::Expr::Compare(comparison)
                if !comparison.ops.is_empty()
                    && comparison.ops.len() == comparison.comparators.len() =>
            {
                let mut left = self.lower(&comparison.left, environment, result)?;
                let mut relations = Vec::with_capacity(comparison.ops.len());
                for (operator, comparator) in comparison.ops.iter().zip(&comparison.comparators) {
                    let right = self.lower(comparator, environment, result)?;
                    relations.push(self.lower_comparison_pair(
                        operator,
                        left,
                        right.clone(),
                        expression,
                    )?);
                    left = right;
                }
                Ok(Term::And { values: relations })
            }
            ast::Expr::Call(call) => {
                if let ast::Expr::Attribute(attribute) = call.func.as_ref()
                    && attribute.attr.as_str() == "format"
                    && call.keywords.is_empty()
                {
                    let template = self.lower(&attribute.value, environment, result)?;
                    let arguments = call
                        .args
                        .iter()
                        .map(|argument| self.lower(argument, environment, result))
                        .collect::<Result<Vec<_>, _>>()?;
                    return lower_constant_string_format(template, &arguments, expression);
                }
                if let ast::Expr::Attribute(attribute) = call.func.as_ref()
                    && attribute.attr.as_str() == "join"
                    && call.args.len() == 1
                    && call.keywords.is_empty()
                {
                    let separator = self.lower(&attribute.value, environment, result)?;
                    let values = self.lower(&call.args[0], environment, result)?;
                    return lower_bytes_join(separator, values);
                }
                if let ast::Expr::Attribute(attribute) = call.func.as_ref()
                    && attribute.attr.as_str() == "keys"
                    && call.args.is_empty()
                    && call.keywords.is_empty()
                {
                    let dictionary = self.lower(&attribute.value, environment, result)?;
                    let Term::FiniteDict {
                        key_sort, entries, ..
                    } = dictionary
                    else {
                        return failure(
                            "frontend.python.contracts.dict-keys-receiver-unsupported",
                            "keys() requires a finite immutable dictionary literal value",
                        );
                    };
                    return Ok(Term::DictKeys {
                        key_sort,
                        values: entries.into_iter().map(|(key, _)| key).collect(),
                    });
                }
                let ast::Expr::Name(name) = call.func.as_ref() else {
                    return unsupported_expression(expression);
                };
                match name.id.as_str() {
                    "Forall" => {
                        if let Some((parameter, predicate, triggers)) = typed_integer_forall(call) {
                            if !quantified_subscripts_are_guarded(predicate, parameter) {
                                return failure(
                                    "frontend.python.contracts.quantified-index-unguarded",
                                    "typed Forall sequence indexing requires explicit 0 <= index and index < len(sequence) guards",
                                );
                            }
                            let ast::Expr::Call(implies) = predicate else {
                                return failure(
                                    "frontend.python.contracts.quantified-index-unguarded",
                                    "typed Forall is currently restricted to guarded sequence-index predicates",
                                );
                            };
                            let binder = format!(
                                "{}::forall::{}::{parameter}",
                                self.call_stack.join("::"),
                                u32::from(call.range.start())
                            );
                            let mut nested_environment = environment.clone();
                            nested_environment.insert(
                                parameter.to_owned(),
                                Term::Variable {
                                    name: binder.clone(),
                                    sort: Sort::Int,
                                },
                            );
                            let mut indexed_collections = Vec::new();
                            collect_binder_subscript_collections(
                                &implies.args[1],
                                parameter,
                                &mut indexed_collections,
                            );
                            for trigger in &triggers {
                                collect_binder_subscript_collections(
                                    trigger,
                                    parameter,
                                    &mut indexed_collections,
                                );
                            }
                            for collection in indexed_collections {
                                let collection =
                                    self.lower(collection, &nested_environment, result)?;
                                if !matches!(
                                    collection.sort().map_err(type_failure)?,
                                    Sort::List(_)
                                ) {
                                    return failure(
                                        "frontend.python.contracts.quantified-index-collection-type",
                                        "typed Forall indexing is restricted to homogeneous List values",
                                    );
                                }
                            }
                            for trigger in triggers {
                                self.lower(trigger, &nested_environment, result)?;
                                if matches!(trigger, ast::Expr::Name(_)) {
                                    return failure(
                                        "frontend.python.contracts.quantifier-trigger-unsupported",
                                        "typed Forall triggers must be read-only indexed terms containing the quantified binder",
                                    );
                                }
                            }
                            let guard =
                                self.lower(&implies.args[0], &nested_environment, result)?;
                            ensure_boolean(&guard, "Forall index guard")?;
                            let predicate = self.lower(predicate, &nested_environment, result)?;
                            ensure_boolean(&predicate, "Forall predicate")?;
                            return Ok(Term::ForAll {
                                binder,
                                binder_sort: Sort::Int,
                                body: Box::new(predicate),
                            });
                        }
                        if looks_like_typed_integer_forall(call) {
                            return failure(
                                "frontend.python.contracts.quantifier-trigger-unsupported",
                                "typed Forall requires nonempty lists of read-only trigger expressions and one unannotated integer binder",
                            );
                        }
                        let Some((collection, parameter, predicate)) = finite_literal_forall(call)
                        else {
                            return unsupported_expression(expression);
                        };
                        let collection =
                            lower_to_sequence(self.lower(collection, environment, result)?).map_err(
                                |_| ContractFailure {
                                    code: "frontend.python.contracts.forall-symbolic-collection-unsupported",
                                    message: "Forall currently requires a statically known homogeneous list literal"
                                        .to_owned(),
                                },
                            )?;
                        let Term::List { values, .. } = collection else {
                            return failure(
                                "frontend.python.contracts.forall-symbolic-collection-unsupported",
                                "Forall currently requires a statically known homogeneous list literal",
                            );
                        };
                        let mut predicates = Vec::with_capacity(values.len());
                        for value in values {
                            let mut nested_environment = environment.clone();
                            nested_environment.insert(parameter.to_owned(), value);
                            let predicate = self.lower(predicate, &nested_environment, result)?;
                            ensure_boolean(&predicate, "Forall predicate")?;
                            predicates.push(predicate);
                        }
                        Ok(Term::And { values: predicates })
                    }
                    "range" if (1..=3).contains(&call.args.len()) && call.keywords.is_empty() => {
                        lower_constant_range(call)
                    }
                    "str" if call.args.len() == 1 && call.keywords.is_empty() => {
                        match self.lower(&call.args[0], environment, result)? {
                            value @ Term::String { .. } => Ok(value),
                            Term::Int { value } => Ok(Term::String {
                                value: value.to_string(),
                            }),
                            Term::Bool { value } => Ok(Term::String {
                                value: if value { "True" } else { "False" }.to_owned(),
                            }),
                            _ => failure(
                                "frontend.python.contracts.str-conversion-symbolic-unsupported",
                                "canonical str conversion requires a statically known int, bool, or string value",
                            ),
                        }
                    }
                    "ToSeq" if call.args.len() == 1 && call.keywords.is_empty() => {
                        lower_to_sequence(self.lower(&call.args[0], environment, result)?)
                    }
                    "Result" if call.args.is_empty() && call.keywords.is_empty() => {
                        result.cloned().ok_or_else(|| ContractFailure {
                            code: "frontend.python.contracts.result-outside-postcondition",
                            message: "Result() is valid only in Ensures".to_owned(),
                        })
                    }
                    "ResultT" if call.args.len() == 1 && call.keywords.is_empty() => {
                        let value = result.cloned().ok_or_else(|| ContractFailure {
                            code: "frontend.python.contracts.result-outside-postcondition",
                            message: "ResultT(...) is valid only in Ensures".to_owned(),
                        })?;
                        let declared = annotation_sort(call.args.first())?;
                        let actual = value.sort().map_err(type_failure)?;
                        if declared != actual {
                            return failure(
                                "frontend.python.contracts.result-type-mismatch",
                                format!(
                                    "ResultT declares {declared:?}, but the result has sort {actual:?}"
                                ),
                            );
                        }
                        Ok(value)
                    }
                    "Acc" if call.args.len() == 1 && call.keywords.is_empty() => {
                        if let ast::Expr::Name(name) = &call.args[0]
                            && self.globals.contains_key(name.id.as_str())
                        {
                            return Ok(module_global_permission(name.id.as_str()));
                        }
                        let permission = self.lower(&call.args[0], environment, result)?;
                        ensure_boolean(&permission, "Acc argument")?;
                        Ok(permission)
                    }
                    "Implies" if call.args.len() == 2 && call.keywords.is_empty() => {
                        let left = self.lower(&call.args[0], environment, result)?;
                        let right = self.lower(&call.args[1], environment, result)?;
                        ensure_boolean(&left, "Implies left operand")?;
                        ensure_boolean(&right, "Implies right operand")?;
                        Ok(Term::Implies {
                            left: Box::new(left),
                            right: Box::new(right),
                        })
                    }
                    "len" if call.args.len() == 1 && call.keywords.is_empty() => {
                        let value = self.lower(&call.args[0], environment, result)?;
                        match value.sort().map_err(type_failure)? {
                            Sort::String => match value {
                                Term::String { value } => Ok(Term::Int {
                                    value: i64::try_from(value.chars().count()).map_err(|_| {
                                        ContractFailure {
                                            code: "frontend.python.contracts.string-length-overflow",
                                            message: "string length exceeds the current i64 frontend"
                                                .to_owned(),
                                        }
                                    })?,
                                }),
                                value => Ok(Term::StringLength {
                                    value: Box::new(value),
                                }),
                            },
                            Sort::Tuple(elements) => Ok(Term::Int {
                                value: i64::try_from(elements.len()).map_err(|_| {
                                    ContractFailure {
                                        code: "frontend.python.contracts.tuple-length-overflow",
                                        message:
                                            "fixed tuple length exceeds the current i64 frontend"
                                                .to_owned(),
                                    }
                                })?,
                            }),
                            Sort::VariadicTuple(_) => Ok(Term::VariadicTupleLength {
                                value: Box::new(value),
                            }),
                            Sort::List(_) => sequence_length(&value),
                            Sort::Set(_) => Ok(Term::SetLength {
                                value: Box::new(value),
                            }),
                            Sort::Dict(_, _) => Ok(Term::DictLength {
                                value: Box::new(value),
                            }),
                            Sort::FiniteDict(_, _) => {
                                let Term::FiniteDict { entries, .. } = value else {
                                    unreachable!("finite dictionary sort came from another term")
                                };
                                Ok(Term::Int {
                                    value: i64::try_from(entries.len()).map_err(|_| {
                                        ContractFailure {
                                            code: "frontend.python.contracts.dict-length-overflow",
                                            message: "finite dictionary length exceeds the current i64 frontend"
                                                .to_owned(),
                                        }
                                    })?,
                                })
                            }
                            Sort::DictKeys(_) => {
                                let Term::DictKeys { values, .. } = value else {
                                    unreachable!("dictionary-key sort came from another term")
                                };
                                Ok(Term::Int {
                                    value: i64::try_from(values.len()).map_err(|_| {
                                        ContractFailure {
                                            code: "frontend.python.contracts.dict-keys-length-overflow",
                                            message: "dictionary-key view length exceeds the current i64 frontend"
                                                .to_owned(),
                                        }
                                    })?,
                                })
                            }
                            Sort::Bytes | Sort::Range => sequence_length(&value),
                            _ => unsupported_expression(expression),
                        }
                    }
                    "sum" if self.sum_builtin_call(expression).is_some() => {
                        if let Some(function_name) =
                            self.first_exceptional_sequence_argument_callee(&call.args[0])
                        {
                            return failure(
                                "frontend.python.contracts.sum-argument-exceptional-call-unsupported",
                                format!(
                                    "sum argument reaches source call {function_name:?} with a declared exceptional outcome; the outcome must be modeled before applying the total builtin"
                                ),
                            );
                        }
                        let source = self.lower(&call.args[0], environment, result)?;
                        python_sequence_builtins::sum(source).map_err(sequence_builtin_failure)
                    }
                    "abs" if call.args.len() == 1 && call.keywords.is_empty() => {
                        let value = coerce_python_int(
                            self.lower(&call.args[0], environment, result)?,
                            "abs argument",
                        )?;
                        Ok(lower_integer_abs(value))
                    }
                    function @ ("min" | "max")
                        if !call.args.is_empty() && call.keywords.is_empty() =>
                    {
                        let mut values = Vec::new();
                        if call.args.len() == 1 {
                            let value = self.lower(&call.args[0], environment, result)?;
                            let Term::List {
                                element_sort,
                                values: list_values,
                            } = value
                            else {
                                return failure(
                                    "frontend.python.contracts.extremum-symbolic-iterable-unsupported",
                                    format!(
                                        "{function} with one argument requires a statically shaped nonempty List[int]"
                                    ),
                                );
                            };
                            if element_sort != Sort::Int {
                                return failure(
                                    "frontend.python.contracts.extremum-element-type",
                                    format!(
                                        "{function} requires integer values, found List[{element_sort:?}]"
                                    ),
                                );
                            }
                            values = list_values;
                        } else {
                            for argument in &call.args {
                                values.push(coerce_python_int(
                                    self.lower(argument, environment, result)?,
                                    "min/max argument",
                                )?);
                            }
                        }
                        lower_integer_extremum(function, values)
                    }
                    "list_pred" if call.args.len() == 1 && call.keywords.is_empty() => {
                        let value = self.lower(&call.args[0], environment, result)?;
                        if matches!(value.sort().map_err(type_failure)?, Sort::List(_)) {
                            // Lists in this fragment are immutable sequence values. Nagini's
                            // ownership predicate therefore has no residual heap condition: every
                            // admitted List value has the complete readable value represented by
                            // the VC term. Mutation remains outside this fragment.
                            Ok(Term::Bool { value: true })
                        } else {
                            failure(
                                "frontend.python.contracts.list-predicate-type",
                                "list_pred requires a homogeneous List value",
                            )
                        }
                    }
                    "type" if call.args.len() == 1 && call.keywords.is_empty() => {
                        let value = self.lower(&call.args[0], environment, result)?;
                        if value == ellipsis_singleton() {
                            Ok(ellipsis_type_object())
                        } else {
                            failure(
                                "frontend.python.contracts.type-call-unsupported",
                                "scalar type() currently owns only the canonical Ellipsis singleton",
                            )
                        }
                    }
                    "isinstance" if call.args.len() == 2 && call.keywords.is_empty() => {
                        let ast::Expr::Name(expected) = &call.args[1] else {
                            return unsupported_expression(expression);
                        };
                        let value = self.lower(&call.args[0], environment, result)?;
                        if expected.id.as_str() == "EllipsisType" {
                            if environment.get("EllipsisType") != Some(&ellipsis_type_object()) {
                                return failure(
                                    "frontend.python.contracts.ellipsis-binding-shadowed",
                                    "isinstance EllipsisType target is not the canonical imported type",
                                );
                            }
                            return Ok(Term::Bool {
                                value: value == ellipsis_singleton(),
                            });
                        }
                        if expected.id.as_str() == "str" {
                            return Ok(Term::Bool {
                                value: value.sort().map_err(type_failure)? == Sort::String,
                            });
                        }
                        ensure_supported_exception_type(
                            self.exception_hierarchy,
                            expected.id.as_str(),
                        )?;
                        match value {
                            Term::NominalReference { class, .. } => Ok(Term::Bool {
                                value: self
                                    .exception_hierarchy
                                    .matches(expected.id.as_str(), &class),
                            }),
                            other if other.sort().map_err(type_failure)? != Sort::Reference => {
                                Ok(Term::Bool { value: false })
                            }
                            _ => failure(
                                "frontend.python.contracts.dynamic-isinstance-unsupported",
                                "isinstance on a dynamically typed reference requires nominal type-flow information",
                            ),
                        }
                    }
                    function_name if self.functions.contains_key(function_name) => {
                        self.inline_call(function_name, call, environment, result)
                    }
                    _ => unsupported_expression(expression),
                }
            }
            ast::Expr::JoinedStr(joined) => {
                let mut values = Vec::new();
                for value in &joined.values {
                    match value {
                        ast::Expr::Constant(constant) => {
                            let ast::Constant::Str(value) = &constant.value else {
                                return unsupported_expression(value);
                            };
                            values.push(Term::String {
                                value: value.clone(),
                            });
                        }
                        ast::Expr::FormattedValue(formatted)
                            if formatted.format_spec.is_none()
                                && formatted.conversion == ast::ConversionFlag::None =>
                        {
                            let value = self.lower(&formatted.value, environment, result)?;
                            values.push(Term::String {
                                value: render_constant_as_string(&value)
                                    .ok_or_else(|| ContractFailure {
                                        code: "frontend.python.contracts.fstring-nonconstant",
                                        message: "formatted strings currently require primitive constant values"
                                            .to_owned(),
                                    })?,
                            });
                        }
                        _ => return unsupported_expression(value),
                    }
                }
                Ok(Term::StringConcat { values })
            }
            ast::Expr::Tuple(tuple) => Ok(Term::Tuple {
                values: tuple
                    .elts
                    .iter()
                    .map(|element| self.lower(element, environment, result))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            ast::Expr::ListComp(comprehension) => {
                if !comprehension_expression_is_pure_total(&comprehension.elt) {
                    return failure(
                        "frontend.python.contracts.comprehension-mapper-effect-unsupported",
                        "comprehension mappers must be total, side-effect-free primitive expressions",
                    );
                }
                let (id, source, binder, _, nested, filter) = self.lower_comprehension_source(
                    &comprehension.generators,
                    environment,
                    result,
                    comprehension.range.start().into(),
                )?;
                let mapped = self.lower(&comprehension.elt, &nested, result)?;
                let element_sort = mapped.sort().map_err(type_failure)?;
                if !is_immutable_collection_value_sort(&element_sort) {
                    return failure(
                        "frontend.python.contracts.comprehension-result-type-unsupported",
                        format!(
                            "list-comprehension results require primitive values, found {element_sort:?}"
                        ),
                    );
                }
                Ok(Term::ListComprehension {
                    id,
                    source: Box::new(source),
                    binder,
                    element_sort,
                    mapped: Box::new(mapped),
                    filter: filter.map(Box::new),
                })
            }
            ast::Expr::SetComp(comprehension) => {
                if !comprehension_expression_is_pure_total(&comprehension.elt) {
                    return failure(
                        "frontend.python.contracts.comprehension-mapper-effect-unsupported",
                        "comprehension mappers must be total, side-effect-free primitive expressions",
                    );
                }
                let (id, source, binder, _, nested, filter) = self.lower_comprehension_source(
                    &comprehension.generators,
                    environment,
                    result,
                    comprehension.range.start().into(),
                )?;
                let mut mapped = self.lower(&comprehension.elt, &nested, result)?;
                let mut element_sort = mapped.sort().map_err(type_failure)?;
                if element_sort == Sort::Bool {
                    mapped = coerce_python_int(mapped, "set-comprehension bool key normalization")?;
                    element_sort = Sort::Int;
                }
                if !is_immutable_collection_key_sort(&element_sort) {
                    return failure(
                        "frontend.python.contracts.comprehension-result-type-unsupported",
                        format!(
                            "set-comprehension results require primitive Python keys, found {element_sort:?}"
                        ),
                    );
                }
                Ok(Term::SetComprehension {
                    id,
                    source: Box::new(source),
                    binder,
                    element_sort,
                    mapped: Box::new(mapped),
                    filter: filter.map(Box::new),
                })
            }
            ast::Expr::DictComp(comprehension) => {
                if !comprehension_expression_is_pure_total(&comprehension.key)
                    || !comprehension_expression_is_pure_total(&comprehension.value)
                {
                    return failure(
                        "frontend.python.contracts.comprehension-mapper-effect-unsupported",
                        "dictionary comprehension keys and values must be total, side-effect-free primitive expressions",
                    );
                }
                let (id, source, binder, _, nested, filter) = self.lower_comprehension_source(
                    &comprehension.generators,
                    environment,
                    result,
                    comprehension.range.start().into(),
                )?;
                let mut key = self.lower(&comprehension.key, &nested, result)?;
                let mut key_sort = key.sort().map_err(type_failure)?;
                if key_sort == Sort::Bool {
                    key = coerce_python_int(key, "dictionary bool key normalization")?;
                    key_sort = Sort::Int;
                }
                if !is_immutable_collection_key_sort(&key_sort) {
                    return failure(
                        "frontend.python.contracts.dict-key-unsupported",
                        format!(
                            "dictionary comprehension keys require primitive Python equality, found {key_sort:?}"
                        ),
                    );
                }
                let value = self.lower(&comprehension.value, &nested, result)?;
                let value_sort = value.sort().map_err(type_failure)?;
                if !is_immutable_collection_value_sort(&value_sort) {
                    return failure(
                        "frontend.python.contracts.comprehension-result-type-unsupported",
                        format!(
                            "dictionary-comprehension values require primitive values, found {value_sort:?}"
                        ),
                    );
                }
                Ok(Term::DictComprehension {
                    id,
                    source: Box::new(source),
                    binder,
                    key_sort,
                    value_sort,
                    key: Box::new(key),
                    value: Box::new(value),
                    filter: filter.map(Box::new),
                })
            }
            ast::Expr::List(list) => {
                let mut values = list
                    .elts
                    .iter()
                    .map(|element| self.lower(element, environment, result))
                    .collect::<Result<Vec<_>, _>>()?;
                let first = values.first().ok_or_else(|| ContractFailure {
                    code: "frontend.python.contracts.empty-list-needs-context",
                    message: "an empty list literal requires an explicit List[T] assignment, argument, or return context"
                        .to_owned(),
                })?;
                let element_sort = first.sort().map_err(type_failure)?;
                if !is_immutable_collection_value_sort(&element_sort) {
                    return failure(
                        "frontend.python.contracts.list-element-type-unsupported",
                        format!(
                            "list literals currently require homogeneous primitive or reference elements, found {element_sort:?}"
                        ),
                    );
                }
                for value in &mut values {
                    let original = std::mem::replace(value, Term::Unit);
                    *value = coerce_to_sort(original, &element_sort, "list element")?;
                }
                let term = Term::List {
                    element_sort,
                    values,
                };
                term.sort().map_err(type_failure)?;
                Ok(term)
            }
            ast::Expr::Set(set) => {
                let mut values = set
                    .elts
                    .iter()
                    .map(|element| self.lower(element, environment, result))
                    .collect::<Result<Vec<_>, _>>()?;
                let first = values.first().ok_or_else(|| ContractFailure {
                    code: "frontend.python.contracts.empty-set-needs-context",
                    message: "an empty set literal requires an explicit construction boundary"
                        .to_owned(),
                })?;
                let mut element_sort = first.sort().map_err(type_failure)?;
                if element_sort == Sort::Bool {
                    element_sort = Sort::Int;
                }
                if !is_immutable_collection_key_sort(&element_sort) {
                    return failure(
                        "frontend.python.contracts.set-element-type-unsupported",
                        format!(
                            "set literals require immutable primitive or fixed-tuple values, found {element_sort:?}"
                        ),
                    );
                }
                for value in &mut values {
                    if !term_is_closed_immutable_value(value) {
                        return failure(
                            "frontend.python.contracts.set-literal-symbolic-unsupported",
                            "set literals in the immutable scalar fragment require closed values; symbolic construction needs exact duplicate elimination",
                        );
                    }
                    let original = std::mem::replace(value, Term::Unit);
                    *value = coerce_to_sort(original, &element_sort, "set element")?;
                }
                let offset: usize = set.range.start().into();
                let binder = format!("__maledictus_set_literal_{offset}");
                let source = Term::List {
                    element_sort: element_sort.clone(),
                    values,
                };
                let term = Term::SetComprehension {
                    id: format!("set-literal:{offset}"),
                    source: Box::new(source),
                    binder: binder.clone(),
                    element_sort: element_sort.clone(),
                    mapped: Box::new(Term::Variable {
                        name: binder,
                        sort: element_sort,
                    }),
                    filter: None,
                };
                term.sort().map_err(type_failure)?;
                Ok(term)
            }
            ast::Expr::Dict(dictionary) => {
                if dictionary.keys.is_empty() {
                    return failure(
                        "frontend.python.contracts.empty-dict-needs-context",
                        "an empty dictionary literal requires an explicit finite key/value context",
                    );
                }
                let mut entries = Vec::<(Term, Term)>::with_capacity(dictionary.keys.len());
                let mut key_sort = None;
                let mut value_sort = None;
                for (key, value) in dictionary.keys.iter().zip(&dictionary.values) {
                    let Some(key) = key.as_ref() else {
                        return failure(
                            "frontend.python.contracts.dict-unpack-unsupported",
                            "finite dictionary literals do not support ** unpacking",
                        );
                    };
                    let key = match self.lower(key, environment, result)? {
                        Term::Bool { value } => Term::Int {
                            value: i64::from(value),
                        },
                        key @ (Term::Int { .. }
                        | Term::String { .. }
                        | Term::Bytes { .. }
                        | Term::Tuple { .. }) => key,
                        _ => {
                            return failure(
                                "frontend.python.contracts.dict-key-unsupported",
                                "finite dictionary keys must be statically known int, bool, str, or bytes values",
                            );
                        }
                    };
                    let current_key_sort = key.sort().map_err(type_failure)?;
                    let expected_key_sort =
                        key_sort.get_or_insert_with(|| current_key_sort.clone());
                    if *expected_key_sort != current_key_sort {
                        return failure(
                            "frontend.python.contracts.dict-key-type-heterogeneous",
                            format!(
                                "finite dictionary keys must have one sort, found {expected_key_sort:?} and {current_key_sort:?}"
                            ),
                        );
                    }

                    let value = self.lower(value, environment, result)?;
                    let current_value_sort = value.sort().map_err(type_failure)?;
                    if !is_immutable_collection_value_sort(&current_value_sort) {
                        return failure(
                            "frontend.python.contracts.dict-value-type-unsupported",
                            format!(
                                "finite dictionary values require a primitive or reference sort, found {current_value_sort:?}"
                            ),
                        );
                    }
                    let expected_value_sort =
                        value_sort.get_or_insert_with(|| current_value_sort.clone());
                    let value =
                        coerce_to_sort(value, expected_value_sort, "finite dictionary value")?;
                    if let Some(position) = entries
                        .iter()
                        .position(|(existing_key, _)| existing_key == &key)
                    {
                        entries[position].1 = value;
                    } else {
                        entries.push((key, value));
                    }
                }
                let term = Term::FiniteDict {
                    key_sort: key_sort.expect("nonempty dictionary established key sort"),
                    value_sort: value_sort.expect("nonempty dictionary established value sort"),
                    entries,
                };
                term.sort().map_err(type_failure)?;
                Ok(term)
            }
            ast::Expr::Subscript(subscript) => {
                let collection = self.lower(&subscript.value, environment, result)?;
                if let ast::Expr::Slice(slice) = subscript.slice.as_ref() {
                    return lower_static_slice(collection, slice);
                }
                let term = match collection.sort().map_err(type_failure)? {
                    Sort::Tuple(elements) => {
                        if let Some(raw_index) = constant_tuple_index(&subscript.slice) {
                            let length =
                                i128::try_from(elements.len()).map_err(|_| ContractFailure {
                                    code: "frontend.python.contracts.tuple-length-overflow",
                                    message:
                                        "fixed tuple length exceeds the current signed index frontend"
                                            .to_owned(),
                                })?;
                            let normalized = if raw_index < 0 {
                                length.checked_add(raw_index)
                            } else {
                                Some(raw_index)
                            };
                            let index = normalized
                                .filter(|index| *index >= 0 && *index < length)
                                .and_then(|index| usize::try_from(index).ok())
                                .ok_or_else(|| ContractFailure {
                                    code: "frontend.python.contracts.tuple-index-invalid",
                                    message: format!(
                                        "tuple index {raw_index} is outside fixed tuple length {}",
                                        elements.len()
                                    ),
                                })?;
                            Term::TupleGet {
                                tuple: Box::new(collection),
                                index,
                            }
                        } else {
                            let index = coerce_python_int(
                                self.lower(&subscript.slice, environment, result)?,
                                "tuple index",
                            )?;
                            dynamic_tuple_index_value(collection, &elements, index)?
                        }
                    }
                    Sort::VariadicTuple(_) => {
                        let index = coerce_python_int(
                            self.lower(&subscript.slice, environment, result)?,
                            "variadic tuple index",
                        )?;
                        variadic_tuple_index_value(collection, index)
                    }
                    Sort::List(_) => {
                        let index = coerce_python_int(
                            self.lower(&subscript.slice, environment, result)?,
                            "list index",
                        )?;
                        if let Term::ListComprehension {
                            source,
                            binder,
                            mapped,
                            filter: None,
                            ..
                        } = &collection
                        {
                            let source_value = list_index_value(source.as_ref().clone(), index);
                            instantiate_frontend_bound_term(mapped, binder, &source_value)?
                        } else {
                            list_index_value(collection, index)
                        }
                    }
                    Sort::Dict(key_sort, _) => {
                        let key = self.lower(&subscript.slice, environment, result)?;
                        let key = coerce_to_sort(key, &key_sort, "dictionary lookup key")?;
                        Term::DictGet {
                            dict: Box::new(collection),
                            key: Box::new(key),
                        }
                    }
                    Sort::FiniteDict(key_sort, value_sort) => {
                        let key = self.lower(&subscript.slice, environment, result)?;
                        let key = coerce_to_sort(key, &key_sort, "dictionary lookup key")?;
                        let Term::FiniteDict { entries, .. } = collection else {
                            unreachable!("finite dictionary sort came from another term")
                        };
                        finite_dict_get(
                            &entries,
                            key,
                            *value_sort,
                            &format!(
                                "{}::finite-dict-lookup::{}",
                                self.call_stack.join("::"),
                                u32::from(subscript.range.start())
                            ),
                        )?
                    }
                    Sort::Bytes => {
                        let index = coerce_python_int(
                            self.lower(&subscript.slice, environment, result)?,
                            "bytes index",
                        )?;
                        bytes_index_value(collection, index)
                    }
                    Sort::Range => lower_static_range_index(collection, &subscript.slice)?,
                    _ => return unsupported_expression(expression),
                };
                term.sort().map_err(type_failure)?;
                Ok(term)
            }
            _ => unsupported_expression(expression),
        }
    }

    fn lower_comparison_pair(
        &self,
        operator: &ast::CmpOp,
        mut left: Term,
        mut right: Term,
        expression: &ast::Expr,
    ) -> Result<Term, ContractFailure> {
        if matches!(operator, ast::CmpOp::In | ast::CmpOp::NotIn) {
            let right_sort = right.sort().map_err(type_failure)?;
            let membership = match right_sort {
                Sort::List(element) => {
                    left = coerce_to_sort(left, &element, "list membership value")?;
                    match right {
                        Term::List { values, .. } => {
                            let mut matches = Vec::with_capacity(values.len());
                            for value in values {
                                matches.push(self.lower_comparison_pair(
                                    &ast::CmpOp::Eq,
                                    left.clone(),
                                    value,
                                    expression,
                                )?);
                            }
                            Term::Or { values: matches }
                        }
                        list => Term::ListContains {
                            list: Box::new(list),
                            value: Box::new(left),
                        },
                    }
                }
                Sort::Set(element) => {
                    left = coerce_to_sort(left, &element, "set membership value")?;
                    Term::SetContains {
                        set: Box::new(right),
                        value: Box::new(left),
                    }
                }
                Sort::Dict(key, _) => {
                    left = coerce_to_sort(left, &key, "dictionary membership key")?;
                    Term::DictContains {
                        dict: Box::new(right),
                        key: Box::new(left),
                    }
                }
                Sort::FiniteDict(key, _) => {
                    left = coerce_to_sort(left, &key, "dictionary membership key")?;
                    let Term::FiniteDict { entries, .. } = right else {
                        unreachable!("finite dictionary sort came from another term")
                    };
                    finite_dict_contains(&entries, &left)
                }
                _ => {
                    right = lower_to_sequence(right).map_err(|_| ContractFailure {
                        code: "frontend.python.contracts.membership-symbolic-collection-unsupported",
                        message: "membership requires a primitive List, Set, Dict, tuple, bytes, or range value".to_owned(),
                    })?;
                    let Term::List { values, .. } = right else {
                        unreachable!()
                    };
                    let mut matches = Vec::with_capacity(values.len());
                    for value in values {
                        matches.push(self.lower_comparison_pair(
                            &ast::CmpOp::Eq,
                            left.clone(),
                            value,
                            expression,
                        )?);
                    }
                    Term::Or { values: matches }
                }
            };
            return if *operator == ast::CmpOp::NotIn {
                Ok(Term::Not {
                    value: Box::new(membership),
                })
            } else {
                Ok(membership)
            };
        }
        if matches!(operator, ast::CmpOp::Is | ast::CmpOp::IsNot) {
            if left == ellipsis_singleton() && right == ellipsis_singleton() {
                return Ok(Term::Bool {
                    value: *operator == ast::CmpOp::Is,
                });
            }
            if !self.conformance_mode {
                return failure(
                    "frontend.python.contracts.identity-operator-unsupported",
                    "Python object identity is not modeled by the production scalar fragment",
                );
            }
            let left_sort = left.sort().map_err(type_failure)?;
            let right_sort = right.sort().map_err(type_failure)?;
            if !matches!(
                (&left_sort, &right_sort),
                (Sort::Int, Sort::Int) | (Sort::Bool, Sort::Bool)
            ) {
                return failure(
                    "frontend.python.contracts.identity-type-unsupported",
                    format!(
                        "scalar conformance identity supports matching bool or integer operands only, found {left_sort:?} and {right_sort:?}"
                    ),
                );
            }
        } else if matches!(operator, ast::CmpOp::Eq | ast::CmpOp::NotEq) {
            let left_sort = left.sort().map_err(type_failure)?;
            let right_sort = right.sort().map_err(type_failure)?;
            if matches!(left_sort, Sort::FiniteDict(_, _) | Sort::DictKeys(_))
                || matches!(right_sort, Sort::FiniteDict(_, _) | Sort::DictKeys(_))
            {
                return failure(
                    "frontend.python.contracts.dict-equality-unsupported",
                    "finite dictionary and dictionary-key-view equality are outside this scalar slice",
                );
            }
            if left_sort == Sort::Bool && right_sort == Sort::Int {
                left = coerce_python_int(left, "equality left operand")?;
            } else if left_sort == Sort::Int && right_sort == Sort::Bool {
                right = coerce_python_int(right, "equality right operand")?;
            } else if left_sort != right_sort {
                return Ok(Term::Bool {
                    value: *operator == ast::CmpOp::NotEq,
                });
            }
        } else {
            left = coerce_python_int(left, "comparison left operand")?;
            right = coerce_python_int(right, "comparison right operand")?;
        }
        if *operator == ast::CmpOp::Lt
            && let Term::Subtract {
                left: upper_bound,
                right: offset,
            } = &right
            && let Term::Int { value: offset } = offset.as_ref()
        {
            left = Term::Add {
                left: Box::new(left),
                right: Box::new(Term::Int { value: *offset }),
            };
            right = upper_bound.as_ref().clone();
        }
        let (left, right) = (Box::new(left), Box::new(right));
        match operator {
            ast::CmpOp::Eq => Ok(Term::Equal { left, right }),
            ast::CmpOp::NotEq => Ok(Term::Not {
                value: Box::new(Term::Equal { left, right }),
            }),
            ast::CmpOp::Is => Ok(Term::Equal { left, right }),
            ast::CmpOp::IsNot => Ok(Term::Not {
                value: Box::new(Term::Equal { left, right }),
            }),
            ast::CmpOp::Lt => Ok(Term::Less { left, right }),
            ast::CmpOp::LtE => Ok(Term::LessEqual { left, right }),
            ast::CmpOp::Gt => Ok(Term::Greater { left, right }),
            ast::CmpOp::GtE => Ok(Term::GreaterEqual { left, right }),
            _ => unsupported_expression(expression),
        }
    }

    fn inline_call(
        &self,
        function_name: &str,
        call: &ast::ExprCall,
        environment: &BTreeMap<String, Term>,
        result: Option<&Term>,
    ) -> Result<Term, ContractFailure> {
        if self.call_stack.iter().any(|name| name == function_name) {
            return failure(
                "frontend.python.contracts.recursive-inline-call",
                format!("recursive source call {function_name:?} requires a termination contract"),
            );
        }
        let summary = &self.functions[function_name];
        if summary.ghost {
            return failure(
                "frontend.python.contracts.ghost-call-unsupported",
                format!(
                    "call to ghost function {function_name:?} requires an explicitly modeled ghost context"
                ),
            );
        }
        if summary.modular_call {
            return failure(
                "frontend.python.external.call-context-unsupported",
                format!(
                    "external call to {function_name:?} must be a complete assignment, return, or expression statement"
                ),
            );
        }
        let callee_environment =
            self.bind_call_arguments(function_name, summary, call, environment, result)?;
        if let Some(parameter) = &summary.scalar_identity_result {
            return callee_environment
                .get(parameter)
                .cloned()
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.contracts.scalar-subclass-constructor-invalid",
                    message: format!(
                        "scalar subclass constructor {function_name:?} lost parameter {parameter:?}"
                    ),
                });
        }
        let Some(expression) = summary.expression.as_ref() else {
            return Ok(Term::Unit);
        };
        let mut call_stack = self.call_stack.clone();
        call_stack.push(function_name.to_owned());
        let nested = Self {
            functions: self.functions,
            globals: self.globals,
            type_comments: self.type_comments,
            call_stack,
            exception_hierarchy: self.exception_hierarchy,
            conformance_mode: self.conformance_mode,
        };
        for (precondition_index, precondition) in summary.preconditions.iter().enumerate() {
            for (clause_index, clause) in nested
                .lower_specification_clauses(
                    precondition,
                    &callee_environment,
                    None,
                    "nested source call precondition",
                )?
                .into_iter()
                .enumerate()
            {
                ensure_boolean(&clause, "nested source call precondition")?;
                let proof = discharge(&Obligation {
                    id: format!(
                        "{function_name}:nested-call-precondition:{precondition_index}:{clause_index}"
                    ),
                    expectation: ObligationExpectation::Prove,
                    assumptions: Vec::new(),
                    conclusion: clause,
                    path: "<nested-source-call>".to_owned(),
                    byte_offset: call.range.start().into(),
                    line: 0,
                    column: 0,
                })
                .map_err(|message| ContractFailure {
                    code: "solver.translation-failed",
                    message,
                })?;
                if !proof.satisfied() {
                    return failure(
                        "frontend.python.contracts.preconditioned-call-context-unsupported",
                        format!(
                            "call to {function_name:?} has a precondition that requires caller path assumptions and must use the statement-level call proof channel"
                        ),
                    );
                }
            }
        }
        nested.lower_expected(
            expression,
            &callee_environment,
            None,
            &summary.return_sort,
            "source call result",
        )
    }

    fn bind_call_arguments(
        &self,
        function_name: &str,
        summary: &InlineFunction,
        call: &ast::ExprCall,
        environment: &BTreeMap<String, Term>,
        result: Option<&Term>,
    ) -> Result<BTreeMap<String, Term>, ContractFailure> {
        let signature = self.lower_call_signature(summary)?;
        let mut items = Vec::with_capacity(call.args.len() + call.keywords.len());
        for argument in &call.args {
            if let ast::Expr::Starred(starred) = argument {
                let expanded = self.lower(&starred.value, environment, result)?;
                let values = match &expanded {
                    Term::Tuple { values } => Some(values.clone()),
                    _ => match expanded.sort().map_err(type_failure)? {
                        Sort::Tuple(elements) => Some(
                            elements
                                .iter()
                                .enumerate()
                                .map(|(index, _)| Term::TupleGet {
                                    tuple: Box::new(expanded.clone()),
                                    index,
                                })
                                .collect(),
                        ),
                        _ => None,
                    },
                };
                if let Some(values) = values {
                    let values = values
                        .into_iter()
                        .map(|value| {
                            Ok(TypedValue::new(value.sort().map_err(type_failure)?, value))
                        })
                        .collect::<Result<Vec<_>, ContractFailure>>()?;
                    items.push(ActualItem::FixedStar(values));
                } else {
                    items.push(ActualItem::DynamicStar);
                }
            } else {
                let value = self.lower(argument, environment, result)?;
                items.push(ActualItem::Positional(TypedValue::new(
                    value.sort().map_err(type_failure)?,
                    value,
                )));
            }
        }
        for keyword in &call.keywords {
            let Some(name) = keyword.arg.as_ref() else {
                items.push(ActualItem::KeywordMapping);
                continue;
            };
            let value = self.lower(&keyword.value, environment, result)?;
            items.push(ActualItem::Named {
                name: name.to_string(),
                value: TypedValue::new(value.sort().map_err(type_failure)?, value),
            });
        }
        let binding = bind_call_with(&signature, &items, None, scalar_call_type_compatible)
            .map_err(|error| scalar_call_binding_failure(function_name, error))?;
        let mut callee_environment = summary
            .captured_environment
            .clone()
            .unwrap_or_else(|| self.globals.clone());
        for cell in binding.cells {
            let parameter_name = cell.parameter.name;
            let expected_sort = cell.parameter.expected_type;
            let value = match cell.argument {
                BoundArgument::SuppliedPositional(argument) => {
                    coerce_to_sort(argument.value.value, &expected_sort, "source call argument")?
                }
                BoundArgument::SuppliedNamed(argument) => {
                    coerce_to_sort(argument.value.value, &expected_sort, "source call argument")?
                }
                BoundArgument::Defaulted(default) => {
                    coerce_to_sort(default.value, &expected_sort, "source call default")?
                }
                BoundArgument::ResidualPositionals(arguments) => {
                    let values = arguments
                        .into_iter()
                        .map(|argument| {
                            coerce_to_sort(
                                argument.value.value,
                                &expected_sort,
                                "variadic positional argument",
                            )
                        })
                        .collect::<Result<Vec<_>, ContractFailure>>()?;
                    Term::List {
                        element_sort: expected_sort,
                        values,
                    }
                }
                BoundArgument::ResidualKeywords(arguments) => {
                    let entries = arguments
                        .into_iter()
                        .map(|argument| {
                            Ok((
                                Term::String {
                                    value: argument.name,
                                },
                                coerce_to_sort(
                                    argument.value.value,
                                    &expected_sort,
                                    "variadic keyword argument",
                                )?,
                            ))
                        })
                        .collect::<Result<Vec<_>, ContractFailure>>()?;
                    Term::FiniteDict {
                        key_sort: Sort::String,
                        value_sort: expected_sort,
                        entries,
                    }
                }
            };
            match cell.kind {
                ParameterKind::PositionalOnly
                | ParameterKind::Positional
                | ParameterKind::KeywordOnly
                | ParameterKind::VarArgs
                | ParameterKind::KeywordArgs => {
                    value.sort().map_err(type_failure)?;
                    callee_environment.insert(parameter_name, value);
                }
            }
        }
        Ok(callee_environment)
    }

    fn lower_call_signature(
        &self,
        summary: &InlineFunction,
    ) -> Result<CallSignature<Sort, Term>, ContractFailure> {
        let mut signature = CallSignature::default();
        let definition_environment = summary
            .captured_environment
            .as_ref()
            .unwrap_or(self.globals);
        for parameter in &summary.positional_parameters {
            let formal = self.lower_formal_parameter(parameter, definition_environment)?;
            if parameter.positional_only {
                signature.positional_only.push(formal);
            } else {
                signature.positional.push(formal);
            }
        }
        signature.keyword_only = summary
            .keyword_only_parameters
            .iter()
            .map(|parameter| self.lower_formal_parameter(parameter, definition_environment))
            .collect::<Result<Vec<_>, _>>()?;
        signature.var_args = summary
            .var_args
            .as_ref()
            .map(|(name, sort)| FormalParameter::required(name.clone(), sort.clone()));
        signature.keyword_args = summary
            .keyword_args
            .as_ref()
            .map(|(name, sort)| FormalParameter::required(name.clone(), sort.clone()));
        Ok(signature)
    }

    fn lower_formal_parameter(
        &self,
        parameter: &InlineParameter,
        definition_environment: &BTreeMap<String, Term>,
    ) -> Result<FormalParameter<Sort, Term>, ContractFailure> {
        if let Some(default) = &parameter.default {
            let value = self.lower_spec(
                default,
                definition_environment,
                None,
                "source function default",
            )?;
            let value = coerce_to_sort(value, &parameter.sort, "source function default")?;
            Ok(FormalParameter::defaulted(
                parameter.name.clone(),
                parameter.sort.clone(),
                TypedValue::new(parameter.sort.clone(), value),
            ))
        } else {
            Ok(FormalParameter::required(
                parameter.name.clone(),
                parameter.sort.clone(),
            ))
        }
    }
}

fn scalar_call_type_compatible(expected: &Sort, actual: &Sort) -> bool {
    expected == actual
        || (*expected == Sort::Int && *actual == Sort::Bool)
        || matches!(
            (expected, actual),
            (Sort::VariadicTuple(element), Sort::Tuple(elements))
                if elements.iter().all(|actual| scalar_call_type_compatible(element, actual))
        )
}

fn scalar_call_binding_failure(function_name: &str, error: BindingError<Sort>) -> ContractFailure {
    let (code, detail) = match error {
        BindingError::MalformedSignature(error) => (
            "frontend.python.contracts.call-signature-invalid",
            format!("invalid signature: {error:?}"),
        ),
        BindingError::DynamicStarUnsupported { item_index } => (
            "frontend.python.contracts.call-star-dynamic-unsupported",
            format!("argument {item_index} uses an unknown-length star expansion"),
        ),
        BindingError::KeywordMappingUnsupported { item_index } => (
            "frontend.python.contracts.call-keyword-star-dynamic-unsupported",
            format!("argument {item_index} uses an unsupported **mapping expansion"),
        ),
        BindingError::SourceExpressionCountOverflow {
            item_count,
            receiver_count,
        } => (
            "frontend.python.contracts.call-source-count-overflow",
            format!(
                "call source count overflows usize: {item_count} explicit items plus {receiver_count} receiver"
            ),
        ),
        BindingError::ExpandedArgumentCountOverflow {
            item_index,
            accumulated,
            contribution,
        } => (
            "frontend.python.contracts.call-expanded-count-overflow",
            format!(
                "argument {item_index} adds {contribution} values after {accumulated}, overflowing usize"
            ),
        ),
        BindingError::AllocationFailed { site, requested } => (
            "frontend.python.contracts.call-binding-allocation-failed",
            format!("could not allocate {requested} entries for {site:?}"),
        ),
        BindingError::DuplicateNamedArgument { name } => (
            "frontend.python.contracts.call-argument-duplicate",
            format!("keyword {name:?} is supplied more than once"),
        ),
        BindingError::DuplicateBinding { parameter } => (
            "frontend.python.contracts.call-argument-duplicate",
            format!("parameter {parameter:?} is supplied by position and name"),
        ),
        BindingError::TooManyPositionals { expected, actual } => (
            "frontend.python.contracts.call-argument-excess",
            format!("received {actual} positional values, but at most {expected} are accepted"),
        ),
        BindingError::UnexpectedKeyword { name } => (
            "frontend.python.contracts.call-keyword-unexpected",
            format!("keyword {name:?} does not name a parameter"),
        ),
        BindingError::MissingRequiredArgument { parameter } => (
            "frontend.python.contracts.call-argument-missing",
            format!("required parameter {parameter:?} was not supplied"),
        ),
        BindingError::TypeMismatch {
            parameter,
            expected,
            actual,
            ..
        } => (
            "frontend.python.contracts.type-mismatch",
            format!("parameter {parameter:?} expects {expected:?}, found {actual:?}"),
        ),
    };
    ContractFailure {
        code,
        message: format!("call to {function_name:?}: {detail}"),
    }
}

fn finite_dict_contains(entries: &[(Term, Term)], key: &Term) -> Term {
    Term::Or {
        values: entries
            .iter()
            .map(|(candidate, _)| Term::Equal {
                left: Box::new(key.clone()),
                right: Box::new(candidate.clone()),
            })
            .collect(),
    }
}

fn finite_dict_get(
    entries: &[(Term, Term)],
    key: Term,
    value_sort: Sort,
    missing_value_name: &str,
) -> Result<Term, ContractFailure> {
    let mut value = Term::Variable {
        name: missing_value_name.to_owned(),
        sort: value_sort,
    };
    for (candidate, candidate_value) in entries.iter().rev() {
        value = Term::IfThenElse {
            condition: Box::new(Term::Equal {
                left: Box::new(key.clone()),
                right: Box::new(candidate.clone()),
            }),
            then_value: Box::new(candidate_value.clone()),
            else_value: Box::new(value),
        };
    }
    value.sort().map_err(type_failure)?;
    Ok(value)
}

fn term_contains_list_get(term: &Term) -> bool {
    match term {
        Term::ListGet { .. } | Term::BytesGet { .. } | Term::VariadicTupleGet { .. } => true,
        Term::FieldRead { receiver, .. }
        | Term::PermissionAtLeast { receiver, .. }
        | Term::PermissionAtMost { receiver, .. }
        | Term::PermissionPositive { receiver, .. }
        | Term::Not { value: receiver }
        | Term::Negate { value: receiver }
        | Term::FloorDivideByPositive {
            value: receiver, ..
        }
        | Term::StringLength { value: receiver }
        | Term::BytesLength { value: receiver }
        | Term::RuntimeClass { value: receiver }
        | Term::IntEnumValue {
            value: receiver, ..
        }
        | Term::IntEnumProjection { value: receiver }
        | Term::IntEnumDomain { value: receiver }
        | Term::TupleGet {
            tuple: receiver, ..
        }
        | Term::VariadicTupleLength { value: receiver }
        | Term::VariadicTupleSlice {
            source: receiver, ..
        }
        | Term::ListSlice {
            source: receiver, ..
        }
        | Term::ListSum { source: receiver }
        | Term::ListSorted { source: receiver }
        | Term::ListLength { value: receiver }
        | Term::SetLength { value: receiver }
        | Term::DictLength { value: receiver }
        | Term::ForAll { body: receiver, .. } => term_contains_list_get(receiver),
        Term::Implies { left, right }
        | Term::Equal { left, right }
        | Term::Less { left, right }
        | Term::LessEqual { left, right }
        | Term::Greater { left, right }
        | Term::GreaterEqual { left, right }
        | Term::Add { left, right }
        | Term::Subtract { left, right }
        | Term::Multiply { left, right }
        | Term::ListConcat { left, right }
        | Term::IntEnumIdentity { left, right }
        | Term::ListContains {
            list: left,
            value: right,
        }
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
        } => term_contains_list_get(left) || term_contains_list_get(right),
        Term::ClassSubtype { actual, expected } => {
            term_contains_list_get(actual) || term_contains_list_get(expected)
        }
        Term::IfThenElse {
            condition,
            then_value,
            else_value,
        } => {
            term_contains_list_get(condition)
                || term_contains_list_get(then_value)
                || term_contains_list_get(else_value)
        }
        Term::And { values }
        | Term::Or { values }
        | Term::StringConcat { values }
        | Term::BytesConcat { values }
        | Term::Tuple { values }
        | Term::VariadicTuple { values, .. }
        | Term::List { values, .. }
        | Term::DictKeys { values, .. }
        | Term::PredicateInstance {
            arguments: values, ..
        } => values.iter().any(term_contains_list_get),
        Term::FiniteDict { entries, .. } => entries
            .iter()
            .any(|(key, value)| term_contains_list_get(key) || term_contains_list_get(value)),
        Term::PermissionMaskTransition {
            consumed, produced, ..
        } => consumed
            .iter()
            .chain(produced)
            .any(|amount| term_contains_list_get(&amount.receiver)),
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
            term_contains_list_get(source)
                || term_contains_list_get(mapped)
                || filter.as_deref().is_some_and(term_contains_list_get)
        }
        Term::DictComprehension {
            source,
            key,
            value,
            filter,
            ..
        } => {
            term_contains_list_get(source)
                || term_contains_list_get(key)
                || term_contains_list_get(value)
                || filter.as_deref().is_some_and(term_contains_list_get)
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
        | Term::PermissionMaskValid { .. }
        | Term::Variable { .. } => false,
    }
}

fn revealed_source_call(expression: &ast::Expr) -> Option<&ast::ExprCall> {
    let ast::Expr::Call(reveal) = expression else {
        return None;
    };
    if !reveal.keywords.is_empty() || reveal.args.len() != 1 {
        return None;
    }
    let ast::Expr::Name(reveal_name) = reveal.func.as_ref() else {
        return None;
    };
    if reveal_name.id.as_str() != "Reveal" {
        return None;
    }
    let ast::Expr::Call(source_call) = &reveal.args[0] else {
        return None;
    };
    matches!(source_call.func.as_ref(), ast::Expr::Name(_)).then_some(source_call)
}

fn expand_revealed_selection(
    declarations: &[&ast::StmtFunctionDef],
    selected: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut expanded = selected.clone();
    loop {
        let mut discovered = BTreeSet::new();
        for declaration in declarations {
            if expanded.contains(declaration.name.as_str()) {
                collect_revealed_targets(&declaration.body, &mut discovered);
            }
        }
        let previous_len = expanded.len();
        expanded.extend(discovered);
        if expanded.len() == previous_len {
            return expanded;
        }
    }
}

fn collect_revealed_targets(statements: &[ast::Stmt], targets: &mut BTreeSet<String>) {
    for statement in statements {
        let expression = match statement {
            ast::Stmt::Assign(assignment) => Some(assignment.value.as_ref()),
            ast::Stmt::AnnAssign(assignment) => assignment.value.as_deref(),
            ast::Stmt::Expr(expression) => Some(expression.value.as_ref()),
            ast::Stmt::Return(return_statement) => return_statement.value.as_deref(),
            ast::Stmt::If(branch) => {
                collect_revealed_targets(&branch.body, targets);
                collect_revealed_targets(&branch.orelse, targets);
                None
            }
            ast::Stmt::While(loop_statement) => {
                collect_revealed_targets(&loop_statement.body, targets);
                collect_revealed_targets(&loop_statement.orelse, targets);
                None
            }
            ast::Stmt::Try(try_statement) => {
                collect_revealed_targets(&try_statement.body, targets);
                collect_revealed_targets(&try_statement.orelse, targets);
                collect_revealed_targets(&try_statement.finalbody, targets);
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    collect_revealed_targets(&handler.body, targets);
                }
                None
            }
            _ => None,
        };
        if let Some(call) = expression.and_then(revealed_source_call)
            && let ast::Expr::Name(name) = call.func.as_ref()
        {
            targets.insert(name.id.to_string());
        }
    }
}

fn lower_constant_string_format(
    template: Term,
    arguments: &[Term],
    original: &ast::Expr,
) -> Result<Term, ContractFailure> {
    let Term::String { value: template } = template else {
        return unsupported_expression(original);
    };
    let rendered = if template.is_empty() && arguments.is_empty() {
        String::new()
    } else if template == "{0}" && arguments.len() == 1 {
        render_constant_as_string(&arguments[0]).ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.format-nonconstant",
            message: "str.format currently requires primitive constant arguments".to_owned(),
        })?
    } else {
        return unsupported_expression(original);
    };
    Ok(Term::String { value: rendered })
}

fn render_constant_as_string(term: &Term) -> Option<String> {
    match term {
        Term::String { value } => Some(value.clone()),
        Term::Int { value } => Some(value.to_string()),
        Term::Bool { value: true } => Some("True".to_owned()),
        Term::Bool { value: false } => Some("False".to_owned()),
        _ => None,
    }
}

fn constant_tuple_index(expression: &ast::Expr) -> Option<i128> {
    match expression {
        ast::Expr::Constant(constant) => {
            let ast::Constant::Int(value) = &constant.value else {
                return None;
            };
            value.to_string().parse().ok()
        }
        ast::Expr::UnaryOp(unary) if unary.op == ast::UnaryOp::USub => {
            let ast::Expr::Constant(constant) = unary.operand.as_ref() else {
                return None;
            };
            let ast::Constant::Int(value) = &constant.value else {
                return None;
            };
            value.to_string().parse::<i128>().ok()?.checked_neg()
        }
        _ => None,
    }
}

fn lower_static_slice(collection: Term, slice: &ast::ExprSlice) -> Result<Term, ContractFailure> {
    match collection {
        Term::List {
            element_sort,
            values,
        } => {
            let indices = static_slice_indices(slice, values.len())?;
            Ok(Term::List {
                element_sort,
                values: indices
                    .into_iter()
                    .map(|index| values[index].clone())
                    .collect(),
            })
        }
        Term::Tuple { values } => {
            let indices = static_slice_indices(slice, values.len())?;
            Ok(Term::Tuple {
                values: indices
                    .into_iter()
                    .map(|index| values[index].clone())
                    .collect(),
            })
        }
        tuple if matches!(tuple.sort().map_err(type_failure)?, Sort::VariadicTuple(_)) => {
            let lower = static_slice_bound(
                slice.lower.as_deref(),
                "frontend.python.contracts.slice-bound-unsupported",
                "slice lower bound must be an integer literal or omitted",
            )?;
            let upper = static_slice_bound(
                slice.upper.as_deref(),
                "frontend.python.contracts.slice-bound-unsupported",
                "slice upper bound must be an integer literal or omitted",
            )?;
            let step = static_slice_bound(
                slice.step.as_deref(),
                "frontend.python.contracts.slice-step-unsupported",
                "slice step must be an integer literal",
            )?
            .unwrap_or(1);
            let step = NonZeroI128::new(step).ok_or_else(|| ContractFailure {
                code: "frontend.python.contracts.slice-step-zero",
                message: "slice step zero raises ValueError".to_owned(),
            })?;
            Ok(Term::VariadicTupleSlice {
                source: Box::new(tuple),
                lower,
                upper,
                step,
            })
        }
        Term::Bytes { values } => {
            let indices = static_slice_indices(slice, values.len())?;
            Ok(Term::Bytes {
                values: indices.into_iter().map(|index| values[index]).collect(),
            })
        }
        Term::Range { values } => {
            let indices = static_slice_indices(slice, values.len())?;
            Ok(Term::Range {
                values: indices.into_iter().map(|index| values[index]).collect(),
            })
        }
        Term::String { value } => {
            let characters = value.chars().collect::<Vec<_>>();
            let indices = static_slice_indices(slice, characters.len())?;
            Ok(Term::String {
                value: indices.into_iter().map(|index| characters[index]).collect(),
            })
        }
        _ => failure(
            "frontend.python.contracts.slice-symbolic-sequence-unsupported",
            "slicing currently requires a statically known sequence or a homogeneous variadic tuple",
        ),
    }
}

fn static_slice_indices(
    slice: &ast::ExprSlice,
    length: usize,
) -> Result<Vec<usize>, ContractFailure> {
    let length = i128::try_from(length).map_err(|_| ContractFailure {
        code: "frontend.python.contracts.sequence-length-overflow",
        message: "sequence length exceeds the current signed slice frontend".to_owned(),
    })?;
    let step = static_slice_bound(
        slice.step.as_deref(),
        "frontend.python.contracts.slice-step-unsupported",
        "slice step must be an integer literal",
    )?
    .unwrap_or(1);
    if step == 0 {
        return failure(
            "frontend.python.contracts.slice-step-zero",
            "slice step zero raises ValueError",
        );
    }
    let explicit_start = static_slice_bound(
        slice.lower.as_deref(),
        "frontend.python.contracts.slice-bound-unsupported",
        "slice lower bound must be an integer literal or omitted",
    )?;
    let explicit_stop = static_slice_bound(
        slice.upper.as_deref(),
        "frontend.python.contracts.slice-bound-unsupported",
        "slice upper bound must be an integer literal or omitted",
    )?;
    let normalize_positive = |value: i128| {
        let adjusted = if value < 0 {
            value.saturating_add(length)
        } else {
            value
        };
        adjusted.clamp(0, length)
    };
    let normalize_negative = |value: i128| {
        let adjusted = if value < 0 {
            value.saturating_add(length)
        } else {
            value
        };
        adjusted.clamp(-1, length.saturating_sub(1))
    };
    let (mut current, stop) = if step > 0 {
        (
            normalize_positive(explicit_start.unwrap_or(0)),
            normalize_positive(explicit_stop.unwrap_or(length)),
        )
    } else {
        (
            explicit_start.map_or(length - 1, normalize_negative),
            explicit_stop.map_or(-1, normalize_negative),
        )
    };
    let mut indices = Vec::new();
    while if step > 0 {
        current < stop
    } else {
        current > stop
    } {
        let index = usize::try_from(current).map_err(|_| ContractFailure {
            code: "frontend.python.contracts.slice-index-overflow",
            message: "normalized slice index exceeds the current usize frontend".to_owned(),
        })?;
        indices.push(index);
        current = current.checked_add(step).ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.slice-index-overflow",
            message: "slice iteration overflowed the current signed frontend".to_owned(),
        })?;
    }
    Ok(indices)
}

fn static_slice_bound(
    expression: Option<&ast::Expr>,
    code: &'static str,
    message: &str,
) -> Result<Option<i128>, ContractFailure> {
    expression
        .map(|expression| {
            constant_tuple_index(expression).ok_or_else(|| ContractFailure {
                code,
                message: message.to_owned(),
            })
        })
        .transpose()
}

fn lower_static_range_index(collection: Term, index: &ast::Expr) -> Result<Term, ContractFailure> {
    let Term::Range { values } = collection else {
        return failure(
            "frontend.python.contracts.range-index-symbolic-unsupported",
            "range indexing currently requires a statically known value",
        );
    };
    lower_static_integer_sequence_index(values, index, "range")
}

fn lower_bytes_repeat(bytes: Term, count: Term) -> Result<Term, ContractFailure> {
    let count = static_python_int_value(&count).ok_or_else(|| ContractFailure {
        code: "frontend.python.contracts.bytes-repeat-symbolic-count-unsupported",
        message: "bytes repetition currently requires a statically known integer count".to_owned(),
    })?;
    if count <= 0 {
        return Ok(Term::BytesConcat { values: Vec::new() });
    }
    let count = usize::try_from(count).map_err(|_| ContractFailure {
        code: "frontend.python.contracts.bytes-repeat-count-overflow",
        message: "bytes repetition count exceeds the current usize frontend".to_owned(),
    })?;
    let mut values = Vec::new();
    reserve_scalar_expansion(
        &mut values,
        count,
        "frontend.python.contracts.bytes-repeat-allocation-failed",
        "bytes repetition",
    )?;
    values.extend(std::iter::repeat_n(bytes, count));
    Ok(Term::BytesConcat { values })
}

fn reserve_scalar_expansion<T>(
    values: &mut Vec<T>,
    additional: usize,
    code: &'static str,
    expansion: &str,
) -> Result<(), ContractFailure> {
    values
        .try_reserve_exact(additional)
        .map_err(|error| ContractFailure {
            code,
            message: format!(
                "{expansion} could not reserve space for {additional} elements: {error}"
            ),
        })
}

fn lower_nonnegative_integer_power(base: Term, exponent: Term) -> Result<Term, ContractFailure> {
    let base = coerce_python_int(base, "power base")?;
    let exponent = static_python_int_value(&exponent).ok_or_else(|| ContractFailure {
        code: "frontend.python.contracts.power-symbolic-exponent-unsupported",
        message: "integer power currently requires a statically known exponent".to_owned(),
    })?;
    if exponent < 0 {
        return failure(
            "frontend.python.contracts.power-negative-exponent-unsupported",
            "a negative Python exponent produces a non-integer result outside the scalar integer fragment",
        );
    }
    let exponent = usize::try_from(exponent).map_err(|_| ContractFailure {
        code: "frontend.python.contracts.power-exponent-overflow",
        message: "integer power exponent exceeds the current usize frontend".to_owned(),
    })?;
    if exponent > 64 {
        return failure(
            "frontend.python.contracts.power-expansion-limit",
            "integer power exceeds the 64-multiplication proof expansion limit",
        );
    }
    let mut result = Term::Int { value: 1 };
    for _ in 0..exponent {
        result = Term::Multiply {
            left: Box::new(result),
            right: Box::new(base.clone()),
        };
    }
    Ok(result)
}

fn lower_integer_abs(value: Term) -> Term {
    Term::IfThenElse {
        condition: Box::new(Term::Less {
            left: Box::new(value.clone()),
            right: Box::new(Term::Int { value: 0 }),
        }),
        then_value: Box::new(Term::Negate {
            value: Box::new(value.clone()),
        }),
        else_value: Box::new(value),
    }
}

fn lower_integer_extremum(function: &str, values: Vec<Term>) -> Result<Term, ContractFailure> {
    let mut values = values.into_iter();
    let mut selected = values.next().ok_or_else(|| ContractFailure {
        code: "frontend.python.contracts.extremum-empty",
        message: format!(
            "{function} over an empty iterable would raise ValueError; this partial call requires an explicit modeled exception path"
        ),
    })?;
    for value in values {
        let value = coerce_python_int(value, "min/max value")?;
        let condition = match function {
            "min" => Term::LessEqual {
                left: Box::new(selected.clone()),
                right: Box::new(value.clone()),
            },
            "max" => Term::GreaterEqual {
                left: Box::new(selected.clone()),
                right: Box::new(value.clone()),
            },
            _ => {
                return failure(
                    "frontend.python.contracts.extremum-name-unsupported",
                    format!("unsupported integer extremum {function:?}"),
                );
            }
        };
        selected = Term::IfThenElse {
            condition: Box::new(condition),
            then_value: Box::new(selected),
            else_value: Box::new(value),
        };
    }
    Ok(selected)
}

fn static_python_int_value(value: &Term) -> Option<i64> {
    match value {
        Term::Int { value } => Some(*value),
        Term::Bool { value } => Some(i64::from(*value)),
        Term::Negate { value } => static_python_int_value(value)?.checked_neg(),
        Term::IfThenElse {
            condition,
            then_value,
            else_value,
        } => match condition.as_ref() {
            Term::Bool { value: true } => static_python_int_value(then_value),
            Term::Bool { value: false } => static_python_int_value(else_value),
            _ => None,
        },
        _ => None,
    }
}

fn lower_bytes_join(separator: Term, values: Term) -> Result<Term, ContractFailure> {
    if separator.sort().map_err(type_failure)? != Sort::Bytes {
        return failure(
            "frontend.python.contracts.bytes-join-separator-type",
            "bytes.join requires a bytes receiver",
        );
    }
    let Term::List {
        element_sort,
        values,
    } = values
    else {
        return failure(
            "frontend.python.contracts.bytes-join-symbolic-list-unsupported",
            "bytes.join currently requires a statically shaped List[bytes] value",
        );
    };
    if element_sort != Sort::Bytes {
        return failure(
            "frontend.python.contracts.bytes-join-element-type",
            format!("bytes.join requires List[bytes], found List[{element_sort:?}]"),
        );
    }
    let mut concatenated = Vec::with_capacity(values.len().saturating_mul(2).saturating_sub(1));
    for (index, value) in values.into_iter().enumerate() {
        if index > 0 {
            concatenated.push(separator.clone());
        }
        concatenated.push(value);
    }
    Ok(Term::BytesConcat {
        values: concatenated,
    })
}

fn lower_static_integer_sequence_index(
    values: Vec<i64>,
    index: &ast::Expr,
    kind: &str,
) -> Result<Term, ContractFailure> {
    let raw = constant_tuple_index(index).ok_or_else(|| ContractFailure {
        code: "frontend.python.contracts.sequence-index-symbolic-unsupported",
        message: format!("{kind} indexing currently requires an integer literal"),
    })?;
    let length = i128::try_from(values.len()).map_err(|_| ContractFailure {
        code: "frontend.python.contracts.sequence-length-overflow",
        message: format!("{kind} length exceeds the current signed index frontend"),
    })?;
    let normalized = if raw < 0 {
        raw.checked_add(length)
    } else {
        Some(raw)
    };
    let value = normalized
        .filter(|value| *value >= 0 && *value < length)
        .and_then(|value| usize::try_from(value).ok())
        .and_then(|value| values.get(value).copied())
        // The guard creates an explicit IndexError path. The normal path is inconsistent for an
        // out-of-bounds literal, so this placeholder cannot affect a reachable proof state.
        .unwrap_or(0);
    Ok(Term::Int { value })
}

fn lower_to_sequence(value: Term) -> Result<Term, ContractFailure> {
    match value {
        value @ Term::List { .. } => Ok(value),
        Term::DictKeys { key_sort, values } => Ok(Term::List {
            element_sort: key_sort,
            values,
        }),
        Term::FiniteDict {
            key_sort, entries, ..
        } => Ok(Term::List {
            element_sort: key_sort,
            values: entries.into_iter().map(|(key, _)| key).collect(),
        }),
        Term::Bytes { values } => Ok(Term::List {
            element_sort: Sort::Int,
            values: values
                .into_iter()
                .map(|value| Term::Int {
                    value: i64::from(value),
                })
                .collect(),
        }),
        Term::Range { values } => Ok(Term::List {
            element_sort: Sort::Int,
            values: values
                .into_iter()
                .map(|value| Term::Int { value })
                .collect(),
        }),
        Term::Tuple { values } => {
            let Some(first) = values.first() else {
                return failure(
                    "frontend.python.contracts.toseq-empty-tuple-unsupported",
                    "ToSeq on an empty tuple requires an element-type context",
                );
            };
            let element_sort = first.sort().map_err(type_failure)?;
            if values
                .iter()
                .any(|value| value.sort().map_or(true, |sort| sort != element_sort))
            {
                return failure(
                    "frontend.python.contracts.toseq-heterogeneous-tuple",
                    "ToSeq requires a homogeneous fixed tuple",
                );
            }
            Ok(Term::List {
                element_sort,
                values,
            })
        }
        Term::VariadicTuple {
            element_sort,
            values,
        } => Ok(Term::List {
            element_sort,
            values,
        }),
        _ => failure(
            "frontend.python.contracts.toseq-type-unsupported",
            "ToSeq requires a list, tuple, bytes, or range value",
        ),
    }
}

fn finite_literal_forall(call: &ast::ExprCall) -> Option<(&ast::Expr, &str, &ast::Expr)> {
    if !call.keywords.is_empty() || call.args.len() != 2 {
        return None;
    }
    let ast::Expr::Lambda(lambda) = &call.args[1] else {
        return None;
    };
    if !lambda.args.posonlyargs.is_empty()
        || lambda.args.args.len() != 1
        || lambda.args.vararg.is_some()
        || !lambda.args.kwonlyargs.is_empty()
        || lambda.args.kwarg.is_some()
        || lambda.args.args[0].default.is_some()
        || lambda.args.args[0].def.annotation.is_some()
    {
        return None;
    }
    let ast::Expr::Tuple(body) = lambda.body.as_ref() else {
        return None;
    };
    if body.elts.len() != 2
        || !matches!(&body.elts[1], ast::Expr::List(triggers) if triggers.elts.is_empty())
    {
        return None;
    }
    Some((
        &call.args[0],
        lambda.args.args[0].def.arg.as_str(),
        &body.elts[0],
    ))
}

fn typed_integer_forall(call: &ast::ExprCall) -> Option<(&str, &ast::Expr, Vec<&ast::Expr>)> {
    if !call.keywords.is_empty()
        || call.args.len() != 2
        || !matches!(&call.args[0], ast::Expr::Name(name) if name.id.as_str() == "int")
    {
        return None;
    }
    let ast::Expr::Lambda(lambda) = &call.args[1] else {
        return None;
    };
    if !lambda.args.posonlyargs.is_empty()
        || lambda.args.args.len() != 1
        || lambda.args.vararg.is_some()
        || !lambda.args.kwonlyargs.is_empty()
        || lambda.args.kwarg.is_some()
        || lambda.args.args[0].default.is_some()
        || lambda.args.args[0].def.annotation.is_some()
    {
        return None;
    }
    let ast::Expr::Tuple(body) = lambda.body.as_ref() else {
        return None;
    };
    if body.elts.len() != 2 {
        return None;
    }
    let ast::Expr::List(groups) = &body.elts[1] else {
        return None;
    };
    if groups.elts.is_empty() {
        return None;
    }
    let mut triggers = Vec::new();
    for group in &groups.elts {
        let ast::Expr::List(group) = group else {
            return None;
        };
        if group.elts.is_empty() {
            return None;
        }
        for trigger in &group.elts {
            if !quantifier_trigger_is_read_only(trigger, lambda.args.args[0].def.arg.as_str()) {
                return None;
            }
            triggers.push(trigger);
        }
    }
    Some((
        lambda.args.args[0].def.arg.as_str(),
        &body.elts[0],
        triggers,
    ))
}

fn looks_like_typed_integer_forall(call: &ast::ExprCall) -> bool {
    call.keywords.is_empty()
        && call.args.len() == 2
        && matches!(&call.args[0], ast::Expr::Name(name) if name.id.as_str() == "int")
        && matches!(&call.args[1], ast::Expr::Lambda(_))
}

fn typed_integer_forall_is_guarded(call: &ast::ExprCall) -> bool {
    typed_integer_forall(call)
        .is_some_and(|(binder, predicate, _)| quantified_subscripts_are_guarded(predicate, binder))
}

fn typed_integer_forall_expression_is_guarded(expression: &ast::Expr) -> bool {
    matches!(expression, ast::Expr::Call(call) if typed_integer_forall_is_guarded(call))
}

fn quantified_subscripts_are_guarded(predicate: &ast::Expr, binder: &str) -> bool {
    let ast::Expr::Call(implies) = predicate else {
        return !contains_binder_subscript(predicate, binder);
    };
    if !matches!(implies.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Implies")
        || implies.args.len() != 2
        || !implies.keywords.is_empty()
    {
        return !contains_binder_subscript(predicate, binder);
    }
    let mut indexed_subscripts = Vec::new();
    if !collect_binder_subscripts(&implies.args[1], binder, &mut indexed_subscripts)
        || indexed_subscripts.is_empty()
    {
        return false;
    }
    indexed_subscripts.into_iter().all(|subscript| {
        guard_implies_index_nonnegative(&implies.args[0], binder, subscript.offset)
            && guard_implies_index_below_length(&implies.args[0], binder, subscript.offset)
    })
}

#[derive(Clone, Copy)]
struct BinderSubscript {
    offset: i128,
}

fn collect_binder_subscripts(
    expression: &ast::Expr,
    binder: &str,
    subscripts: &mut Vec<BinderSubscript>,
) -> bool {
    match expression {
        ast::Expr::Subscript(subscript) => {
            if expression_contains_name(&subscript.slice, binder) {
                let Some(offset) = binder_index_offset(&subscript.slice, binder) else {
                    return false;
                };
                subscripts.push(BinderSubscript { offset });
            }
            collect_binder_subscripts(&subscript.value, binder, subscripts)
                && collect_binder_subscripts(&subscript.slice, binder, subscripts)
        }
        ast::Expr::BoolOp(operation) => operation
            .values
            .iter()
            .all(|value| collect_binder_subscripts(value, binder, subscripts)),
        ast::Expr::Call(call) => {
            collect_binder_subscripts(&call.func, binder, subscripts)
                && call
                    .args
                    .iter()
                    .all(|argument| collect_binder_subscripts(argument, binder, subscripts))
                && call
                    .keywords
                    .iter()
                    .all(|keyword| collect_binder_subscripts(&keyword.value, binder, subscripts))
        }
        ast::Expr::Compare(comparison) => {
            collect_binder_subscripts(&comparison.left, binder, subscripts)
                && comparison
                    .comparators
                    .iter()
                    .all(|value| collect_binder_subscripts(value, binder, subscripts))
        }
        ast::Expr::BinOp(operation) => {
            collect_binder_subscripts(&operation.left, binder, subscripts)
                && collect_binder_subscripts(&operation.right, binder, subscripts)
        }
        ast::Expr::UnaryOp(operation) => {
            collect_binder_subscripts(&operation.operand, binder, subscripts)
        }
        ast::Expr::IfExp(conditional) => {
            collect_binder_subscripts(&conditional.test, binder, subscripts)
                && collect_binder_subscripts(&conditional.body, binder, subscripts)
                && collect_binder_subscripts(&conditional.orelse, binder, subscripts)
        }
        _ => true,
    }
}

fn expression_contains_name(expression: &ast::Expr, name: &str) -> bool {
    match expression {
        ast::Expr::Name(candidate) => candidate.id.as_str() == name,
        ast::Expr::BinOp(operation) => {
            expression_contains_name(&operation.left, name)
                || expression_contains_name(&operation.right, name)
        }
        ast::Expr::UnaryOp(operation) => expression_contains_name(&operation.operand, name),
        _ => false,
    }
}

fn binder_index_offset(expression: &ast::Expr, binder: &str) -> Option<i128> {
    match expression {
        ast::Expr::Name(name) if name.id.as_str() == binder => Some(0),
        ast::Expr::BinOp(operation) if operation.op == ast::Operator::Add => {
            if matches!(operation.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binder)
            {
                constant_tuple_index(&operation.right)
            } else if matches!(operation.right.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binder)
            {
                constant_tuple_index(&operation.left)
            } else {
                None
            }
        }
        ast::Expr::BinOp(operation) if operation.op == ast::Operator::Sub => {
            if matches!(operation.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binder)
            {
                constant_tuple_index(&operation.right)?.checked_neg()
            } else {
                None
            }
        }
        _ => None,
    }
}

fn quantifier_trigger_is_read_only(expression: &ast::Expr, binder: &str) -> bool {
    match expression {
        ast::Expr::Name(_) => true,
        ast::Expr::Subscript(subscript) => {
            matches!(
                subscript.value.as_ref(),
                ast::Expr::Name(_) | ast::Expr::Call(_)
            ) && matches!(subscript.slice.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binder)
                && match subscript.value.as_ref() {
                    ast::Expr::Name(_) => true,
                    ast::Expr::Call(call) => {
                        matches!(call.func.as_ref(), ast::Expr::Name(name) if matches!(name.id.as_str(), "Result" | "ResultT"))
                            && call.keywords.is_empty()
                            && (call.args.is_empty() || name_is_type_annotation(call.args.first()))
                    }
                    _ => false,
                }
        }
        _ => false,
    }
}

fn name_is_type_annotation(expression: Option<&ast::Expr>) -> bool {
    expression.is_some_and(|expression| annotation_sort(Some(expression)).is_ok())
}

fn contains_binder_subscript(expression: &ast::Expr, binder: &str) -> bool {
    let mut collections = Vec::new();
    collect_binder_subscript_collections(expression, binder, &mut collections);
    !collections.is_empty()
}

fn collect_binder_subscript_collections<'a>(
    expression: &'a ast::Expr,
    binder: &str,
    collections: &mut Vec<&'a ast::Expr>,
) {
    match expression {
        ast::Expr::Subscript(subscript) if matches!(subscript.slice.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binder) =>
        {
            collections.push(&subscript.value);
        }
        ast::Expr::BoolOp(operation) => {
            for value in &operation.values {
                collect_binder_subscript_collections(value, binder, collections);
            }
        }
        ast::Expr::Call(call) => {
            for argument in &call.args {
                collect_binder_subscript_collections(argument, binder, collections);
            }
        }
        ast::Expr::Compare(comparison) => {
            collect_binder_subscript_collections(&comparison.left, binder, collections);
            for value in &comparison.comparators {
                collect_binder_subscript_collections(value, binder, collections);
            }
        }
        ast::Expr::BinOp(operation) => {
            collect_binder_subscript_collections(&operation.left, binder, collections);
            collect_binder_subscript_collections(&operation.right, binder, collections);
        }
        ast::Expr::UnaryOp(operation) => {
            collect_binder_subscript_collections(&operation.operand, binder, collections)
        }
        ast::Expr::IfExp(conditional) => {
            collect_binder_subscript_collections(&conditional.test, binder, collections);
            collect_binder_subscript_collections(&conditional.body, binder, collections);
            collect_binder_subscript_collections(&conditional.orelse, binder, collections);
        }
        _ => {}
    }
}

fn guard_conjuncts(expression: &ast::Expr) -> Vec<&ast::Expr> {
    match expression {
        ast::Expr::BoolOp(operation) if operation.op == ast::BoolOp::And => {
            operation.values.iter().collect()
        }
        expression => vec![expression],
    }
}

fn guard_implies_index_nonnegative(guard: &ast::Expr, binder: &str, offset: i128) -> bool {
    let required_binder_minimum = offset.checked_neg().unwrap_or(i128::MAX);
    guard_conjuncts(guard).into_iter().any(|conjunct| {
        let ast::Expr::Compare(comparison) = conjunct else {
            return false;
        };
        if !matches!(comparison.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binder)
            || comparison.comparators.len() != 1
        {
            return false;
        }
        let Some(bound) = constant_tuple_index(&comparison.comparators[0]) else {
            return false;
        };
        match comparison.ops.as_slice() {
            [ast::CmpOp::GtE] => bound >= required_binder_minimum,
            [ast::CmpOp::Gt] => bound
                .checked_add(1)
                .is_some_and(|minimum| minimum >= required_binder_minimum),
            _ => false,
        }
    })
}

fn guard_implies_index_below_length(guard: &ast::Expr, binder: &str, offset: i128) -> bool {
    guard_conjuncts(guard).into_iter().any(|conjunct| {
        let ast::Expr::Compare(comparison) = conjunct else {
            return false;
        };
        if !matches!(comparison.left.as_ref(), ast::Expr::Name(name) if name.id.as_str() == binder)
            || comparison.comparators.len() != 1
        {
            return false;
        }
        let Some(subtracted_from_length) = length_minus_offset(&comparison.comparators[0]) else {
            return false;
        };
        match comparison.ops.as_slice() {
            [ast::CmpOp::Lt] => subtracted_from_length >= offset,
            [ast::CmpOp::LtE] => subtracted_from_length
                .checked_sub(1)
                .is_some_and(|strict_offset| strict_offset >= offset),
            _ => false,
        }
    })
}

fn length_minus_offset(expression: &ast::Expr) -> Option<i128> {
    if canonical_length(expression) {
        return Some(0);
    }
    let ast::Expr::BinOp(operation) = expression else {
        return None;
    };
    if !canonical_length(&operation.left) {
        return None;
    }
    let constant = constant_tuple_index(&operation.right)?;
    match operation.op {
        ast::Operator::Sub => Some(constant),
        ast::Operator::Add => constant.checked_neg(),
        _ => None,
    }
}

fn canonical_length(expression: &ast::Expr) -> bool {
    let ast::Expr::Call(length) = expression else {
        return false;
    };
    matches!(length.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "len")
        && length.args.len() == 1
        && length.keywords.is_empty()
}

fn is_zero_step_range_call(call: &ast::ExprCall) -> bool {
    matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "range")
        && call.keywords.is_empty()
        && call.args.len() == 3
        && constant_tuple_index(&call.args[2]) == Some(0)
}

fn contains_zero_step_range(expression: &ast::Expr) -> bool {
    match expression {
        ast::Expr::Call(call) => {
            is_zero_step_range_call(call)
                || contains_zero_step_range(&call.func)
                || call.args.iter().any(contains_zero_step_range)
                || call
                    .keywords
                    .iter()
                    .any(|keyword| contains_zero_step_range(&keyword.value))
        }
        ast::Expr::BoolOp(operation) => operation.values.iter().any(contains_zero_step_range),
        ast::Expr::IfExp(conditional) => {
            contains_zero_step_range(&conditional.test)
                || contains_zero_step_range(&conditional.body)
                || contains_zero_step_range(&conditional.orelse)
        }
        ast::Expr::BinOp(operation) => {
            contains_zero_step_range(&operation.left) || contains_zero_step_range(&operation.right)
        }
        ast::Expr::UnaryOp(operation) => contains_zero_step_range(&operation.operand),
        ast::Expr::Compare(comparison) => {
            contains_zero_step_range(&comparison.left)
                || comparison.comparators.iter().any(contains_zero_step_range)
        }
        ast::Expr::JoinedStr(joined) => joined.values.iter().any(contains_zero_step_range),
        ast::Expr::FormattedValue(formatted) => {
            contains_zero_step_range(&formatted.value)
                || formatted
                    .format_spec
                    .as_deref()
                    .is_some_and(contains_zero_step_range)
        }
        ast::Expr::Tuple(tuple) => tuple.elts.iter().any(contains_zero_step_range),
        ast::Expr::List(list) => list.elts.iter().any(contains_zero_step_range),
        ast::Expr::Subscript(subscript) => {
            contains_zero_step_range(&subscript.value) || contains_zero_step_range(&subscript.slice)
        }
        ast::Expr::Slice(slice) => [&slice.lower, &slice.upper, &slice.step]
            .into_iter()
            .filter_map(|bound| bound.as_deref())
            .any(contains_zero_step_range),
        ast::Expr::Attribute(attribute) => contains_zero_step_range(&attribute.value),
        ast::Expr::Lambda(lambda) => contains_zero_step_range(&lambda.body),
        _ => false,
    }
}

fn contains_dynamic_subscript(expression: &ast::Expr) -> bool {
    match expression {
        ast::Expr::Subscript(subscript) => {
            (!matches!(subscript.slice.as_ref(), ast::Expr::Slice(_))
                && constant_tuple_index(&subscript.slice).is_none())
                || contains_dynamic_subscript(&subscript.value)
                || contains_dynamic_subscript(&subscript.slice)
        }
        ast::Expr::Call(call) => {
            if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "ResultT")
                && call.args.len() == 1
                && call.keywords.is_empty()
                && annotation_sort(call.args.first()).is_ok()
            {
                return false;
            }
            contains_dynamic_subscript(&call.func)
                || call.args.iter().any(contains_dynamic_subscript)
                || call
                    .keywords
                    .iter()
                    .any(|keyword| contains_dynamic_subscript(&keyword.value))
        }
        ast::Expr::BoolOp(operation) => operation.values.iter().any(contains_dynamic_subscript),
        ast::Expr::IfExp(conditional) => {
            contains_dynamic_subscript(&conditional.test)
                || contains_dynamic_subscript(&conditional.body)
                || contains_dynamic_subscript(&conditional.orelse)
        }
        ast::Expr::BinOp(operation) => {
            contains_dynamic_subscript(&operation.left)
                || contains_dynamic_subscript(&operation.right)
        }
        ast::Expr::UnaryOp(operation) => contains_dynamic_subscript(&operation.operand),
        ast::Expr::Compare(comparison) => {
            contains_dynamic_subscript(&comparison.left)
                || comparison
                    .comparators
                    .iter()
                    .any(contains_dynamic_subscript)
        }
        ast::Expr::JoinedStr(joined) => joined.values.iter().any(contains_dynamic_subscript),
        ast::Expr::FormattedValue(formatted) => {
            contains_dynamic_subscript(&formatted.value)
                || formatted
                    .format_spec
                    .as_deref()
                    .is_some_and(contains_dynamic_subscript)
        }
        ast::Expr::Tuple(tuple) => tuple.elts.iter().any(contains_dynamic_subscript),
        ast::Expr::List(list) => list.elts.iter().any(contains_dynamic_subscript),
        ast::Expr::Slice(slice) => [&slice.lower, &slice.upper, &slice.step]
            .into_iter()
            .filter_map(|bound| bound.as_deref())
            .any(contains_dynamic_subscript),
        ast::Expr::Attribute(attribute) => contains_dynamic_subscript(&attribute.value),
        ast::Expr::Lambda(lambda) => contains_dynamic_subscript(&lambda.body),
        _ => false,
    }
}

fn lower_constant_range(call: &ast::ExprCall) -> Result<Term, ContractFailure> {
    let bounds = call
        .args
        .iter()
        .map(constant_tuple_index)
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.contracts.range-symbolic-unsupported",
            message: "range currently requires one to three integer literals".to_owned(),
        })?;
    let (start, stop, step) = match bounds.as_slice() {
        [stop] => (0, *stop, 1),
        [start, stop] => (*start, *stop, 1),
        [start, stop, step] => (*start, *stop, *step),
        _ => return unsupported_expression(&ast::Expr::Call(call.clone())),
    };
    if step == 0 {
        // Runtime lowering has already forked a ValueError path and made this normal path
        // inconsistent. A concrete placeholder keeps the term well-sorted without fabricating a
        // reachable return value. Specifications reject the partial operation before lowering.
        return Ok(Term::Range { values: Vec::new() });
    }
    let length = finite_range_length(start, stop, step);
    let length = usize::try_from(length).map_err(|_| ContractFailure {
        code: "frontend.python.contracts.range-expansion-size-overflow",
        message: "constant range length exceeds the current usize frontend".to_owned(),
    })?;
    let mut current = start;
    let mut values = Vec::new();
    reserve_scalar_expansion(
        &mut values,
        length,
        "frontend.python.contracts.range-expansion-allocation-failed",
        "constant range",
    )?;
    while values.len() < length {
        values.push(i64::try_from(current).map_err(|_| ContractFailure {
            code: "frontend.python.integer.out-of-range",
            message: format!("range value {current} exceeds the current i64 frontend"),
        })?);
        if values.len() == length {
            break;
        }
        current = current.checked_add(step).ok_or_else(|| ContractFailure {
            code: "frontend.python.integer.out-of-range",
            message: "range expansion overflowed the current signed integer frontend".to_owned(),
        })?;
    }
    Ok(Term::Range { values })
}

fn finite_range_length(start: i128, stop: i128, step: i128) -> u128 {
    if (step > 0 && start >= stop) || (step < 0 && start <= stop) {
        return 0;
    }
    let distance = start.abs_diff(stop);
    let step = step.unsigned_abs();
    ((distance - 1) / step) + 1
}

fn python_object_identity(
    expression: &ast::Expr,
    environment: &BTreeMap<String, Term>,
    identities: &BTreeMap<String, PythonObjectIdentity>,
) -> Option<PythonObjectIdentity> {
    match expression {
        ast::Expr::Name(name) => identities.get(name.id.as_str()).cloned().or_else(|| {
            (environment.get(name.id.as_str()) == Some(&ellipsis_singleton()))
                .then_some(PythonObjectIdentity::EllipsisSingleton)
        }),
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Str(value) => Some(PythonObjectIdentity::InternedString(value.clone())),
            ast::Constant::Ellipsis => Some(PythonObjectIdentity::EllipsisSingleton),
            _ => None,
        },
        ast::Expr::Tuple(tuple) if tuple.elts.is_empty() => Some(PythonObjectIdentity::EmptyTuple),
        ast::Expr::Tuple(_) => Some(PythonObjectIdentity::Fresh(
            expression.range().start().into(),
        )),
        ast::Expr::List(_)
        | ast::Expr::Set(_)
        | ast::Expr::Dict(_)
        | ast::Expr::ListComp(_)
        | ast::Expr::SetComp(_)
        | ast::Expr::DictComp(_) => Some(PythonObjectIdentity::Fresh(
            expression.range().start().into(),
        )),
        ast::Expr::Call(call)
            if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "range")
                && (1..=3).contains(&call.args.len())
                && call.keywords.is_empty() =>
        {
            Some(PythonObjectIdentity::Fresh(
                expression.range().start().into(),
            ))
        }
        ast::Expr::Call(call)
            if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "str")
                && call.args.len() == 1
                && call.keywords.is_empty() =>
        {
            let argument = &call.args[0];
            if matches!(argument, ast::Expr::Name(name) if environment
                .get(name.id.as_str())
                .and_then(|value| value.sort().ok()) == Some(Sort::String))
            {
                python_object_identity(argument, environment, identities)
            } else {
                Some(PythonObjectIdentity::Uncertain(
                    expression.range().start().into(),
                ))
            }
        }
        ast::Expr::BinOp(operation) if matches!(operation.op, ast::Operator::Add) => Some(
            PythonObjectIdentity::Uncertain(expression.range().start().into()),
        ),
        _ => None,
    }
}

fn lower_proven_object_identity(
    expression: &ast::Expr,
    lowerer: &ExpressionLowerer<'_>,
    environment: &BTreeMap<String, Term>,
    identities: &BTreeMap<String, PythonObjectIdentity>,
) -> Result<Option<Term>, ContractFailure> {
    let ast::Expr::Compare(comparison) = expression else {
        return Ok(None);
    };
    let [operator] = comparison.ops.as_slice() else {
        return Ok(None);
    };
    if !matches!(operator, ast::CmpOp::Is | ast::CmpOp::IsNot) {
        return Ok(None);
    }
    let [right_expression] = comparison.comparators.as_slice() else {
        return Ok(None);
    };
    let Some(left_identity) = python_object_identity(&comparison.left, environment, identities)
    else {
        return Ok(None);
    };
    let Some(right_identity) = python_object_identity(right_expression, environment, identities)
    else {
        return Ok(None);
    };
    let left = lowerer.lower(&comparison.left, environment, None)?;
    let right = lowerer.lower(right_expression, environment, None)?;
    let left_sort = left.sort().map_err(type_failure)?;
    let right_sort = right.sort().map_err(type_failure)?;
    if !matches!(
        left_sort,
        Sort::String
            | Sort::Tuple(_)
            | Sort::VariadicTuple(_)
            | Sort::Range
            | Sort::List(_)
            | Sort::Set(_)
            | Sort::Dict(_, _)
            | Sort::FiniteDict(_, _)
            | Sort::Reference
    ) || !matches!(
        right_sort,
        Sort::String
            | Sort::Tuple(_)
            | Sort::VariadicTuple(_)
            | Sort::Range
            | Sort::List(_)
            | Sort::Set(_)
            | Sort::Dict(_, _)
            | Sort::FiniteDict(_, _)
            | Sort::Reference
    ) {
        return Ok(None);
    }
    if left_sort != right_sort {
        return Ok(Some(Term::Bool {
            value: *operator == ast::CmpOp::IsNot,
        }));
    }
    if (matches!(left_identity, PythonObjectIdentity::Fresh(_))
        && matches!(right_identity, PythonObjectIdentity::FunctionInput(_)))
        || (matches!(left_identity, PythonObjectIdentity::FunctionInput(_))
            && matches!(right_identity, PythonObjectIdentity::Fresh(_)))
    {
        return Ok(Some(Term::Bool {
            value: *operator == ast::CmpOp::IsNot,
        }));
    }
    if (matches!(left_identity, PythonObjectIdentity::Uncertain(_))
        || matches!(right_identity, PythonObjectIdentity::Uncertain(_))
        || matches!(left_identity, PythonObjectIdentity::FunctionInput(_))
        || matches!(right_identity, PythonObjectIdentity::FunctionInput(_)))
        && left_identity != right_identity
    {
        let identity_relation = Term::Variable {
            name: format!(
                "python-object-identity:{}:{}",
                u32::from(comparison.left.range().start()),
                u32::from(right_expression.range().start())
            ),
            sort: Sort::Bool,
        };
        return Ok(Some(if *operator == ast::CmpOp::Is {
            identity_relation
        } else {
            Term::Not {
                value: Box::new(identity_relation),
            }
        }));
    }
    let identical = left_identity == right_identity;
    Ok(Some(Term::Bool {
        value: if *operator == ast::CmpOp::Is {
            identical
        } else {
            !identical
        },
    }))
}

fn is_immutable_collection_value_sort(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Bool | Sort::Int | Sort::String | Sort::Reference | Sort::Bytes
    ) || matches!(sort, Sort::Tuple(elements) if elements.iter().all(is_immutable_collection_value_sort))
        || matches!(sort, Sort::VariadicTuple(element) if is_immutable_collection_value_sort(element))
        || matches!(sort, Sort::List(element) if is_immutable_collection_value_sort(element))
        || matches!(sort, Sort::Set(element) if is_immutable_collection_key_sort(element))
        || matches!(sort, Sort::Dict(key, value) | Sort::FiniteDict(key, value)
            if is_immutable_collection_key_sort(key)
                && is_immutable_collection_value_sort(value))
}

fn is_immutable_collection_key_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int | Sort::String | Sort::Bytes)
        || matches!(sort, Sort::Tuple(elements) if elements.iter().all(is_immutable_collection_key_sort))
        || matches!(sort, Sort::VariadicTuple(element) if is_immutable_collection_key_sort(element))
}

fn term_is_closed_immutable_value(term: &Term) -> bool {
    match term {
        Term::Bool { .. } | Term::Int { .. } | Term::String { .. } | Term::Bytes { .. } => true,
        Term::Tuple { values } => values.iter().all(term_is_closed_immutable_value),
        Term::VariadicTuple { values, .. } => values.iter().all(term_is_closed_immutable_value),
        _ => false,
    }
}

fn annotation_sort(expression: Option<&ast::Expr>) -> Result<Sort, ContractFailure> {
    match expression {
        Some(ast::Expr::Name(name)) if name.id.as_str() == "int" => Ok(Sort::Int),
        Some(ast::Expr::Name(name)) if name.id.as_str() == "bool" => Ok(Sort::Bool),
        Some(ast::Expr::Name(name)) if name.id.as_str() == "str" => Ok(Sort::String),
        Some(ast::Expr::Name(name)) if name.id.as_str() == "bytes" => Ok(Sort::Bytes),
        Some(ast::Expr::Name(name)) if name.id.as_str() == "range" => Ok(Sort::Range),
        Some(ast::Expr::Name(name)) if name.id.as_str() == "EllipsisType" => Ok(Sort::Reference),
        Some(ast::Expr::Constant(constant)) if matches!(&constant.value, ast::Constant::None) => {
            Ok(Sort::Unit)
        }
        Some(ast::Expr::Subscript(subscript)) if matches!(subscript.value.as_ref(), ast::Expr::Name(name) if matches!(name.id.as_str(), "Tuple" | "tuple")) =>
        {
            if let ast::Expr::Tuple(tuple) = subscript.slice.as_ref()
                && let [element, ellipsis] = tuple.elts.as_slice()
                && matches!(ellipsis, ast::Expr::Constant(constant) if matches!(constant.value, ast::Constant::Ellipsis))
            {
                let element = annotation_sort(Some(element))?;
                if !is_immutable_collection_value_sort(&element) {
                    return failure(
                        "frontend.python.contracts.variadic-tuple-element-type-unsupported",
                        format!(
                            "Tuple[T, ...] elements require an immutable supported value type, found {element:?}"
                        ),
                    );
                }
                return Ok(Sort::VariadicTuple(Box::new(element)));
            }
            let elements = match subscript.slice.as_ref() {
                ast::Expr::Tuple(tuple) => tuple
                    .elts
                    .iter()
                    .map(|element| annotation_sort(Some(element)))
                    .collect::<Result<Vec<_>, _>>()?,
                element => vec![annotation_sort(Some(element))?],
            };
            Ok(Sort::Tuple(elements))
        }
        Some(ast::Expr::Subscript(subscript)) if matches!(subscript.value.as_ref(), ast::Expr::Name(name) if matches!(name.id.as_str(), "List" | "list")) =>
        {
            let element = annotation_sort(Some(&subscript.slice))?;
            if !is_immutable_collection_value_sort(&element) {
                return failure(
                    "frontend.python.contracts.list-element-type-unsupported",
                    format!(
                        "List elements currently require a primitive, bytes, or reference type, found {element:?}"
                    ),
                );
            }
            Ok(Sort::List(Box::new(element)))
        }
        Some(ast::Expr::Subscript(subscript)) if matches!(subscript.value.as_ref(), ast::Expr::Name(name) if matches!(name.id.as_str(), "Set" | "set")) =>
        {
            let mut element = annotation_sort(Some(&subscript.slice))?;
            if !is_immutable_collection_key_sort(&element) {
                return failure(
                    "frontend.python.contracts.set-element-type-unsupported",
                    format!("Set elements require primitive value equality, found {element:?}"),
                );
            }
            // Python considers bool and int equal keys.  The frontend normalizes
            // bool-valued set comprehensions to Int before constructing this sort.
            if element == Sort::Bool {
                element = Sort::Int;
            }
            Ok(Sort::Set(Box::new(element)))
        }
        Some(ast::Expr::Subscript(subscript)) if matches!(subscript.value.as_ref(), ast::Expr::Name(name) if matches!(name.id.as_str(), "Dict" | "dict")) =>
        {
            let ast::Expr::Tuple(arguments) = subscript.slice.as_ref() else {
                return failure(
                    "frontend.python.contracts.dict-annotation-arity",
                    "Dict requires exactly key and value type arguments",
                );
            };
            if arguments.elts.len() != 2 {
                return failure(
                    "frontend.python.contracts.dict-annotation-arity",
                    "Dict requires exactly key and value type arguments",
                );
            }
            let mut key = annotation_sort(arguments.elts.first())?;
            let value = annotation_sort(arguments.elts.get(1))?;
            if !is_immutable_collection_key_sort(&key)
                || !is_immutable_collection_value_sort(&value)
            {
                return failure(
                    "frontend.python.contracts.dict-type-unsupported",
                    format!(
                        "Dict comprehensions require primitive key/value types, found {key:?}/{value:?}"
                    ),
                );
            }
            if key == Sort::Bool {
                key = Sort::Int;
            }
            Ok(Sort::Dict(Box::new(key), Box::new(value)))
        }
        _ => failure(
            "frontend.python.contracts.type-unsupported",
            "the scalar contract fragment requires explicit primitive, fixed Tuple, homogeneous List, Set, or Dict annotations",
        ),
    }
}

fn assignment_type_sort(
    assignment: &ast::StmtAssign,
    lowerer: &ExpressionLowerer<'_>,
    source: &str,
) -> Result<Option<ScalarTypeComment>, ContractFailure> {
    if let Some(annotation) = assignment.type_comment.as_deref() {
        return scalar_type_comment_sort(annotation).map(Some);
    }
    let line = source_location(source, assignment.range.start().into()).0;
    Ok(lowerer.type_comments.get(&line).cloned())
}

fn scalar_type_comment_sort(annotation: &str) -> Result<ScalarTypeComment, ContractFailure> {
    let annotation = annotation.trim();
    let expression =
        ast::Expr::parse(annotation, "<scalar-type-comment>").map_err(|error| ContractFailure {
            code: "frontend.python.contracts.type-comment-parse-error",
            message: format!("cannot parse assignment type comment {annotation:?}: {error}"),
        })?;
    let parsed = if let ast::Expr::Subscript(optional) = &expression
        && matches!(optional.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Optional")
    {
        annotation_sort(Some(&optional.slice)).map(ScalarTypeComment::Optional)
    } else {
        annotation_sort(Some(&expression)).map(ScalarTypeComment::Exact)
    };
    parsed.map_err(|error| ContractFailure {
        code: "frontend.python.contracts.type-comment-unsupported",
        message: format!(
            "assignment type comment {annotation:?} is unsupported: {}",
            error.message
        ),
    })
}

fn coerce_to_type_comment(
    term: Term,
    annotation: &ScalarTypeComment,
    context: &str,
) -> Result<Term, ContractFailure> {
    match annotation {
        ScalarTypeComment::Exact(expected) => coerce_to_sort(term, expected, context),
        ScalarTypeComment::Optional(expected) => {
            if term.sort().map_err(type_failure)? == Sort::Unit {
                Ok(term)
            } else {
                coerce_to_sort(term, expected, context)
            }
        }
    }
}

fn lower_type_commented_expression(
    lowerer: &ExpressionLowerer<'_>,
    expression: &ast::Expr,
    environment: &BTreeMap<String, Term>,
    result: Option<&Term>,
    annotation: &ScalarTypeComment,
    context: &str,
) -> Result<Term, ContractFailure> {
    match annotation {
        ScalarTypeComment::Exact(expected) => {
            lowerer.lower_expected(expression, environment, result, expected, context)
        }
        ScalarTypeComment::Optional(_) if matches!(expression, ast::Expr::Constant(constant) if matches!(constant.value, ast::Constant::None)) => {
            lowerer.lower(expression, environment, result)
        }
        ScalarTypeComment::Optional(expected) => {
            lowerer.lower_expected(expression, environment, result, expected, context)
        }
    }
}

fn ensure_boolean(term: &Term, context: &str) -> Result<(), ContractFailure> {
    if term.sort().map_err(type_failure)? == Sort::Bool {
        Ok(())
    } else {
        failure(
            "frontend.python.contracts.expected-bool",
            format!("{context} must be boolean"),
        )
    }
}

fn coerce_python_int(term: Term, context: &str) -> Result<Term, ContractFailure> {
    match term.sort().map_err(type_failure)? {
        Sort::Int => Ok(term),
        Sort::Bool => Ok(Term::IfThenElse {
            condition: Box::new(term),
            then_value: Box::new(Term::Int { value: 1 }),
            else_value: Box::new(Term::Int { value: 0 }),
        }),
        Sort::String
        | Sort::Float
        | Sort::Unit
        | Sort::Reference
        | Sort::Class
        | Sort::Bytes
        | Sort::Range
        | Sort::Tuple(_)
        | Sort::VariadicTuple(_)
        | Sort::List(_)
        | Sort::Set(_)
        | Sort::Dict(_, _)
        | Sort::FiniteDict(_, _)
        | Sort::DictKeys(_) => failure(
            "frontend.python.contracts.expected-int",
            format!("{context} must be int or bool"),
        ),
    }
}

fn coerce_truthy(term: Term, context: &str) -> Result<Term, ContractFailure> {
    match &term {
        Term::Bool { .. } => return Ok(term),
        Term::Int { value } => return Ok(Term::Bool { value: *value != 0 }),
        Term::String { value } => {
            return Ok(Term::Bool {
                value: !value.is_empty(),
            });
        }
        Term::Unit => return Ok(Term::Bool { value: false }),
        Term::List { values, .. } => {
            return Ok(Term::Bool {
                value: !values.is_empty(),
            });
        }
        Term::Bytes { values } => {
            return Ok(Term::Bool {
                value: !values.is_empty(),
            });
        }
        Term::Range { values } => {
            return Ok(Term::Bool {
                value: !values.is_empty(),
            });
        }
        Term::FiniteDict { entries, .. } => {
            return Ok(Term::Bool {
                value: !entries.is_empty(),
            });
        }
        Term::DictKeys { values, .. } => {
            return Ok(Term::Bool {
                value: !values.is_empty(),
            });
        }
        _ => {}
    }
    match term.sort().map_err(type_failure)? {
        Sort::Bool => Ok(term),
        Sort::Int => Ok(Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(term),
                right: Box::new(Term::Int { value: 0 }),
            }),
        }),
        Sort::Float => failure(
            "frontend.python.contracts.float-truthiness-unsupported",
            format!("{context}: float truthiness requires IEEE-754 zero/NaN semantics"),
        ),
        Sort::Unit => Ok(Term::Bool { value: false }),
        Sort::String => Ok(Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(term),
                right: Box::new(Term::String {
                    value: String::new(),
                }),
            }),
        }),
        Sort::Reference => failure(
            "frontend.python.contracts.reference-truthiness-unsupported",
            format!("{context}: reference truthiness requires explicit None semantics"),
        ),
        Sort::Class => failure(
            "frontend.python.contracts.class-truthiness-unsupported",
            format!("{context}: class-object truthiness is not part of the scalar fragment"),
        ),
        Sort::Tuple(elements) => Ok(Term::Bool {
            value: !elements.is_empty(),
        }),
        Sort::VariadicTuple(_) => Ok(Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(Term::VariadicTupleLength {
                    value: Box::new(term),
                }),
                right: Box::new(Term::Int { value: 0 }),
            }),
        }),
        Sort::Bytes => Ok(Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(Term::BytesLength {
                    value: Box::new(term),
                }),
                right: Box::new(Term::Int { value: 0 }),
            }),
        }),
        Sort::Range => failure(
            "frontend.python.contracts.symbolic-sequence-truthiness-unsupported",
            format!("{context}: symbolic range truthiness is not yet lowered"),
        ),
        Sort::List(_) => Ok(Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(Term::ListLength {
                    value: Box::new(term),
                }),
                right: Box::new(Term::Int { value: 0 }),
            }),
        }),
        Sort::Set(_) => Ok(Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(Term::SetLength {
                    value: Box::new(term),
                }),
                right: Box::new(Term::Int { value: 0 }),
            }),
        }),
        Sort::Dict(_, _) => Ok(Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(Term::DictLength {
                    value: Box::new(term),
                }),
                right: Box::new(Term::Int { value: 0 }),
            }),
        }),
        Sort::FiniteDict(_, _) | Sort::DictKeys(_) => failure(
            "frontend.python.contracts.symbolic-dict-truthiness-unsupported",
            format!("{context}: symbolic dictionary truthiness is outside this scalar slice"),
        ),
    }
}

fn select_python_value(
    condition: Term,
    mut then_value: Term,
    mut else_value: Term,
) -> Result<Term, ContractFailure> {
    let then_sort = then_value.sort().map_err(type_failure)?;
    let else_sort = else_value.sort().map_err(type_failure)?;
    if then_sort == Sort::Bool && else_sort == Sort::Int {
        then_value = coerce_python_int(then_value, "conditional true value")?;
    } else if then_sort == Sort::Int && else_sort == Sort::Bool {
        else_value = coerce_python_int(else_value, "conditional false value")?;
    } else if then_sort != else_sort {
        return failure(
            "frontend.python.contracts.conditional-result-type",
            format!(
                "path-dependent Python expression has incompatible result sorts {then_sort:?} and {else_sort:?}"
            ),
        );
    }
    match condition {
        Term::Bool { value: true } => Ok(then_value),
        Term::Bool { value: false } => Ok(else_value),
        condition => Ok(Term::IfThenElse {
            condition: Box::new(condition),
            then_value: Box::new(then_value),
            else_value: Box::new(else_value),
        }),
    }
}

fn coerce_to_sort(term: Term, expected: &Sort, context: &str) -> Result<Term, ContractFailure> {
    let actual = term.sort().map_err(type_failure)?;
    if &actual == expected {
        Ok(term)
    } else if *expected == Sort::Int && actual == Sort::Bool {
        coerce_python_int(term, context)
    } else if let Sort::VariadicTuple(expected_element) = expected
        && let Term::Tuple { values } = term
    {
        let values = values
            .into_iter()
            .map(|value| coerce_to_sort(value, expected_element, "variadic tuple element"))
            .collect::<Result<Vec<_>, _>>()?;
        let tuple = Term::VariadicTuple {
            element_sort: (**expected_element).clone(),
            values,
        };
        tuple.sort().map_err(type_failure)?;
        Ok(tuple)
    } else {
        failure(
            "frontend.python.contracts.type-mismatch",
            format!("{context} has sort {actual:?}, expected {expected:?}"),
        )
    }
}

fn type_failure(message: String) -> ContractFailure {
    ContractFailure {
        code: "frontend.python.contracts.term-type-error",
        message,
    }
}

fn sequence_builtin_failure(error: SequenceBuiltinError) -> ContractFailure {
    match error {
        SequenceBuiltinError::ExpectedList { operation, actual } => ContractFailure {
            code: "frontend.python.contracts.sequence-builtin-expected-list",
            message: format!("{operation} requires a homogeneous List value, found {actual:?}"),
        },
        SequenceBuiltinError::MismatchedConcatElements { left, right } => ContractFailure {
            code: "frontend.python.contracts.list-concat-element-mismatch",
            message: format!(
                "list concatenation requires identical element sorts, found {left:?} and {right:?}"
            ),
        },
        SequenceBuiltinError::ExpectedIntegerElements { operation, actual } => ContractFailure {
            code: "frontend.python.contracts.sequence-builtin-expected-integers",
            message: format!("{operation} requires List[int], found List[{actual:?}]"),
        },
    }
}

fn statement_offset(statement: &ast::Stmt) -> u32 {
    use rustpython_parser::ast::Ranged;
    statement.range().start().into()
}

fn source_location(source: &str, byte_offset: u32) -> (u32, u32) {
    let end = usize::try_from(byte_offset)
        .unwrap_or(source.len())
        .min(source.len());
    let prefix = &source.as_bytes()[..end];
    let line = 1 + prefix.iter().filter(|byte| **byte == b'\n').count() as u32;
    let column = prefix
        .iter()
        .rposition(|byte| *byte == b'\n')
        .map_or(prefix.len() + 1, |position| prefix.len() - position) as u32;
    (line, column)
}

fn unsupported_statement<T>(
    function: &ast::StmtFunctionDef,
    statement: &ast::Stmt,
) -> Result<T, ContractFailure> {
    failure(
        "frontend.python.contracts.statement-unsupported",
        format!(
            "function {:?} contains unsupported statement {statement:?}",
            function.name
        ),
    )
}

fn unsupported_expression<T>(expression: &ast::Expr) -> Result<T, ContractFailure> {
    failure(
        "frontend.python.contracts.expression-unsupported",
        format!("unsupported symbolic expression {expression:?}"),
    )
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

    #[test]
    fn class_declaration_islands_never_satisfy_class_or_method_selection() {
        let source = "class Record:\n    def inspect(self) -> int:\n        return 1\n\ndef run() -> int:\n    return 1\n";
        for target in ["Record", "inspect"] {
            let selected = BTreeSet::from([target.to_owned()]);
            let error = verify_contract_module_internal(
                source,
                "select/class_island.py",
                &[],
                &[],
                Some(&selected),
                true,
                ModuleIdentity::entry("select/class_island.py"),
            )
            .expect_err("the scalar frontend must not claim class or method selection");
            assert_eq!(
                error.code,
                "frontend.python.contracts.class-declaration-island-selected"
            );
        }
    }

    #[test]
    fn parses_precise_nested_mutable_collection_annotations() {
        for (annotation, expected) in [
            (
                "List[List[int]]",
                Sort::List(Box::new(Sort::List(Box::new(Sort::Int)))),
            ),
            (
                "List[Set[int]]",
                Sort::List(Box::new(Sort::Set(Box::new(Sort::Int)))),
            ),
            (
                "List[Dict[int, int]]",
                Sort::List(Box::new(Sort::Dict(
                    Box::new(Sort::Int),
                    Box::new(Sort::Int),
                ))),
            ),
        ] {
            assert_eq!(
                scalar_type_comment_sort(annotation).unwrap(),
                ScalarTypeComment::Exact(expected)
            );
        }
    }

    #[test]
    fn proves_assertion_and_postcondition_from_requires() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef successor(value: int) -> int:\n    Requires(value > 0)\n    Ensures(Result() > value)\n    next_value = value + 1\n    assert next_value > 0\n    return next_value\n",
            "successor.py",
            &["successor".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
        assert_eq!(result.obligations.len(), 2);
    }

    #[test]
    fn accepts_typing_imports_but_still_resolves_scalar_annotations_locally() {
        let result = verify_contract_module(
            "from typing import List\nfrom nagini_contracts.contracts import *\n\ndef identity(value: int) -> int:\n    return value\n",
            "typing_import.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn leading_module_and_function_docstrings_are_inert() {
        let result = verify_contract_module(
            "\"\"\"module documentation\"\"\"\nfrom nagini_contracts.contracts import *\n\ndef choose(flag: bool) -> int:\n    \"\"\"function documentation\"\"\"\n    Requires(flag)\n    Ensures(Result() == 1)\n    value = 1\n    return value\n",
            "docstrings.py",
            &["choose".to_owned()],
        )
        .unwrap();

        assert!(result.passed);
        assert_eq!(result.functions, ["choose"]);
        assert!(result.obligations.iter().all(ObligationResult::satisfied));
    }

    #[test]
    fn a_nonleading_string_does_not_move_a_late_contract_before_execution() {
        let error = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef choose() -> int:\n    value = 1\n    \"not a docstring\"\n    Requires(value == 1)\n    return value\n",
            "late_contract_after_string.py",
            &["choose".to_owned()],
        )
        .unwrap_err();

        assert_eq!(error.code, "frontend.python.contracts.late-contract");
    }

    #[test]
    fn passive_class_declaration_does_not_block_unrelated_scalar_functions() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\nclass Marker:\n    pass\n\ndef choose(flag: bool) -> int:\n    Requires(flag)\n    Ensures(Result() == 1)\n    return 1\n",
            "passive_class.py",
            &["choose".to_owned()],
        )
        .unwrap();

        assert!(result.passed);
        assert_eq!(result.functions, ["choose"]);
        assert!(result.obligations.iter().all(ObligationResult::satisfied));
    }

    #[test]
    fn passive_class_does_not_promote_nominal_runtime_semantics() {
        let nominal = verify_contract_module(
            "class Marker:\n    pass\n\ndef identity(value: Marker) -> Marker:\n    return value\n",
            "passive_nominal.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(nominal.code, "frontend.python.contracts.type-unsupported");

        for source in [
            "class Marker(object):\n    pass\n\ndef value() -> int:\n    return 1\n",
            "class Marker:\n    number = 1\n\ndef value() -> int:\n    return 1\n",
            "def decorate(value: int) -> int:\n    return value\n\n@decorate\nclass Marker:\n    pass\n",
        ] {
            let error = verify_contract_module(source, "active_class.py", &[]).unwrap_err();
            assert_eq!(
                error.code, "frontend.python.contracts.module-statement-unsupported",
                "source:\n{source}\n{error:#?}"
            );
        }
    }

    #[test]
    fn passive_class_names_are_unique_and_cannot_shadow_scalar_syntax() {
        for source in [
            "class Marker:\n    pass\n\ndef Marker() -> int:\n    return 1\n",
            "class Marker:\n    pass\n\nMarker = 1\n",
            "class Marker:\n    pass\n\nclass Marker:\n    pass\n",
        ] {
            let error = verify_contract_module(source, "shadowed_class.py", &[]).unwrap_err();
            assert_eq!(
                error.code, "frontend.python.contracts.passive-class-binding-shadowed",
                "source:\n{source}\n{error:#?}"
            );
        }

        let reserved = verify_contract_module(
            "class int:\n    pass\n\ndef value() -> int:\n    return 1\n",
            "reserved_class.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            reserved.code,
            "frontend.python.contracts.passive-class-name-reserved"
        );
    }

    #[test]
    fn pass_only_int_subclass_uses_exact_inherited_numeric_construction() {
        let proved = verify_contract_module(
            "from nagini_contracts.contracts import *\n\nclass Count(int):\n    pass\n\ndef value() -> int:\n    Ensures(Result() == 5)\n    return Count(5)\n",
            "int_subclass.py",
            &["value".to_owned()],
        )
        .unwrap();
        assert!(proved.passed);

        let exact_upstream = verify_contract_module(
            "class A(int):\n    pass\n\ndef client() -> None:\n    assert A(5) == 2\n",
            "issues/00261.py",
            &["client".to_owned()],
        )
        .unwrap();
        assert!(!exact_upstream.passed);
        assert_eq!(exact_upstream.obligations.len(), 1);
        assert_eq!(
            exact_upstream.obligations[0].status,
            ObligationStatus::Refuted
        );
    }

    #[test]
    fn scalar_int_subclass_refuses_shadowed_or_widened_construction() {
        let shadowed = verify_contract_module(
            "int = 1\n\nclass Count(int):\n    pass\n",
            "shadowed_int.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            shadowed.code,
            "frontend.python.contracts.scalar-subclass-base-shadowed"
        );

        for source in [
            "class Count(int):\n    pass\n\ndef value(text: str) -> int:\n    return Count(text)\n",
            "class Count(int):\n    pass\n\ndef value() -> int:\n    return Count(value=5)\n",
            "class Count(bool):\n    pass\n\ndef value() -> int:\n    return 1\n",
            "class Count(int):\n    def custom(self) -> int:\n        return 1\n",
        ] {
            assert!(
                verify_contract_module(source, "unsupported_subclass.py", &[]).is_err(),
                "source unexpectedly verified:\n{source}"
            );
        }
    }

    #[test]
    fn proves_symbolic_string_concatenation_and_length_contract() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef append(left: str, right: str) -> str:\n    Ensures(len(Result()) == len(left) + len(right))\n    return left + right\n",
            "strings.py",
            &["append".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn proves_fixed_typed_tuple_construction_indexing_and_length() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef pair(number: int, text: str) -> Tuple[int, str]:\n    Ensures(Result()[0] == number)\n    Ensures(Result()[1] == text)\n    Ensures(Result()[-1] == text)\n    Ensures(len(Result()) == 2)\n    return number, text\n",
            "tuples.py",
            &["pair".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn heterogeneous_tuple_element_equality_is_statically_false() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef broken() -> Tuple[int, str]:\n    Ensures(Result()[1] == 2)\n    return 1, 'text'\n",
            "heterogeneous_tuple.py",
            &[],
        )
        .unwrap();
        assert!(!result.passed);
        assert!(
            result
                .obligations
                .iter()
                .any(|obligation| obligation.status == ObligationStatus::Refuted),
            "the false postcondition must remain refuted: {result:#?}"
        );
    }

    #[test]
    fn out_of_bounds_fixed_tuple_index_refuses() {
        let error = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef invalid(value: Tuple[int, str]) -> int:\n    return value[2]\n",
            "tuple_oob.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.python.contracts.tuple-index-invalid");
        assert!(error.message.contains("outside fixed tuple length"));
    }

    #[test]
    fn proves_homogeneous_typed_list_values_length_equality_and_literal_indexing() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import List\n\ndef preserve(values: List[int]) -> List[int]:\n    Ensures(Result() == values)\n    Ensures(len(Result()) == len(values))\n    return values\n\ndef run() -> int:\n    items: List[int] = [4, 9]\n    same = preserve(items)\n    assert same == items\n    assert len(items) == 2\n    assert items[-1] == 9\n    empty: List[int] = []\n    assert len(empty) == 0\n    commented = [7, 8]  # type: List[int]\n    assert len(commented) == 2\n    return items[0]\n",
            "immutable_lists.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn proves_finite_dictionary_keys_as_a_distinct_immutable_view() {
        let result = verify_contract_module(
            "def inspect() -> None:\n    values = {1: 'old', 2: 'two', 1: 'new'}\n    keys = values.keys()\n    assert len(values) == 2\n    assert len(keys) == 2\n    assert 1 in keys\n    assert 3 not in keys\n    for key in keys:\n        assert key > 0\n",
            "finite_dict_keys.py",
            &["inspect".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn dictionary_key_views_remain_non_sliceable() {
        let error = verify_contract_module(
            "def broken() -> None:\n    values = {1: 'one'}\n    keys = values.keys()\n    sliced = keys[:]\n",
            "dict_keys_slice.py",
            &["broken".to_owned()],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.slice-symbolic-sequence-unsupported"
        );
    }

    #[test]
    fn finite_dictionary_keys_refuse_dynamic_hash_and_mixed_key_sorts() {
        let dynamic = verify_contract_module(
            "def broken(key: int) -> None:\n    values = {key: 'value'}\n",
            "dynamic_dict_key.py",
            &["broken".to_owned()],
        )
        .unwrap_err();
        assert_eq!(
            dynamic.code,
            "frontend.python.contracts.dict-key-unsupported"
        );

        let mixed = verify_contract_module(
            "def broken() -> None:\n    values = {1: 'one', 'two': 'two'}\n",
            "mixed_dict_keys.py",
            &["broken".to_owned()],
        )
        .unwrap_err();
        assert_eq!(
            mixed.code,
            "frontend.python.contracts.dict-key-type-heterogeneous"
        );
    }

    #[test]
    fn proves_static_slices_and_preserves_list_tuple_bytes_and_range_types() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef slices() -> None:\n    values = [1, 2, 3, 4, 5]\n    assert values[1:4] == [2, 3, 4]\n    assert values[::-1] == [5, 4, 3, 2, 1]\n    pair = (1, 2, 3)\n    assert pair[-2:] == (2, 3)\n    data = b'12345'\n    assert data[1:-1] == b'234'\n    numbers = range(1, 6)\n    assert numbers[::2] == range(1, 6, 2)\n    assert ToSeq(numbers[:3]) == [1, 2, 3]\n    assert data != [49, 50, 51, 52, 53]\n    assert numbers != [1, 2, 3, 4, 5]\n",
            "static_slices.py",
            &["slices".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
        assert!(result.obligations.iter().all(ObligationResult::satisfied));
    }

    #[test]
    fn proves_symbolic_bytes_operations_join_repetition_and_indexing() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef combine(left: bytes, right: bytes) -> bytes:\n    Ensures(Result() == left + right)\n    Ensures(len(Result()) == len(left) + len(right))\n    return left + right\n\ndef repeated(value: bytes) -> bytes:\n    Ensures(Result() == value + value)\n    return value * 2\n\ndef reverse_repeated(value: bytes) -> bytes:\n    Ensures(Result() == value + value)\n    return 2 * value\n\ndef negative_repeat() -> bytes:\n    Ensures(Result() == b'')\n    return b'x' * -3\n\ndef joined(left: bytes, right: bytes) -> bytes:\n    Ensures(Result() == left + b'-' + right)\n    values = [left, right]\n    return b'-'.join(values)\n\ndef first(value: bytes) -> int:\n    Requires(len(value) > 0)\n    return value[0]\n\ndef first_or_zero(value: bytes) -> int:\n    try:\n        return value[0]\n    except IndexError:\n        return 0\n",
            "symbolic_bytes.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn bytes_operations_refuse_unmodeled_dynamic_shapes_and_partial_specs() {
        let symbolic_repeat = verify_contract_module(
            "def repeated(value: bytes, count: int) -> bytes:\n    return value * count\n",
            "symbolic_bytes_repeat.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            symbolic_repeat.code,
            "frontend.python.contracts.bytes-repeat-symbolic-count-unsupported"
        );

        let symbolic_join = verify_contract_module(
            "from typing import List\n\ndef joined(values: List[bytes]) -> bytes:\n    return b'-'.join(values)\n",
            "symbolic_bytes_join.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            symbolic_join.code,
            "frontend.python.contracts.bytes-join-symbolic-list-unsupported"
        );

        let wrong_join = verify_contract_module(
            "from typing import List\n\ndef joined() -> bytes:\n    values: List[int] = [1]\n    return b'-'.join(values)\n",
            "wrong_bytes_join.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            wrong_join.code,
            "frontend.python.contracts.bytes-join-element-type"
        );

        let partial_spec = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef invalid(value: bytes) -> int:\n    Requires(value[0] == 1)\n    return 1\n",
            "bytes_index_specification.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            partial_spec.code,
            "frontend.python.contracts.partial-operation-in-spec"
        );
    }

    #[test]
    fn proves_integer_abs_power_and_extrema() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import List\n\ndef absolute(value: int) -> int:\n    Ensures(Result() >= 0)\n    return abs(value)\n\ndef fourth(value: int) -> int:\n    Ensures(Result() == value * value * value * value)\n    return value ** 4\n\ndef extremes(left: int, right: int) -> None:\n    low = min(left, right)\n    high = max(left, right)\n    assert low <= left and low <= right\n    assert high >= left and high >= right\n\ndef static_values() -> None:\n    values: List[int] = [3, -2, 8]\n    assert min(values) == -2\n    assert max(values) != 7\n",
            "integer_builtins.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn integer_builtins_refuse_unmodeled_partial_or_dynamic_forms() {
        let symbolic_power = verify_contract_module(
            "def power(value: int, exponent: int) -> int:\n    return value ** exponent\n",
            "symbolic_power.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            symbolic_power.code,
            "frontend.python.contracts.power-symbolic-exponent-unsupported"
        );

        let negative_power = verify_contract_module(
            "def power(value: int) -> int:\n    return value ** -1\n",
            "negative_power.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            negative_power.code,
            "frontend.python.contracts.power-negative-exponent-unsupported"
        );

        let oversized_power = verify_contract_module(
            "def power(value: int) -> int:\n    return value ** 65\n",
            "oversized_power.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            oversized_power.code,
            "frontend.python.contracts.power-expansion-limit"
        );

        let empty_min = verify_contract_module(
            "from typing import List\n\ndef smallest() -> int:\n    values: List[int] = []\n    return min(values)\n",
            "empty_min.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(empty_min.code, "frontend.python.contracts.extremum-empty");

        let symbolic_min = verify_contract_module(
            "from typing import List\n\ndef smallest(values: List[int]) -> int:\n    return min(values)\n",
            "symbolic_min.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            symbolic_min.code,
            "frontend.python.contracts.extremum-symbolic-iterable-unsupported"
        );

        let module_print = verify_contract_module(
            "def value() -> int:\n    return 1\n\nprint('not part of the proved function')\n",
            "module_print.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            module_print.code,
            "frontend.python.contracts.module-statement-unsupported"
        );

        let integer_identity = verify_contract_module(
            "def same(left: int, right: int) -> bool:\n    return left is right\n",
            "integer_identity.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            integer_identity.code,
            "frontend.python.contracts.identity-operator-unsupported"
        );
    }

    #[test]
    fn static_slice_zero_step_and_symbolic_sequence_refuse() {
        let zero_step = verify_contract_module(
            "def broken() -> None:\n    values = [1, 2, 3]\n    sliced = values[::0]\n",
            "zero_step.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(zero_step.code, "frontend.python.contracts.slice-step-zero");

        let symbolic = verify_contract_module(
            "from typing import List\n\ndef broken(values: List[int]) -> None:\n    sliced = values[:]\n",
            "symbolic_slice.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            symbolic.code,
            "frontend.python.contracts.slice-symbolic-sequence-unsupported"
        );
    }

    #[test]
    fn refuses_heterogeneous_or_mutated_lists_and_unproved_symbolic_indexing() {
        let heterogeneous = verify_contract_module(
            "from typing import List\n\ndef broken() -> None:\n    values: List[int] = [1, 'two']\n",
            "heterogeneous_list.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            heterogeneous.code,
            "frontend.python.contracts.type-mismatch"
        );

        let mutation = verify_contract_module(
            "from typing import List\n\ndef broken() -> None:\n    values: List[int] = [1]\n    values.append(2)\n",
            "mutated_list.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            mutation.code,
            "frontend.python.contracts.statement-unsupported"
        );

        let symbolic_index = verify_contract_module(
            "from typing import List\n\ndef broken(values: List[int]) -> int:\n    return values[0]\n",
            "symbolic_list_index.py",
            &[],
        )
        .unwrap();
        assert!(!symbolic_index.passed);
        assert!(symbolic_index.obligations.iter().any(|item| {
            item.id.contains(":exception-undeclared:IndexError:")
                && item.status == ObligationStatus::Refuted
        }));

        let symbolic_forall = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import List\n\ndef broken(values: List[int]) -> None:\n    Assert(Forall(values, lambda value: (value > 0, [])))\n",
            "symbolic_list_forall.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            symbolic_forall.code,
            "frontend.python.contracts.forall-symbolic-collection-unsupported"
        );

        let zero_step = verify_contract_module(
            "def broken() -> None:\n    values = range(0, 3, 0)\n",
            "zero_step_range.py",
            &[],
        )
        .unwrap();
        assert!(!zero_step.passed);
        assert!(zero_step.obligations.iter().any(|item| {
            item.id
                .contains(":exception-undeclared:ValueError:application-precondition:")
                && item.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn models_zero_step_range_as_a_typed_value_error_with_short_circuiting() {
        let caught = verify_contract_module(
            "def caught() -> range:\n    try:\n        return range(0, 3, 0)\n    except ValueError:\n        return range(0)\n",
            "caught_zero_step_range.py",
            &[],
        )
        .unwrap();
        assert!(caught.passed);

        let declared = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef declared() -> range:\n    Exsures(ValueError, True)\n    return range(0, 3, 0)\n",
            "declared_zero_step_range.py",
            &[],
        )
        .unwrap();
        assert!(declared.passed);

        let short_circuited = verify_contract_module(
            "def safe() -> range:\n    return range(1) or range(0, 3, 0)\n",
            "short_circuit_zero_step_range.py",
            &[],
        )
        .unwrap();
        assert!(short_circuited.passed);

        let evaluated = verify_contract_module(
            "def broken() -> range:\n    return range(0) or range(0, 3, 0)\n",
            "evaluated_zero_step_range.py",
            &[],
        )
        .unwrap();
        assert!(!evaluated.passed);

        let specification = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef invalid() -> None:\n    Requires(range(0, 3, 0) == range(0))\n",
            "zero_step_range_specification.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            specification.code,
            "frontend.python.contracts.partial-operation-in-spec"
        );
    }

    #[test]
    fn symbolic_list_indexing_proves_bounds_or_exposes_typed_index_error() {
        let bounded = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import List\n\ndef first(values: List[int]) -> int:\n    Requires(len(values) > 0)\n    return values[0]\n\ndef last(values: List[int]) -> int:\n    Requires(len(values) > 0)\n    return values[-1]\n\ndef branched(values: List[int]) -> int:\n    if len(values) > 0:\n        return values[0]\n    return 0\n",
            "bounded_list_index.py",
            &[],
        )
        .unwrap();
        assert!(bounded.passed);

        let declared = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import List\n\ndef first(values: List[int]) -> int:\n    Exsures(IndexError, len(values) == 0)\n    return values[0]\n",
            "declared_list_index_error.py",
            &[],
        )
        .unwrap();
        assert!(declared.passed);

        let caught = verify_contract_module(
            "from typing import List\n\ndef first_or_default(values: List[int]) -> int:\n    try:\n        return values[0]\n    except IndexError:\n        return -1\n",
            "caught_list_index_error.py",
            &[],
        )
        .unwrap();
        assert!(caught.passed);

        let specification = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import List\n\ndef invalid(values: List[int]) -> int:\n    Requires(values[0] > 0)\n    return values[0]\n",
            "partial_list_specification.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            specification.code,
            "frontend.python.contracts.partial-operation-in-spec"
        );
    }

    #[test]
    fn typed_lambda_postconditions_and_guarded_dynamic_tuple_indices_are_sound() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef choose(values: Tuple[int, int, int], index: int) -> int:\n    Requires(-3 <= index and index < 3)\n    Requires(values[0] >= 0 and values[1] >= 0 and values[2] >= 0)\n    Ensures(int, lambda returned: returned >= 5)\n    Ensures(Implies(index == -3 or index == 0, Result() == values[0] + 5))\n    Ensures(Implies(index == -2 or index == 1, Result() == values[1] + 5))\n    Ensures(Implies(index == -1 or index == 2, Result() == values[2] + 5))\n    return values[index] + 5\n\ndef mixed(values: Tuple[int, bool, int], index: int) -> int:\n    Requires(0 <= index and index < 3)\n    Requires(values[0] >= 0 and values[2] >= 0)\n    Ensures(int, lambda returned: returned >= 0)\n    Ensures(Implies(index == 1, Result() == values[1]))\n    return values[index]\n",
            "typed_lambda_dynamic_tuple.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);

        let refuted = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef broken(value: int) -> int:\n    Ensures(int, lambda returned: returned > value)\n    return value\n",
            "typed_lambda_refuted.py",
            &[],
        )
        .unwrap();
        assert!(!refuted.passed);
        assert!(refuted.obligations.iter().any(|item| {
            item.id.contains(":postcondition:") && item.status == ObligationStatus::Refuted
        }));

        let mismatch = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef wrong() -> int:\n    Ensures(bool, lambda returned: returned)\n    return 1\n",
            "typed_lambda_wrong_result.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            mismatch.code,
            "frontend.python.contracts.postcondition-lambda-result-type"
        );

        let malformed = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef wrong() -> int:\n    Ensures(int, lambda left, right: left == right)\n    return 1\n",
            "typed_lambda_wrong_signature.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            malformed.code,
            "frontend.python.contracts.postcondition-lambda-signature"
        );

        let exposed = verify_contract_module(
            "from typing import Tuple\n\ndef choose(values: Tuple[int, int], index: int) -> int:\n    return values[index]\n",
            "dynamic_tuple_index_error.py",
            &[],
        )
        .unwrap();
        assert!(!exposed.passed);
        assert!(exposed.obligations.iter().any(|item| {
            item.id.contains(":exception-undeclared:IndexError:")
                && item.status == ObligationStatus::Refuted
        }));

        let incompatible = verify_contract_module(
            "from typing import Tuple\n\ndef choose(values: Tuple[int, str], index: int) -> int:\n    return values[index]\n",
            "dynamic_tuple_incompatible.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            incompatible.code,
            "frontend.python.contracts.tuple-index-dynamic-heterogeneous"
        );

        let partial_specification = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef choose(values: Tuple[int, int], index: int) -> int:\n    Requires(values[index] >= 0)\n    return values[0]\n",
            "dynamic_tuple_specification.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            partial_specification.code,
            "frontend.python.contracts.partial-operation-in-spec"
        );
    }

    #[test]
    fn immutable_module_initialization_is_ordered_typed_and_captured() {
        let globals = verify_contract_module(
            "from nagini_contracts.contracts import *\n\nBASE: int = 4\nENABLED = True\nOFFSET = BASE if ENABLED else 9\n\n@Pure\ndef read() -> int:\n    Ensures(Result() == 4)\n    return OFFSET\n",
            "immutable_globals.py",
            &[],
        )
        .unwrap();
        assert!(globals.passed);

        let empty = verify_contract_module("", "empty.py", &[]).unwrap();
        assert!(empty.passed);
        assert!(empty.functions.is_empty());

        let later_binding = verify_contract_module(
            "def read() -> int:\n    return LATER\n\nEARLY = read()\nLATER = 1\n",
            "later_global.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(later_binding.code, "frontend.python.name.unresolved");

        let duplicate =
            verify_contract_module("VALUE = 1\nVALUE = 2\n", "duplicate_global.py", &[])
                .unwrap_err();
        assert_eq!(
            duplicate.code,
            "frontend.python.contracts.module-binding-reassigned"
        );

        let future_function_collision = verify_contract_module(
            "run = 1\n\ndef run() -> int:\n    return 2\n",
            "global_before_function.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            future_function_collision.code,
            "frontend.python.contracts.module-binding-reassigned"
        );

        let wrong_annotation =
            verify_contract_module("VALUE: bool = 1\n", "wrong_global_annotation.py", &[])
                .unwrap_err();
        assert_eq!(
            wrong_annotation.code,
            "frontend.python.contracts.type-mismatch"
        );

        let total_literal_index = verify_contract_module(
            "from nagini_contracts.contracts import *\n\nVALUES = [1]\nFIRST = VALUES[0]\n\ndef read_first() -> int:\n    Ensures(Result() == 1)\n    return FIRST\n",
            "total_literal_global_index.py",
            &[],
        )
        .unwrap();
        assert!(total_literal_index.passed);

        let local_shadow = verify_contract_module(
            "BASE = 4\n\ndef broken() -> int:\n    copy = BASE\n    BASE = 5\n    return copy\n",
            "local_shadows_global.py",
            &[],
        )
        .unwrap();
        assert!(!local_shadow.passed);
        assert!(local_shadow.obligations.iter().any(|obligation| {
            obligation.id.contains(":undefined-local:BASE:") && !obligation.satisfied()
        }));

        let explicit_mutation = verify_contract_module(
            "BASE = 4\n\ndef broken() -> int:\n    global BASE\n    BASE = 5\n    return BASE\n",
            "global_mutation.py",
            &[],
        )
        .unwrap();
        assert!(!explicit_mutation.passed);
        assert!(
            explicit_mutation.obligations.iter().any(|obligation| {
                obligation.id.contains(":field-write-permission:BASE:") && !obligation.satisfied()
            }),
            "{explicit_mutation:#?}"
        );

        let (_, provider) = verify_and_export_source_contract_module(
            "from nagini_contracts.contracts import *\n\nOFFSET = 3\n\ndef add(value: int) -> int:\n    Ensures(Result() == value + OFFSET)\n    return value + OFFSET\n",
            "provider.py",
            "provider",
            &[],
        )
        .unwrap();
        let caller = verify_contract_module_with_imports(
            "from provider import add\nfrom nagini_contracts.contracts import *\n\nOFFSET = 100\n\ndef run() -> int:\n    Ensures(Result() == 5)\n    return add(2)\n",
            "caller.py",
            &[],
            &[provider],
        )
        .unwrap();
        assert!(caller.passed);
    }

    #[test]
    fn builtin_type_object_aliases_are_ordered_and_shadow_aware() {
        let alias = verify_contract_module("TextIO = int\n", "builtin_type_alias.py", &[])
            .expect("the canonical builtin type object is a total module initializer");
        assert!(alias.passed);

        let source = "int = 7\nTextIO = int\n";
        let suite = ast::Suite::parse(source, "shadowed_builtin_type.py").unwrap();
        let hierarchy = ExceptionHierarchy::from_suite(&suite).unwrap();
        let globals = derive_immutable_module_globals(
            &suite,
            ModuleDerivationContext {
                source,
                path: "shadowed_builtin_type.py",
                functions: &BTreeMap::new(),
                type_comments: &BTreeMap::new(),
                exception_hierarchy: &hierarchy,
                conformance_mode: false,
                identity: &ModuleIdentity::entry("shadowed_builtin_type.py"),
            },
        )
        .unwrap();
        assert_eq!(globals.values.get("TextIO"), Some(&Term::Int { value: 7 }));

        let imported = ast::Suite::parse(
            "from provider import int\nTextIO = int\n",
            "import_shadowed_builtin_type.py",
        )
        .unwrap();
        let hierarchy = ExceptionHierarchy::from_suite(&imported).unwrap();
        let error = derive_immutable_module_globals(
            &imported,
            ModuleDerivationContext {
                source: "from provider import int\nTextIO = int\n",
                path: "import_shadowed_builtin_type.py",
                functions: &BTreeMap::new(),
                type_comments: &BTreeMap::new(),
                exception_hierarchy: &hierarchy,
                conformance_mode: false,
                identity: &ModuleIdentity::entry("import_shadowed_builtin_type.py"),
            },
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.python.name.unresolved");
    }

    #[test]
    fn module_list_mutation_records_exact_python_evaluation_order_once() {
        let source = "from typing import List\nvalues: List[int] = [2, 3]\nvalues[1] += 4\n";
        let suite = ast::Suite::parse(source, "module_list_order.py").unwrap();
        let hierarchy = ExceptionHierarchy::from_suite(&suite).unwrap();
        let globals = derive_immutable_module_globals(
            &suite,
            ModuleDerivationContext {
                source,
                path: "module_list_order.py",
                functions: &BTreeMap::new(),
                type_comments: &BTreeMap::new(),
                exception_hierarchy: &hierarchy,
                conformance_mode: false,
                identity: &ModuleIdentity::entry("module_list_order.py"),
            },
        )
        .unwrap();
        assert_eq!(globals.list_mutations.len(), 1);
        let record = &globals.list_mutations[0];
        assert_eq!(record.binding, "values");
        assert_eq!(record.index, 1);
        assert_eq!(
            record.evaluation,
            [
                ModuleListMutationStep::Container,
                ModuleListMutationStep::Index,
                ModuleListMutationStep::Read,
                ModuleListMutationStep::RightHandSide,
                ModuleListMutationStep::PrimitiveOperation,
                ModuleListMutationStep::Store,
            ]
        );
        assert_eq!(record.previous, Term::Int { value: 3 });
        assert_eq!(record.right, Term::Int { value: 4 });
        assert_eq!(
            globals.values.get("values"),
            Some(&Term::List {
                element_sort: Sort::Int,
                values: vec![
                    Term::Int { value: 2 },
                    Term::Add {
                        left: Box::new(Term::Int { value: 3 }),
                        right: Box::new(Term::Int { value: 4 }),
                    },
                ],
            })
        );
    }

    #[test]
    fn models_python_value_returning_boolean_and_conditional_expressions() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef conjunction(left: int, right: int) -> int:\n    Ensures(Implies(left == 0, Result() == left))\n    Ensures(Implies(left != 0, Result() == right))\n    return left and right\n\ndef disjunction(left: int, right: int) -> int:\n    Ensures(Implies(left != 0, Result() == left))\n    Ensures(Implies(left == 0, Result() == right))\n    return left or right\n\ndef choose(flag: bool) -> int:\n    Ensures(Implies(flag, Result() == 4))\n    Ensures(Implies(not flag, Result() == 7))\n    return 4 if flag else 7\n\ndef truthiness() -> bool:\n    Ensures(Result())\n    return (not 0) and (not '') and (not None) and ((not [1]) == False)\n",
            "python_value_selection.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);

        let incompatible = verify_contract_module(
            "from typing import List\n\ndef broken(flag: int) -> List[int]:\n    return flag and [1]\n",
            "incompatible_conditional_result.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            incompatible.code,
            "frontend.python.contracts.conditional-result-type"
        );

        let dead_branch = verify_contract_module(
            "def broken() -> int:\n    return 1 if True else 'not an int'\n",
            "dead_branch_type_error.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            dead_branch.code,
            "frontend.python.contracts.conditional-result-type"
        );
    }

    #[test]
    fn short_circuit_and_conditional_evaluation_guard_partial_list_indexing() {
        let safe = verify_contract_module(
            "from typing import List\n\ndef safe_and(values: List[int]) -> bool:\n    return False and values[0] > 0\n\ndef safe_or(values: List[int]) -> bool:\n    return True or values[0] > 0\n\ndef first_or_default(values: List[int]) -> int:\n    return values[0] if len(values) > 0 else -1\n\ndef constant_choice(values: List[int]) -> int:\n    return 1 if True else values[0]\n",
            "short_circuit_index.py",
            &[],
        )
        .unwrap();
        assert!(safe.passed);

        let exposed = verify_contract_module(
            "from typing import List\n\ndef maybe_first(flag: bool, values: List[int]) -> int:\n    return values[0] if flag else -1\n",
            "conditional_index_error.py",
            &[],
        )
        .unwrap();
        assert!(!exposed.passed);
        assert!(exposed.obligations.iter().any(|item| {
            item.id.contains(":exception-undeclared:IndexError:")
                && item.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn proves_chained_comparisons_and_their_short_circuit_evaluation() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import List\n\ndef transitive(left: int, middle: int, right: int) -> None:\n    Requires(left < middle < right)\n    assert left < right\n\ndef chained_equal(left: int, middle: int, right: int) -> bool:\n    Ensures(Implies(Result(), left == right))\n    return left == middle == right\n\ndef skipped_index(values: List[int]) -> bool:\n    return 1 > 2 < values[0]\n",
            "chained_comparisons.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);

        let exposed = verify_contract_module(
            "from typing import List\n\ndef reachable_index(values: List[int]) -> bool:\n    return 1 < 2 < values[0]\n",
            "chained_comparison_index_error.py",
            &[],
        )
        .unwrap();
        assert!(!exposed.passed);
        assert!(exposed.obligations.iter().any(|item| {
            item.id.contains(":exception-undeclared:IndexError:")
                && item.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn executes_finite_and_symbolic_list_for_loops_and_static_membership() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\nfrom typing import List\n\ndef total() -> int:\n    result = 0\n    for value in range(1, 4):\n        result += value\n    else:\n        result += 1\n    assert result == 7\n    return result\n\ndef membership() -> None:\n    values: List[int] = [1, 3, 5]\n    assert 3 in values\n    assert 2 not in values\n    assert True in values\n\ndef empty_retains_target() -> int:\n    value = 9\n    for value in range(0):\n        value = 1\n    return value\n",
            "finite_for.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);

        let symbolic = verify_contract_module(
            "from typing import List\n\ndef supported(values: List[int]) -> None:\n    for value in values:\n        assert value == value\n",
            "symbolic_for.py",
            &[],
        )
        .unwrap();
        assert!(symbolic.passed);

        let break_statement = verify_contract_module(
            "def unsupported() -> None:\n    for value in range(3):\n        break\n",
            "finite_for_break.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            break_statement.code,
            "frontend.python.contracts.statement-unsupported"
        );
    }

    #[test]
    fn unused_local_callable_shadow_is_safe_but_calling_it_refuses() {
        let result = verify_contract_module(
            "def helper() -> int:\n    return 1\n\ndef harmless() -> int:\n    helper = [4]\n    return helper[0]\n",
            "unused_callable_shadow.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);

        let error = verify_contract_module(
            "def helper() -> int:\n    return 1\n\ndef broken() -> int:\n    helper = 4\n    return helper()\n",
            "called_callable_shadow.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.python.contracts.callable-shadowed");
    }

    #[test]
    fn optional_assignment_type_comments_preserve_both_exact_branches() {
        for source in [
            "from typing import Optional\n\ndef maybe() -> None:\n    value = None  # type: Optional[int]\n    assert value == None\n",
            "from typing import Optional\n\ndef maybe() -> None:\n    value = 7  # type: Optional[int]\n    assert value == 7\n",
        ] {
            let result = verify_contract_module(source, "optional_type_comment.py", &[]).unwrap();
            assert!(result.passed);
        }

        let wrong_member = verify_contract_module(
            "from typing import Optional\n\ndef wrong() -> None:\n    value = 'seven'  # type: Optional[int]\n",
            "optional_type_comment_wrong_member.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(wrong_member.code, "frontend.python.contracts.type-mismatch");

        let unsupported_member = verify_contract_module(
            "from typing import Optional\n\ndef wrong() -> None:\n    value = None  # type: Optional[complex]\n",
            "optional_type_comment_unsupported_member.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            unsupported_member.code,
            "frontend.python.contracts.type-comment-unsupported"
        );

        let non_optional_none = verify_contract_module(
            "def wrong() -> None:\n    value = None  # type: int\n",
            "non_optional_none_type_comment.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            non_optional_none.code,
            "frontend.python.contracts.type-mismatch"
        );
    }

    #[test]
    fn enforces_scalar_assignment_type_comments_from_lexer_tokens() {
        let result = verify_contract_module(
            "def typed() -> None:\n    value = 1  # type: int\n    assert value == 1\n",
            "scalar_type_comment.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);

        let error = verify_contract_module(
            "def wrong() -> None:\n    value = 1  # type: bool\n",
            "wrong_type_comment.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.python.contracts.type-mismatch");

        let result = verify_contract_module(
            "from typing import Tuple\n\ndef typed_tuple() -> None:\n    value = (1, 'text')  # type: Tuple[int, str]\n    assert value[0] == 1\n",
            "tuple_type_comment.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn does_not_honor_external_type_ignore_suppressions() {
        let result = verify_contract_module(
            "def identity(value: int) -> int:\n    return value  # type: ignore[return-value]\n",
            "ignored_suppression.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn refutes_false_assertion_with_counterexample() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef positive(value: int) -> int:\n    assert value > 0\n    return value\n",
            "false.py",
            &["positive".to_owned()],
        )
        .unwrap();
        assert!(!result.passed);
        assert_eq!(result.obligations[0].status, ObligationStatus::Refuted);
        assert!(result.obligations[0].counterexample.is_some());
    }

    #[test]
    fn refuses_unsupported_call_instead_of_abstracting_it() {
        let error = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef opaque(value: int) -> int:\n    assert unknown(value) > 0\n    return value\n",
            "opaque.py",
            &["opaque".to_owned()],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.expression-unsupported"
        );
    }

    #[test]
    fn supports_pure_decorator_and_annotated_scalar_locals() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Pure\ndef compare(left: int, right: int, flag: bool) -> bool:\n    Requires(left > right)\n    Ensures(Result() == flag)\n    total: int = left + 1\n    comparison: bool = total > right\n    return flag == comparison\n",
            "pure.py",
            &["compare".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn symbolically_executes_both_if_return_paths() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Pure\ndef maximum(left: int, right: int) -> int:\n    Ensures(Result() >= left and Result() >= right)\n    if left > right:\n        return left\n    return right\n",
            "branch.py",
            &["maximum".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
        assert_eq!(result.obligations.len(), 2);
    }

    #[test]
    fn refutes_contract_assert_on_only_the_reachable_branch() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Pure\ndef broken(left: int, right: int) -> int:\n    Ensures(Result() >= left and Result() >= right)\n    if left > right:\n        Assert(left == right)\n        return left\n    return right\n",
            "branch.py",
            &["broken".to_owned()],
        )
        .unwrap();
        assert!(!result.passed);
        assert!(result.obligations.iter().any(|item| {
            item.id.contains(":pure-assert:") && item.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn refutes_a_reachable_missing_return_path() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Pure\ndef partial(value: int) -> int:\n    if value > 0:\n        return value\n",
            "partial.py",
            &["partial".to_owned()],
        )
        .unwrap();
        assert!(!result.passed);
        assert!(result.obligations.iter().any(|item| {
            item.id.contains(":function-totality:") && item.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn proves_missing_return_path_unreachable_from_precondition() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Pure\ndef constrained(value: int) -> int:\n    Requires(value > 0)\n    if value > 0:\n        return value\n",
            "constrained.py",
            &["constrained".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn total_return_is_a_non_vacuous_obligation_without_postconditions() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Pure\ndef identity(value: int) -> int:\n    return value\n",
            "identity.py",
            &["identity".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
        assert_eq!(result.obligations.len(), 1);
        assert!(
            result.obligations[0]
                .id
                .contains(":function-totality:complete")
        );
    }

    #[test]
    fn refute_obligation_succeeds_only_when_claim_is_not_provable() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef checks(value: int) -> None:\n    Requires(value > 0)\n    Refute(value < 0)\n    Refute(value > 0)\n",
            "refute.py",
            &["checks".to_owned()],
        )
        .unwrap();
        assert!(!result.passed);
        let refutations: Vec<_> = result
            .obligations
            .iter()
            .filter(|item| item.expectation == ObligationExpectation::Refute)
            .collect();
        assert_eq!(refutations.len(), 2);
        assert!(refutations[0].satisfied());
        assert!(!refutations[1].satisfied());
    }

    #[test]
    fn inlines_typed_source_function_and_coerces_bool_to_int() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef twice(value: int) -> int:\n    return value * 2\n\ndef caller() -> int:\n    Ensures(Result() == 2)\n    return twice(True)\n",
            "calls.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn proves_each_source_call_precondition_at_the_call_site() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef positive(value: int) -> None:\n    Requires(value > 0)\n\ndef caller() -> None:\n    positive(1)\n    positive(0)\n",
            "call_precondition.py",
            &[],
        )
        .unwrap();
        assert!(!result.passed);
        let calls: Vec<_> = result
            .obligations
            .iter()
            .filter(|item| item.id.contains(":call-precondition:"))
            .collect();
        assert_eq!(calls.len(), 2);
        assert!(calls[0].satisfied());
        assert!(!calls[1].satisfied());
        assert_eq!(calls[1].line, 8);
    }

    #[test]
    fn imports_verified_postconditions_into_assignment_callers() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef successor(value: int) -> int:\n    Requires(value > 0)\n    Ensures(Result() == value + 1)\n    return value + 1\n\ndef caller() -> None:\n    result = successor(4)\n    assert result == 5\n",
            "call_postcondition.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn modular_assignment_call_does_not_leak_the_callee_body() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef identity(value: int) -> int:\n    Requires(True)\n    return value\n\ndef caller() -> None:\n    result = identity(5)\n    assert result == 5\n",
            "modular_call.py",
            &[],
        )
        .unwrap();
        assert!(!result.passed);
        assert!(result.obligations.iter().any(|item| {
            item.id.contains(":assert:") && item.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn composes_source_contracts_through_a_return_call() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef identity(value: int) -> int:\n    Requires(value > 0)\n    Ensures(Result() == value)\n    return value\n\ndef wrapper(value: int) -> int:\n    Requires(value > 0)\n    Ensures(Result() == value)\n    return identity(value)\n",
            "return_call.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
        assert!(
            result
                .obligations
                .iter()
                .any(|item| item.id.contains("wrapper:call-precondition:"))
        );
    }

    #[test]
    fn refuses_recursive_inline_without_termination_contract() {
        let error = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Pure\ndef loop(value: int) -> int:\n    return loop(value)\n",
            "recursive.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.recursive-inline-call"
        );
    }

    #[test]
    fn checks_loop_invariant_establishment_and_preservation() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef count() -> int:\n    Ensures(Result() == 3)\n    value = 0\n    while value < 3:\n        Invariant(value >= 0 and value <= 3)\n        value += 1\n    return value\n",
            "loop.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
        assert!(
            result
                .obligations
                .iter()
                .any(|item| item.id.contains(":invariant-establishment:"))
        );
        assert!(
            result
                .obligations
                .iter()
                .any(|item| item.id.contains(":invariant-preservation:"))
        );
    }

    #[test]
    fn external_contracts_are_typed_and_used_modularly() {
        let external = parse_external_contract_module(
            "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef successor(value: int) -> int:\n    Requires(value > 0)\n    Ensures(Result() == value + 1)\n    ...\n",
            "provider_contract.py",
            "provider",
        )
        .unwrap();
        let result = verify_contract_module_with_imports(
            "from provider import successor\nfrom nagini_contracts.contracts import *\n\ndef run() -> int:\n    Ensures(Result() == 2)\n    return successor(1)\n",
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
                .any(|item| item.id.contains(":call-precondition:"))
        );
    }

    #[test]
    fn external_custom_exception_subclass_is_caught_through_imported_base() {
        let external = parse_external_contract_module(
            "from nagini_contracts.contracts import *\n\nclass ProviderError(Exception):\n    pass\n\nclass SpecificProviderError(ProviderError):\n    pass\n\n@ContractOnly\ndef maybe(flag: bool) -> int:\n    Ensures(not flag and Result() == 1)\n    Exsures(SpecificProviderError, flag)\n    ...\n",
            "provider_contract.py",
            "provider",
        )
        .unwrap();
        assert_eq!(
            external.exception_type_names(),
            ["provider.ProviderError", "provider.SpecificProviderError"]
        );
        let result = verify_contract_module_with_imports(
            "from provider import maybe, ProviderError\nfrom nagini_contracts.contracts import *\n\ndef run(flag: bool) -> int:\n    Ensures(Implies(flag, Result() == 2))\n    Ensures(Implies(not flag, Result() == 1))\n    try:\n        return maybe(flag)\n    except ProviderError:\n        return 2\n",
            "adapter.py",
            &["run".to_owned()],
            &[external],
        )
        .unwrap();
        assert!(result.passed);
    }

    #[test]
    fn refuses_aliasing_imported_exception_identity() {
        let external = parse_external_contract_module(
            "from nagini_contracts.contracts import *\n\nclass ProviderError(Exception):\n    pass\n\n@ContractOnly\ndef maybe() -> int:\n    Exsures(ProviderError, True)\n    ...\n",
            "provider_contract.py",
            "provider",
        )
        .unwrap();
        let error = verify_contract_module_with_imports(
            "from provider import maybe, ProviderError as RenamedError\n\ndef run() -> int:\n    try:\n        return maybe()\n    except RenamedError:\n        return 2\n",
            "adapter.py",
            &["run".to_owned()],
            &[external],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contract-import.exception-alias-unsupported"
        );
    }

    #[test]
    fn refuses_same_exception_spelling_from_distinct_provider_modules() {
        let first = parse_external_contract_module(
            "from nagini_contracts.contracts import *\n\nclass ProviderError(Exception):\n    pass\n\n@ContractOnly\ndef first() -> int:\n    Exsures(ProviderError, True)\n    ...\n",
            "first_contract.py",
            "first_provider",
        )
        .unwrap();
        let second = parse_external_contract_module(
            "from nagini_contracts.contracts import *\n\nclass ProviderError(Exception):\n    pass\n\n@ContractOnly\ndef second() -> int:\n    Exsures(ProviderError, True)\n    ...\n",
            "second_contract.py",
            "second_provider",
        )
        .unwrap();
        let error = verify_contract_module_with_imports(
            "from first_provider import first\nfrom second_provider import second\n\ndef run() -> int:\n    first()\n    return second()\n",
            "adapter.py",
            &["run".to_owned()],
            &[first, second],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.exception-hierarchy-conflict"
        );
    }

    #[test]
    fn typed_exception_binding_tracks_exact_nominal_type_and_is_cleaned_up() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\nclass BaseError(Exception):\n    pass\n\nclass SpecificError(BaseError):\n    pass\n\ndef maybe(flag: bool) -> None:\n    Ensures(not flag)\n    Exsures(SpecificError, flag)\n    if flag:\n        raise SpecificError()\n\ndef run(flag: bool) -> bool:\n    Ensures(Result() == flag)\n    try:\n        maybe(flag)\n    except BaseError as error:\n        return isinstance(error, SpecificError) and isinstance(error, BaseError)\n    return False\n",
            "typed_exception_binding.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);

        let error = verify_contract_module(
            "class AppError(Exception):\n    pass\n\ndef run() -> None:\n    try:\n        raise AppError()\n    except AppError as error:\n        pass\n    return error\n",
            "cleaned_exception_binding.py",
            &[],
        )
        .unwrap();
        assert!(!error.passed);
        assert!(error.obligations.iter().any(|obligation| {
            obligation.id.contains(":undefined-local:error:") && !obligation.satisfied()
        }));
    }

    #[test]
    fn typed_exception_binding_refutes_an_unrelated_nominal_type() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\nclass BaseError(Exception):\n    pass\n\nclass SpecificError(BaseError):\n    pass\n\nclass OtherError(Exception):\n    pass\n\ndef maybe() -> None:\n    Exsures(SpecificError, True)\n    raise SpecificError()\n\ndef broken() -> None:\n    try:\n        maybe()\n    except BaseError as error:\n        Assert(isinstance(error, OtherError))\n",
            "unrelated_exception_binding.py",
            &[],
        )
        .unwrap();
        assert!(!result.passed);
        assert!(result.obligations.iter().any(|item| {
            item.id.contains(":assert:") && item.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn refuses_unsupported_expression_in_unreachable_handler() {
        let error = verify_contract_module(
            "def run() -> None:\n    try:\n        pass\n    except ValueError:\n        isinstance(1, int)\n",
            "unreachable_handler_body.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.statement-unsupported"
        );
    }

    #[test]
    fn refuses_unsupported_statement_after_return() {
        let error = verify_contract_module(
            "def run() -> int:\n    return 1\n    with resource():\n        pass\n",
            "after_return.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.statement-unsupported"
        );
    }

    #[test]
    fn external_contract_rejects_executable_provider_body() {
        let error = parse_external_contract_module(
            "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef successor(value: int) -> int:\n    return value + 1\n",
            "provider_contract.py",
            "provider",
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.external.body-not-contract-only"
        );
    }

    #[test]
    fn external_contract_rejects_untyped_or_invalid_clauses_even_when_unused() {
        let error = parse_external_contract_module(
            "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef broken(value: int) -> int:\n    Ensures(Result() + value)\n    ...\n",
            "provider_contract.py",
            "provider",
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.python.contracts.expected-bool");
    }

    #[test]
    fn external_callable_cannot_be_shadowed_by_a_runtime_value() {
        let external = parse_external_contract_module(
            "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef successor(value: int) -> int:\n    Ensures(Result() == value + 1)\n    ...\n",
            "provider_contract.py",
            "provider",
        )
        .unwrap();
        let error = verify_contract_module_with_imports(
            "from provider import successor\n\ndef run() -> int:\n    successor = 1\n    return successor(1)\n",
            "adapter.py",
            &["run".to_owned()],
            &[external],
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.python.contracts.callable-shadowed");
    }

    #[test]
    fn verified_source_module_contract_composes_into_a_caller() {
        let (_, dependency) = verify_and_export_source_contract_module(
            "from nagini_contracts.contracts import *\n\ndef successor(value: int) -> int:\n    Requires(value > 0)\n    Ensures(Result() == value + 1)\n    return value + 1\n",
            "math_helpers.py",
            "math_helpers",
            &[],
        )
        .unwrap();
        let caller = verify_contract_module_with_imports(
            "from math_helpers import successor\nfrom nagini_contracts.contracts import *\n\ndef run() -> int:\n    Ensures(Result() == 3)\n    return successor(2)\n",
            "app.py",
            &["run".to_owned()],
            &[dependency],
        )
        .unwrap();
        assert!(caller.passed);
    }

    #[test]
    fn refuted_source_module_cannot_export_a_trusted_summary() {
        let error = verify_and_export_source_contract_module(
            "from nagini_contracts.contracts import *\n\ndef broken(value: int) -> int:\n    Ensures(Result() == value + 1)\n    return value\n",
            "broken.py",
            "broken",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contract-import.source-module-refuted"
        );
    }

    #[test]
    fn source_contract_import_scan_refuses_plain_and_describes_relative_imports() {
        let plain = source_contract_imports("import helper\n", "app.py").unwrap_err();
        assert_eq!(
            plain.code,
            "frontend.python.contract-import.plain-import-unsupported"
        );
        let relative =
            source_contract_import_requests("from .helper import run\n", "pkg/app.py").unwrap();
        assert_eq!(
            relative,
            [SourceContractImportRequest {
                module: "helper".to_owned(),
                relative_level: 1,
                imported_names: vec![("run".to_owned(), None)],
            }]
        );
        assert_eq!(
            source_contract_imports("from .helper import run\n", "pkg/app.py").unwrap(),
            ["helper"]
        );
    }

    #[test]
    fn proves_declared_exception_and_its_path_sensitive_exsures() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef maybe_raise(flag: bool) -> int:\n    Ensures(Result() == 1)\n    Exsures(ValueError, flag)\n    if flag:\n        raise ValueError()\n    return 1\n",
            "declared_exception.py",
            &["maybe_raise".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
        assert!(
            result
                .obligations
                .iter()
                .any(|item| item.id.contains(":exception-postcondition:"))
        );
    }

    #[test]
    fn proves_source_defined_exception_subclass_against_base_exsures() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\nclass AppError(Exception):\n    pass\n\nclass SpecificError(AppError):\n    pass\n\ndef maybe_raise(flag: bool) -> int:\n    Ensures(not flag and Result() == 1)\n    Exsures(AppError, flag)\n    if flag:\n        raise SpecificError()\n    return 1\n",
            "custom_exception.py",
            &["maybe_raise".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
        assert!(
            result
                .obligations
                .iter()
                .any(|item| { item.id.contains(":exception-postcondition:") && item.satisfied() })
        );
    }

    #[test]
    fn source_defined_base_handler_catches_source_defined_subclass() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\nclass AppError(Exception):\n    pass\n\nclass SpecificError(AppError):\n    pass\n\ndef recovered() -> int:\n    Ensures(Result() == 2)\n    try:\n        raise SpecificError()\n    except AppError:\n        return 2\n",
            "custom_exception_handler.py",
            &["recovered".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
        assert!(
            !result
                .obligations
                .iter()
                .any(|item| item.id.contains("recovered:exception-"))
        );
    }

    #[test]
    fn refuses_unresolved_exception_type_in_exsures() {
        let error = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef broken() -> None:\n    Exsures(MissingError, True)\n    raise ValueError()\n",
            "missing_exception_type.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.exception-type-unresolved"
        );
    }

    #[test]
    fn refuses_executable_source_exception_class_body() {
        let error = verify_contract_module(
            "class AppError(Exception):\n    code: int = 3\n\ndef run() -> None:\n    pass\n",
            "executable_exception_class.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.exception-class-body-unsupported"
        );
    }

    #[test]
    fn refutes_false_exceptional_postcondition() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef broken() -> None:\n    Exsures(ValueError, False)\n    raise ValueError()\n",
            "false_exsures.py",
            &[],
        )
        .unwrap();
        assert!(!result.passed);
        assert!(result.obligations.iter().any(|item| {
            item.id.contains(":exception-postcondition:")
                && item.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn refutes_undeclared_exceptional_exit() {
        let result = verify_contract_module(
            "def broken() -> None:\n    raise ValueError()\n",
            "undeclared_exception.py",
            &[],
        )
        .unwrap();
        assert!(!result.passed);
        assert!(result.obligations.iter().any(|item| {
            item.id.contains(":exception-undeclared:") && item.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn propagates_typed_exceptional_outcome_across_modular_call() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef callee(flag: bool) -> int:\n    Ensures(Result() == 1)\n    Exsures(ValueError, flag)\n    if flag:\n        raise ValueError()\n    return 1\n\ndef wrapper(flag: bool) -> int:\n    Ensures(Result() == 1)\n    Exsures(ValueError, flag)\n    return callee(flag)\n",
            "exceptional_call.py",
            &["wrapper".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
        assert!(result.obligations.iter().any(|item| {
            item.id.contains("wrapper:exception-postcondition:") && item.satisfied()
        }));
    }

    #[test]
    fn caller_must_declare_propagated_exceptional_outcome() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef callee() -> int:\n    Exsures(ValueError, True)\n    raise ValueError()\n\ndef wrapper() -> int:\n    return callee()\n",
            "undeclared_call_exception.py",
            &[],
        )
        .unwrap();
        assert!(!result.passed);
        assert!(result.obligations.iter().any(|item| {
            item.id.contains("wrapper:exception-undeclared:")
                && item.status == ObligationStatus::Refuted
        }));
    }

    #[test]
    fn typed_handler_converts_declared_call_exception_to_normal_return() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef callee(flag: bool) -> int:\n    Ensures(not flag and Result() == 1)\n    Exsures(ValueError, flag)\n    if flag:\n        raise ValueError()\n    return 1\n\ndef recovered(flag: bool) -> int:\n    Ensures(Implies(flag, Result() == 2))\n    Ensures(Implies(not flag, Result() == 1))\n    try:\n        return callee(flag)\n    except ValueError:\n        return 2\n",
            "caught_exception.py",
            &["recovered".to_owned()],
        )
        .unwrap();
        assert!(result.passed);
        assert!(
            !result
                .obligations
                .iter()
                .any(|item| item.id.contains("recovered:exception-"))
        );
    }

    #[test]
    fn nonmatching_handler_does_not_hide_exceptional_exit() {
        let result = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef propagated() -> None:\n    Exsures(TypeError, True)\n    try:\n        raise TypeError()\n    except ValueError:\n        pass\n",
            "nonmatching_handler.py",
            &[],
        )
        .unwrap();
        assert!(result.passed);
        assert!(
            result
                .obligations
                .iter()
                .any(|item| item.id.contains("propagated:exception-postcondition:"))
        );
    }

    #[test]
    fn imported_exception_hierarchy_survives_source_module_export() {
        let (_, provider) = verify_and_export_source_contract_module(
            "from nagini_contracts.contracts import *\n\nclass ProviderError(Exception):\n    pass\n\nclass SpecificProviderError(ProviderError):\n    pass\n\ndef maybe(flag: bool) -> int:\n    Ensures(not flag and Result() == 1)\n    Exsures(SpecificProviderError, flag)\n    if flag:\n        raise SpecificProviderError()\n    return 1\n",
            "provider.py",
            "provider",
            &[],
        )
        .unwrap();
        let (_, adapter) = verify_and_export_source_contract_module(
            "from provider import maybe, ProviderError\nfrom nagini_contracts.contracts import *\n\ndef recover(flag: bool) -> int:\n    Ensures(Implies(flag, Result() == 2))\n    Ensures(Implies(not flag, Result() == 1))\n    try:\n        return maybe(flag)\n    except ProviderError:\n        return 2\n",
            "adapter.py",
            "adapter",
            &[provider],
        )
        .unwrap();
        let caller = verify_contract_module_with_imports(
            "from adapter import recover\nfrom nagini_contracts.contracts import *\n\ndef run(flag: bool) -> int:\n    Ensures(Implies(flag, Result() == 2))\n    Ensures(Implies(not flag, Result() == 1))\n    return recover(flag)\n",
            "app.py",
            &["run".to_owned()],
            &[adapter],
        )
        .unwrap();
        assert!(caller.passed);
    }

    #[test]
    fn source_exception_can_subclass_an_explicitly_imported_base() {
        let (_, provider) = verify_and_export_source_contract_module(
            "class ProviderError(Exception):\n    pass\n\ndef marker() -> None:\n    pass\n",
            "provider.py",
            "provider",
            &[],
        )
        .unwrap();
        let (verification, adapter) = verify_and_export_source_contract_module(
            "from provider import ProviderError\nfrom nagini_contracts.contracts import *\n\nclass LocalError(ProviderError):\n    pass\n\ndef fail() -> None:\n    Exsures(ProviderError, True)\n    raise LocalError()\n",
            "adapter.py",
            "adapter",
            &[provider],
        )
        .unwrap();
        assert!(verification.passed);
        assert!(
            adapter
                .exception_type_names()
                .contains(&"adapter.LocalError".to_owned())
        );
    }

    #[test]
    fn ghost_declaration_is_verified_but_runtime_calls_refuse() {
        let declaration = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Ghost\ndef marker() -> None:\n    return\n",
            "ghost.py",
            &["marker".to_owned()],
        )
        .unwrap();
        assert!(declaration.passed);

        let error = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Ghost\ndef marker() -> None:\n    return\n\ndef invalid() -> None:\n    marker()\n",
            "ghost_call.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.ghost-call-unsupported"
        );
    }

    #[test]
    fn ghost_identity_survives_source_module_export() {
        let (_, provider) = verify_and_export_source_contract_module(
            "from nagini_contracts.contracts import *\n\n@Ghost\ndef marker() -> None:\n    return\n",
            "provider.py",
            "provider",
            &[],
        )
        .unwrap();
        let error = verify_contract_module_with_imports(
            "from provider import marker\n\ndef invalid() -> None:\n    marker()\n",
            "adapter.py",
            &[],
            &[provider],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.ghost-call-unsupported"
        );
    }

    #[test]
    fn opaque_requires_pure_and_its_body_is_still_verified() {
        let error = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Opaque\ndef invalid() -> int:\n    return 1\n",
            "opaque_without_pure.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(error.code, "frontend.python.contracts.opaque-requires-pure");

        let verification = verify_contract_module(
            "from nagini_contracts.contracts import *\n\n@Pure\n@Opaque\ndef invalid() -> int:\n    Ensures(Result() == 2)\n    return 1\n",
            "opaque_body.py",
            &[],
        )
        .unwrap();
        assert!(!verification.passed);
        assert_eq!(verification.obligations.len(), 1);
    }

    #[test]
    fn nested_preconditioned_call_requires_an_unconditional_bound_proof() {
        let error = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef positive(value: int) -> int:\n    Requires(value > 0)\n    return value\n\ndef caller(value: int) -> None:\n    assert positive(value) == value\n",
            "nested_symbolic_precondition.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.preconditioned-call-context-unsupported"
        );

        let verified = verify_contract_module(
            "from nagini_contracts.contracts import *\n\ndef positive(value: int) -> int:\n    Requires(value > 0)\n    return value\n\ndef caller() -> None:\n    assert positive(1) == 1\n",
            "nested_closed_precondition.py",
            &[],
        )
        .unwrap();
        assert!(verified.passed, "{verified:#?}");
    }

    #[test]
    fn variadic_tuple_capture_cannot_leak_through_the_sequence_proof_representation() {
        let error = verify_contract_module(
            "from typing import Tuple\n\ndef invalid(*values: int) -> bool:\n    return values == (1, 2)\n",
            "varargs_tuple_identity.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.contracts.varargs-operation-unsupported"
        );
    }
}
