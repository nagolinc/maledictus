//! Source-general well-formedness checks for Nagini contract positions.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_ast::{Ranged, Visitor};
use rustpython_parser::{Parse, ast};

use crate::python_adt_wellformedness::{MALFORMED_ADT, validate_adt_wellformedness};
use crate::python_io_wellformedness::validate_io_wellformedness;
use crate::python_language_wellformedness::validate_language_suite;
use crate::python_predicate_family_wellformedness::validate_predicate_families;
use crate::python_private_fields::{PRIVATE_FIELD_ACCESS, validate_private_field_access};
use crate::python_thread_wellformedness::validate_thread_suite;

pub const INVALID_CONTRACT_POSITION: &str = "invalid.program:invalid.contract.position";
pub const INVALID_CONTRACT_CALL: &str = "invalid.program:invalid.contract.call";
pub const INVALID_RESULT: &str = "invalid.program:invalid.result";
pub const INVALID_RESULT_TYPE: &str = "invalid.program:invalid.result.type";
pub const INCORRECT_DECLARED_TYPE: &str = "invalid.program:incorrect.declared.type";
pub const INVALID_PREDICATE: &str = "invalid.program:invalid.predicate";
pub const NESTED_CLASS_DECLARATION: &str = "invalid.program:nested.class.declaration";
pub const NESTED_FUNCTION_DECLARATION: &str = "invalid.program:nested.function.declaration";
pub const DECORATORS_INCOMPATIBLE: &str = "invalid.program:decorators.incompatible";
pub const OVERRIDING_INLINE_METHOD: &str = "invalid.program:overriding.inline.method";
pub const INVALID_OVERRIDE: &str = "invalid.program:invalid.override";
pub const ABSTRACT_PREDICATE_FOLD: &str = "invalid.program:abstract.predicate.fold";
pub const CONTRACT_IN_INLINE_METHOD: &str = "invalid.program:contract.in.inline.method";
pub const LOCAL_IMPORT: &str = "invalid.program:local.import";
pub const LOCAL_TYPE_ALIAS: &str = "invalid.program:local.type.alias";
pub const PURE_FUNCTION_TYPE_NONE: &str = "invalid.program:function.type.none";
pub const PURE_FUNCTION_THROWS_EXCEPTION: &str = "invalid.program:function.throws.exception";
pub const PURE_FUNCTION_RETURN_MISSING: &str = "invalid.program:function.return.missing";
pub const PURE_FUNCTION_DEAD_CODE: &str = "invalid.program:function.dead.code";
pub const RECURSIVE_STATIC_CALL: &str = "invalid.program:recursive.static.call";
pub const TYPE_ERROR_DEAD_CODE: &str = "type.error:dead.code";
pub const IO_OPERATION_RETURN_TYPE_NOT_BOOL: &str =
    "invalid.program:invalid.io_operation.return_type_not_bool";
pub const IO_OPERATION_VARARG: &str = "invalid.program:invalid.io_operation.vararg";
pub const IO_OPERATION_KWARG: &str = "invalid.program:invalid.io_operation.kwarg";
pub const IO_OPERATION_DEFAULT_ARGUMENT: &str =
    "invalid.program:invalid.io_operation.default_argument";
pub const IO_OPERATION_INVALID_PRESET: &str = "invalid.program:invalid.io_operation.invalid_preset";
pub const IO_OPERATION_INVALID_POSTSET: &str =
    "invalid.program:invalid.io_operation.invalid_postset";
pub const INVALID_FLOAT_VALUE: &str = "invalid.program:invalid.float.val";
pub const FLOAT_CONVERSION_UNSUPPORTED: &str =
    "unsupported:float() is currently only supported with arguments NaN and inf.";
pub const MULTIPLE_INHERITANCE_UNSUPPORTED: &str = "unsupported:multiple inheritance";
pub const METACLASS_UNSUPPORTED: &str = "unsupported:Unsupported metaclass";
pub const LARGE_TUPLE_UNSUPPORTED: &str = "unsupported:Tuples longer than 9 elements are currently unsupported. Please file an issue to resolve this.";
pub const ILLEGAL_MAGIC_METHOD: &str = "invalid.program:illegal.magic.method";
pub const WILDCARD_VARIABLE_READ: &str = "invalid.program:wildcard.variable.read";
pub const INLINE_CONSTRUCTOR_UNSUPPORTED: &str =
    "unsupported:Inlining constructors is currently not supported.";
pub const PURE_MULTI_ASSIGN_UNSUPPORTED: &str =
    "unsupported:Multi-target assignments are not supported in pure functions.";
pub const BUILTIN_SUBCLASS_UNSUPPORTED: &str =
    "unsupported:Subclassing builtin type is currently not supported.";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractPositionFailure {
    pub code: &'static str,
    pub message: String,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

/// Selects the source-language verification rules that are active for one Python module.
///
/// Production requests retain the ordinary profile unless their caller explicitly opts into
/// information-flow verification.  The pinned conformance harness supplies this value from its
/// suite metadata; source text and fixture filenames never select a profile.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum InformationFlowVerificationProfile {
    #[default]
    Ordinary,
    /// Sequential secure-information-flow semantics. Concurrency primitives are rejected because
    /// this profile does not assign them a relational meaning.
    SecureInformationFlow,
    /// Possibilistic secure-information-flow semantics, where source-bound locks and threads are
    /// part of the verified language rather than an invalid-program condition.
    PossibilisticSecureInformationFlow,
    /// Probabilistic secure-information-flow semantics, which likewise assigns concurrency a
    /// relational meaning instead of rejecting it during sequential-SIF preflight.
    ProbabilisticSecureInformationFlow,
}

impl InformationFlowVerificationProfile {
    pub(crate) fn is_secure(self) -> bool {
        matches!(
            self,
            Self::SecureInformationFlow
                | Self::PossibilisticSecureInformationFlow
                | Self::ProbabilisticSecureInformationFlow
        )
    }

    pub(crate) fn forbids_concurrency(self) -> bool {
        self == Self::SecureInformationFlow
    }
}

/// Predicates exported by one source-owned module after that module's heap semantics have been
/// verified.  Contract-position validation consumes this sealed catalog rather than trusting the
/// spelling of an import in the consumer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SourcePredicateModule {
    module: String,
    predicates: BTreeSet<String>,
}

impl SourcePredicateModule {
    pub(crate) fn new(module: impl Into<String>, predicates: BTreeSet<String>) -> Self {
        Self {
            module: module.into(),
            predicates,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExpressionContext {
    Runtime,
    Precondition { pure: bool },
    Postcondition { pure: bool },
    LoopInvariant,
    UnfoldingValue,
}

#[derive(Clone, Default)]
struct Bindings {
    canonical: BTreeMap<String, String>,
    predicates: BTreeSet<String>,
    pure_functions: BTreeSet<String>,
    declared_functions: BTreeSet<String>,
    io_operations: BTreeSet<String>,
    typing_types: BTreeMap<String, String>,
    adt_markers: BTreeSet<String>,
    adt_roots: BTreeSet<String>,
    classes: BTreeMap<String, ClassDeclaration>,
    /// Class value bindings that still denote their source declarations at this program point.
    /// The declaration catalog remains available for already-resolved annotations even when a
    /// function-local value shadows the class spelling.
    active_class_values: BTreeSet<String>,
    module_predicates: BTreeMap<String, PredicateKind>,
    nominal_values: BTreeMap<String, NominalProvenance>,
    /// Active module bindings for native Python types whose runtime behavior cannot be inherited
    /// by Nagini's source model. Unlike function globals, class bases are evaluated in module
    /// order, so this catalog is deliberately updated as each module statement executes.
    nonextendable_builtin_types: BTreeMap<String, String>,
    allow_abstract_predicate_operations: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PredicateKind {
    Concrete,
    Abstract,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum NominalProvenance {
    /// Every reachable value was produced with one of these exact source runtime classes.
    Exact(BTreeSet<String>),
    /// A static annotation bounds the value, but runtime subclasses remain possible.
    UpperBound(BTreeSet<String>),
    /// No source-closed nominal fact is justified.
    Unknown,
}

impl NominalProvenance {
    fn classes(&self) -> Option<&BTreeSet<String>> {
        match self {
            Self::Exact(classes) | Self::UpperBound(classes) => Some(classes),
            Self::Unknown => None,
        }
    }

    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Exact(mut left), Self::Exact(right)) => {
                left.extend(right);
                Self::Exact(left)
            }
            (Self::Exact(mut left), Self::UpperBound(right))
            | (Self::UpperBound(mut left), Self::Exact(right))
            | (Self::UpperBound(mut left), Self::UpperBound(right)) => {
                left.extend(right);
                Self::UpperBound(left)
            }
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
        }
    }
}

#[derive(Clone, Default)]
struct ClassDeclaration {
    bases: BTreeSet<String>,
    methods: BTreeMap<String, MethodDeclaration>,
    zero_argument_factories: BTreeSet<String>,
    dynamic_class_factories: BTreeSet<String>,
    predicate_methods: BTreeMap<String, PredicateKind>,
}

#[derive(Clone, Default)]
struct MethodDeclaration {
    inline: bool,
    pure: bool,
    keyword_parameters: Vec<String>,
    parameter_has_default: Vec<bool>,
    exceptional_types: BTreeSet<String>,
}

pub fn validate_contract_positions(
    source: &str,
    path: &str,
) -> Result<(), ContractPositionFailure> {
    validate_contract_positions_with_profile(
        source,
        path,
        InformationFlowVerificationProfile::Ordinary,
    )
}

pub fn validate_contract_positions_with_profile(
    source: &str,
    path: &str,
    information_flow: InformationFlowVerificationProfile,
) -> Result<(), ContractPositionFailure> {
    validate_contract_positions_with_source_predicates_and_profile(
        source,
        path,
        &[],
        information_flow,
    )
}

pub(crate) fn validate_contract_positions_with_source_predicates(
    source: &str,
    path: &str,
    imported_predicates: &[SourcePredicateModule],
) -> Result<(), ContractPositionFailure> {
    validate_contract_positions_with_source_predicates_and_profile(
        source,
        path,
        imported_predicates,
        InformationFlowVerificationProfile::Ordinary,
    )
}

fn validate_contract_positions_with_source_predicates_and_profile(
    source: &str,
    path: &str,
    imported_predicates: &[SourcePredicateModule],
    information_flow: InformationFlowVerificationProfile,
) -> Result<(), ContractPositionFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractPositionFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
        byte_offset: 0,
        line: 1,
        column: 1,
    })?;
    if let Err(failure) = validate_language_suite(&suite, source) {
        return Err(ContractPositionFailure {
            code: failure.code,
            message: failure.message,
            byte_offset: failure.byte_offset,
            line: failure.line,
            column: failure.column,
        });
    }
    if let Err(failure) = validate_thread_suite(&suite, source, information_flow) {
        return Err(ContractPositionFailure {
            code: failure.code,
            message: failure.message,
            byte_offset: failure.byte_offset,
            line: failure.line,
            column: failure.column,
        });
    }
    if let Err(failure) = validate_adt_wellformedness(source, path) {
        return Err(ContractPositionFailure {
            code: MALFORMED_ADT,
            message: failure.message,
            byte_offset: failure.byte_offset,
            line: failure.line,
            column: failure.column,
        });
    }
    if let Err(failure) = validate_predicate_families(&suite, source) {
        return Err(ContractPositionFailure {
            code: failure.code,
            message: failure.message,
            byte_offset: failure.byte_offset,
            line: failure.line,
            column: failure.column,
        });
    }
    let ambiguous_module_bindings = module_rebound_names(&suite);
    let final_function_bindings = collect_final_module_function_bindings(
        &suite,
        &ambiguous_module_bindings,
        imported_predicates,
    );
    let mut bindings = Bindings::default();
    for builtin in nonextendable_builtin_types() {
        bindings
            .nonextendable_builtin_types
            .insert((*builtin).to_owned(), (*builtin).to_owned());
    }
    if !ambiguous_module_bindings.contains("classmethod") {
        bindings
            .canonical
            .insert("classmethod".to_owned(), "classmethod".to_owned());
    }
    if !ambiguous_module_bindings.contains("staticmethod") {
        bindings
            .canonical
            .insert("staticmethod".to_owned(), "staticmethod".to_owned());
    }
    if !ambiguous_module_bindings.contains("bool") {
        bindings
            .canonical
            .insert("bool".to_owned(), "bool".to_owned());
    }
    if !ambiguous_module_bindings.contains("float") {
        bindings
            .canonical
            .insert("float".to_owned(), "float".to_owned());
    }
    for statement in &suite {
        if let ast::Stmt::ImportFrom(import) = statement
            && (bind_contract_import(import, &ambiguous_module_bindings, &mut bindings)
                || bind_typing_import(import, &ambiguous_module_bindings, &mut bindings)
                || bind_abc_import(import, &ambiguous_module_bindings, &mut bindings)
                || bind_adt_import(import, &ambiguous_module_bindings, &mut bindings)
                || bind_source_predicate_import(
                    import,
                    imported_predicates,
                    &ambiguous_module_bindings,
                    &mut bindings,
                ))
        {
            continue;
        }
        match statement {
            ast::Stmt::FunctionDef(function) => {
                // The function value is installed before its body can execute, so a same-named
                // source class is no longer a callable class value in the body. Keep the class
                // declaration temporarily for annotations evaluated while defining the function.
                bindings.active_class_values.remove(function.name.as_str());
                collect_function_declaration(function, &mut bindings);
                collect_module_predicate_declaration(function, &mut bindings);
                let runtime_bindings =
                    bindings_with_final_function_catalog(&bindings, &final_function_bindings);
                validate_function(function, &runtime_bindings, None, source)?;
                bindings.classes.remove(function.name.as_str());
                bindings.canonical.remove(function.name.as_str());
                bindings
                    .nonextendable_builtin_types
                    .remove(function.name.as_str());
            }
            ast::Stmt::ClassDef(class) => {
                for item in &class.body {
                    if let ast::Stmt::FunctionDef(function) = item {
                        collect_function_declaration(function, &mut bindings);
                    }
                }
                validate_nonextendable_builtin_subclass(class, &bindings, source)?;
                validate_module_statement(statement, &bindings, &final_function_bindings, source)?;
                let defines_adt_root = matches!(class.bases.as_slice(), [ast::Expr::Name(base)]
                    if bindings.adt_markers.contains(base.id.as_str()));
                let declaration = collect_class_declaration(class, &bindings);
                bindings.classes.insert(class.name.to_string(), declaration);
                bindings.active_class_values.insert(class.name.to_string());
                if defines_adt_root {
                    bindings.adt_roots.insert(class.name.to_string());
                }
                bindings.canonical.remove(class.name.as_str());
                bindings
                    .nonextendable_builtin_types
                    .remove(class.name.as_str());
            }
            ast::Stmt::Assign(assignment) => {
                validate_expression(
                    &assignment.value,
                    &bindings,
                    ExpressionContext::Runtime,
                    source,
                )?;
                for target in &assignment.targets {
                    remove_target_binding(target, &mut bindings);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                if let Some(value) = assignment.value.as_deref() {
                    validate_expression(value, &bindings, ExpressionContext::Runtime, source)?;
                }
                remove_target_binding(&assignment.target, &mut bindings);
            }
            ast::Stmt::Import(import) => {
                validate_module_statement(statement, &bindings, &Bindings::default(), source)?;
                for alias in &import.names {
                    let local = alias.asname.as_ref().map_or_else(
                        || alias.name.split('.').next().unwrap_or_default(),
                        |name| name.as_str(),
                    );
                    remove_name_binding(local, &mut bindings);
                }
            }
            ast::Stmt::ImportFrom(import) => {
                validate_module_statement(statement, &bindings, &Bindings::default(), source)?;
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        // A wildcard import may replace any builtin binding. Keeping a native
                        // identity here would turn an unknown external base into a false source
                        // rejection, so later class bases must be handled by semantic analysis.
                        bindings.nonextendable_builtin_types.clear();
                    } else {
                        let local = alias.asname.as_ref().unwrap_or(&alias.name);
                        remove_name_binding(local.as_str(), &mut bindings);
                    }
                }
            }
            _ => validate_module_statement(statement, &bindings, &Bindings::default(), source)?,
        }
    }
    // IO operation declarations must be closed and well typed before any use is allowed to trust
    // their output catalog. This also preserves Nagini's declaration-before-use diagnostics.
    if let Err(failure) = validate_io_wellformedness(source, path) {
        return Err(ContractPositionFailure {
            code: failure.code,
            message: failure.message,
            byte_offset: failure.byte_offset,
            line: failure.line,
            column: failure.column,
        });
    }
    if let Err(failure) = validate_private_field_access(&suite, source) {
        return Err(ContractPositionFailure {
            code: PRIVATE_FIELD_ACCESS,
            message: failure.message,
            byte_offset: failure.byte_offset,
            line: failure.line,
            column: failure.column,
        });
    }
    // Resolve static-call cycles only after the existing source-language, contract-position,
    // thread, ADT, and IO declaration checks. This preserves the earlier located diagnostic when
    // one source contains more than one independent invalid construct.
    validate_recursive_static_calls(&suite, source)?;
    Ok(())
}

#[derive(Clone)]
struct StaticCallEdge {
    source: (String, String),
    target: (String, String),
    call: ast::ExprCall,
}

/// Reject a cycle made entirely of class-qualified calls to source methods.
///
/// Nagini statically binds and inlines calls such as `Class.method(receiver)`.  A cycle in those
/// calls cannot be translated as an ordinary dynamic recursion, and the first source call that
/// enters the cycle is an invalid program.  This pass resolves only final, unambiguous module and
/// class-body bindings.  Rebound names remain for the semantic frontend instead of being guessed.
fn validate_recursive_static_calls(
    suite: &[ast::Stmt],
    source: &str,
) -> Result<(), ContractPositionFailure> {
    let mut final_classes: BTreeMap<String, Option<&ast::StmtClassDef>> = BTreeMap::new();
    for statement in suite {
        match statement {
            ast::Stmt::ClassDef(class) => {
                final_classes.insert(class.name.to_string(), Some(class));
            }
            ast::Stmt::FunctionDef(function) => {
                final_classes.insert(function.name.to_string(), None);
            }
            ast::Stmt::Assign(assignment) => {
                let mut names = BTreeSet::new();
                for target in &assignment.targets {
                    collect_target_names(target, &mut names);
                }
                for name in names {
                    final_classes.insert(name, None);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                let mut names = BTreeSet::new();
                collect_target_names(&assignment.target, &mut names);
                for name in names {
                    final_classes.insert(name, None);
                }
            }
            ast::Stmt::Import(import) => {
                for alias in &import.names {
                    let local = alias.asname.as_ref().map_or_else(
                        || alias.name.split('.').next().unwrap_or_default(),
                        |name| name.as_str(),
                    );
                    final_classes.insert(local.to_owned(), None);
                }
            }
            ast::Stmt::ImportFrom(import) => {
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        // A wildcard import replaces only bindings that precede it. A later class
                        // declaration establishes a new exact module binding.
                        for class in final_classes.values_mut() {
                            *class = None;
                        }
                    } else {
                        let local = alias.asname.as_ref().unwrap_or(&alias.name);
                        final_classes.insert(local.to_string(), None);
                    }
                }
            }
            _ => {}
        }
    }

    let classes = final_classes
        .into_iter()
        .filter_map(|(name, class)| class.map(|class| (name, class)))
        .collect::<BTreeMap<_, _>>();
    if classes.is_empty() {
        return Ok(());
    }

    let mut methods: BTreeMap<String, BTreeMap<String, &ast::StmtFunctionDef>> = BTreeMap::new();
    for (class_name, class) in &classes {
        let mut final_methods: BTreeMap<String, Option<&ast::StmtFunctionDef>> = BTreeMap::new();
        for statement in &class.body {
            match statement {
                ast::Stmt::FunctionDef(function) => {
                    final_methods.insert(function.name.to_string(), Some(function));
                }
                ast::Stmt::Assign(assignment) => {
                    let mut names = BTreeSet::new();
                    for target in &assignment.targets {
                        collect_target_names(target, &mut names);
                    }
                    for name in names {
                        final_methods.insert(name, None);
                    }
                }
                ast::Stmt::AnnAssign(assignment) => {
                    let mut names = BTreeSet::new();
                    collect_target_names(&assignment.target, &mut names);
                    for name in names {
                        final_methods.insert(name, None);
                    }
                }
                _ => {}
            }
        }
        methods.insert(
            class_name.clone(),
            final_methods
                .into_iter()
                .filter_map(|(name, method)| method.map(|method| (name, method)))
                .collect(),
        );
    }

    let mut edges = Vec::new();
    for (class_name, class_methods) in &methods {
        for (method_name, function) in class_methods {
            let mut local_names = BTreeSet::new();
            collect_argument_names(&function.args, &mut local_names);
            let mut local_collector = FunctionLocalNameCollector {
                names: &mut local_names,
            };
            for statement in &function.body {
                local_collector.visit_stmt(statement.clone());
            }
            let mut collector = StaticCallCollector {
                source: (class_name.clone(), method_name.clone()),
                methods: &methods,
                local_names: &local_names,
                edges: &mut edges,
            };
            for statement in &function.body {
                collector.visit_stmt(statement.clone());
            }
        }
    }

    let components = static_call_components(&edges);
    edges.sort_by_key(|edge| u32::from(edge.call.range.start()));
    for edge in edges {
        if components.get(&edge.source) == components.get(&edge.target) {
            return invalid_code(
                &edge.call,
                source,
                RECURSIVE_STATIC_CALL,
                format!(
                    "class-qualified call {}.{} enters a recursive static-call cycle",
                    edge.target.0, edge.target.1
                ),
            );
        }
    }
    Ok(())
}

/// Compute strongly connected components with iterative Kosaraju passes. Keeping traversal
/// explicit avoids both call-stack growth and repeated per-edge reachability searches on large
/// source modules.
fn static_call_components(edges: &[StaticCallEdge]) -> BTreeMap<(String, String), usize> {
    let mut nodes = BTreeSet::new();
    let mut forward: BTreeMap<(String, String), Vec<(String, String)>> = BTreeMap::new();
    let mut reverse: BTreeMap<(String, String), Vec<(String, String)>> = BTreeMap::new();
    for edge in edges {
        nodes.insert(edge.source.clone());
        nodes.insert(edge.target.clone());
        forward
            .entry(edge.source.clone())
            .or_default()
            .push(edge.target.clone());
        reverse
            .entry(edge.target.clone())
            .or_default()
            .push(edge.source.clone());
    }

    let mut seen = BTreeSet::new();
    let mut finished = Vec::with_capacity(nodes.len());
    for root in &nodes {
        if seen.contains(root) {
            continue;
        }
        let mut stack = vec![(root.clone(), false)];
        while let Some((node, expanded)) = stack.pop() {
            if expanded {
                finished.push(node);
                continue;
            }
            if !seen.insert(node.clone()) {
                continue;
            }
            stack.push((node.clone(), true));
            if let Some(next) = forward.get(&node) {
                for neighbor in next.iter().rev() {
                    if !seen.contains(neighbor) {
                        stack.push((neighbor.clone(), false));
                    }
                }
            }
        }
    }

    let mut components = BTreeMap::new();
    let mut component = 0_usize;
    while let Some(root) = finished.pop() {
        if components.contains_key(&root) {
            continue;
        }
        let mut stack = vec![root];
        while let Some(node) = stack.pop() {
            if components.insert(node.clone(), component).is_some() {
                continue;
            }
            if let Some(next) = reverse.get(&node) {
                for neighbor in next {
                    if !components.contains_key(neighbor) {
                        stack.push(neighbor.clone());
                    }
                }
            }
        }
        component += 1;
    }
    components
}

fn collect_argument_names(arguments: &ast::Arguments, names: &mut BTreeSet<String>) {
    for argument in arguments
        .posonlyargs
        .iter()
        .chain(&arguments.args)
        .chain(&arguments.kwonlyargs)
    {
        names.insert(argument.def.arg.to_string());
    }
    if let Some(argument) = &arguments.vararg {
        names.insert(argument.arg.to_string());
    }
    if let Some(argument) = &arguments.kwarg {
        names.insert(argument.arg.to_string());
    }
}

struct FunctionLocalNameCollector<'a> {
    names: &'a mut BTreeSet<String>,
}

impl Visitor for FunctionLocalNameCollector<'_> {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if matches!(node.ctx, ast::ExprContext::Store | ast::ExprContext::Del) {
            self.names.insert(node.id.to_string());
        }
    }

    fn visit_stmt_function_def(&mut self, node: ast::StmtFunctionDef) {
        self.names.insert(node.name.to_string());
        // A nested function has its own lexical scope; do not attribute its body bindings to the
        // enclosing method. The language well-formedness pass independently rejects it where
        // Nagini does not permit nested declarations.
    }

    fn visit_stmt_class_def(&mut self, node: ast::StmtClassDef) {
        self.names.insert(node.name.to_string());
    }
}

struct StaticCallCollector<'a> {
    source: (String, String),
    methods: &'a BTreeMap<String, BTreeMap<String, &'a ast::StmtFunctionDef>>,
    local_names: &'a BTreeSet<String>,
    edges: &'a mut Vec<StaticCallEdge>,
}

impl Visitor for StaticCallCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if let ast::Expr::Attribute(attribute) = node.func.as_ref()
            && let ast::Expr::Name(receiver) = attribute.value.as_ref()
            && !self.local_names.contains(receiver.id.as_str())
            && self
                .methods
                .get(receiver.id.as_str())
                .is_some_and(|class| class.contains_key(attribute.attr.as_str()))
        {
            self.edges.push(StaticCallEdge {
                source: self.source.clone(),
                target: (receiver.id.to_string(), attribute.attr.to_string()),
                call: node.clone(),
            });
        }
        self.generic_visit_expr_call(node);
    }

    fn visit_stmt_function_def(&mut self, _node: ast::StmtFunctionDef) {}

    fn visit_stmt_class_def(&mut self, _node: ast::StmtClassDef) {}
}

fn collect_final_module_function_bindings(
    suite: &[ast::Stmt],
    ambiguous: &BTreeSet<String>,
    imported_predicates: &[SourcePredicateModule],
) -> Bindings {
    let mut bindings = Bindings::default();
    for statement in suite {
        match statement {
            ast::Stmt::ImportFrom(import)
                if bind_contract_import(import, ambiguous, &mut bindings)
                    || bind_typing_import(import, ambiguous, &mut bindings)
                    || bind_abc_import(import, ambiguous, &mut bindings)
                    || bind_adt_import(import, ambiguous, &mut bindings)
                    || bind_source_predicate_import(
                        import,
                        imported_predicates,
                        ambiguous,
                        &mut bindings,
                    ) => {}
            ast::Stmt::Import(import) => {
                for alias in &import.names {
                    let local = alias.asname.as_ref().map_or_else(
                        || alias.name.split('.').next().unwrap_or_default(),
                        |name| name.as_str(),
                    );
                    remove_name_binding(local, &mut bindings);
                }
            }
            ast::Stmt::ImportFrom(import) => {
                for alias in &import.names {
                    if alias.name.as_str() != "*" {
                        let local = alias.asname.as_ref().unwrap_or(&alias.name);
                        remove_name_binding(local.as_str(), &mut bindings);
                    }
                }
            }
            ast::Stmt::FunctionDef(function) => {
                collect_function_declaration(function, &mut bindings);
                collect_module_predicate_declaration(function, &mut bindings);
                bindings.canonical.remove(function.name.as_str());
            }
            ast::Stmt::ClassDef(class) => {
                remove_name_binding(class.name.as_str(), &mut bindings);
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    remove_target_binding(target, &mut bindings);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                remove_target_binding(&assignment.target, &mut bindings);
            }
            _ => {}
        }
    }
    bindings
}

fn bindings_with_final_function_catalog(current: &Bindings, final_bindings: &Bindings) -> Bindings {
    let mut bindings = current.clone();
    bindings
        .predicates
        .extend(final_bindings.predicates.iter().cloned());
    bindings
        .pure_functions
        .extend(final_bindings.pure_functions.iter().cloned());
    bindings
        .declared_functions
        .extend(final_bindings.declared_functions.iter().cloned());
    bindings
        .io_operations
        .extend(final_bindings.io_operations.iter().cloned());
    bindings
        .module_predicates
        .extend(final_bindings.module_predicates.clone());
    bindings
}

fn module_rebound_names(suite: &[ast::Stmt]) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                names.insert(function.name.to_string());
            }
            ast::Stmt::ClassDef(class) => {
                names.insert(class.name.to_string());
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    collect_target_names(target, &mut names);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                collect_target_names(&assignment.target, &mut names);
            }
            _ => {}
        }
    }
    names
}

fn collect_target_names(target: &ast::Expr, names: &mut BTreeSet<String>) {
    match target {
        ast::Expr::Name(name) => {
            names.insert(name.id.to_string());
        }
        ast::Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                collect_target_names(element, names);
            }
        }
        _ => {}
    }
}

fn bind_contract_import(
    import: &ast::StmtImportFrom,
    ambiguous: &BTreeSet<String>,
    bindings: &mut Bindings,
) -> bool {
    if !import.level.is_none_or(|level| level == 0_u32)
        || !import.module.as_ref().is_some_and(|module| {
            matches!(
                module.as_str(),
                "nagini_contracts.contracts"
                    | "nagini_contracts.obligations"
                    | "nagini_contracts.io_contracts"
            )
        })
    {
        return false;
    }
    for alias in &import.names {
        if alias.name.as_str() == "*" {
            for primitive in known_primitives() {
                if !ambiguous.contains(*primitive) {
                    bindings
                        .canonical
                        .insert((*primitive).to_owned(), (*primitive).to_owned());
                }
            }
        } else {
            let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
            if !ambiguous.contains(&local) {
                bindings.canonical.insert(local, alias.name.to_string());
            }
        }
    }
    true
}

fn bind_typing_import(
    import: &ast::StmtImportFrom,
    ambiguous: &BTreeSet<String>,
    bindings: &mut Bindings,
) -> bool {
    if !import.level.is_none_or(|level| level == 0_u32)
        || import.module.as_ref().map(|module| module.as_str()) != Some("typing")
    {
        return false;
    }
    for alias in &import.names {
        if alias.name.as_str() == "*" {
            for constructor in typing_alias_constructors() {
                if !ambiguous.contains(*constructor) {
                    bindings
                        .typing_types
                        .insert((*constructor).to_owned(), (*constructor).to_owned());
                }
            }
        } else if typing_alias_constructors().contains(&alias.name.as_str()) {
            let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
            if !ambiguous.contains(&local) {
                bindings.typing_types.insert(local, alias.name.to_string());
            }
        }
    }
    true
}

fn bind_abc_import(
    import: &ast::StmtImportFrom,
    ambiguous: &BTreeSet<String>,
    bindings: &mut Bindings,
) -> bool {
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
    if !is_canonical_abc_import_binding(
        import.level.is_none_or(|level| level == 0_u32),
        import.module.as_ref().map_or("", |module| module.as_str()),
        &imported_names,
    ) {
        return false;
    }
    for alias in &import.names {
        if alias.name.as_str() == "ABCMeta" {
            let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
            if !ambiguous.contains(&local) {
                bindings.canonical.insert(local, "ABCMeta".to_owned());
            }
        }
    }
    true
}

pub(crate) fn is_canonical_abc_import_binding(
    absolute: bool,
    module: &str,
    imported_names: &[(String, Option<String>)],
) -> bool {
    if !absolute || module != "abc" || imported_names.is_empty() {
        return false;
    }
    let mut seen = BTreeSet::new();
    imported_names.iter().all(|(name, alias)| {
        alias.is_none()
            && matches!(name.as_str(), "ABC" | "ABCMeta" | "abstractmethod")
            && seen.insert(name.as_str())
    })
}

fn bind_adt_import(
    import: &ast::StmtImportFrom,
    ambiguous: &BTreeSet<String>,
    bindings: &mut Bindings,
) -> bool {
    if !import.level.is_none_or(|level| level == 0_u32)
        || import.module.as_ref().map(|module| module.as_str()) != Some("nagini_contracts.adt")
    {
        return false;
    }
    for alias in &import.names {
        if alias.name.as_str() == "ADT" {
            let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
            if !ambiguous.contains(&local) {
                bindings.adt_markers.insert(local);
            }
        }
    }
    true
}

fn bind_source_predicate_import(
    import: &ast::StmtImportFrom,
    imported_modules: &[SourcePredicateModule],
    ambiguous: &BTreeSet<String>,
    bindings: &mut Bindings,
) -> bool {
    if !import.level.is_none_or(|level| level == 0_u32) {
        return false;
    }
    let Some(module_name) = import.module.as_ref() else {
        return false;
    };
    let Some(module) = imported_modules
        .iter()
        .find(|module| module.module == module_name.as_str())
    else {
        return false;
    };

    for alias in &import.names {
        if alias.name.as_str() == "*" {
            continue;
        }
        let local_name = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
        // The import executes a real Python binding for every named symbol, not just predicates.
        // Clear any earlier exact identity before selectively installing the source-verified one.
        remove_name_binding(&local_name, bindings);
        if module.predicates.contains(alias.name.as_str()) && !ambiguous.contains(&local_name) {
            bindings
                .module_predicates
                .insert(local_name, PredicateKind::Concrete);
        }
    }
    true
}

fn typing_alias_constructors() -> &'static [&'static str] {
    &[
        "Callable",
        "Dict",
        "FrozenSet",
        "Generic",
        "List",
        "NamedTuple",
        "Optional",
        "Set",
        "Sized",
        "Tuple",
        "Type",
        "Union",
    ]
}

fn nonextendable_builtin_types() -> &'static [&'static str] {
    &[
        "bool",
        "bytearray",
        "bytes",
        "dict",
        "float",
        "frozenset",
        "list",
        "range",
        "set",
        "str",
        "tuple",
    ]
}

fn known_primitives() -> &'static [&'static str] {
    &[
        "Acc",
        "Assert",
        "ContractOnly",
        "Decreases",
        "Ensures",
        "Exsures",
        "Fold",
        "IOExists",
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
        "IOOperation",
        "Inline",
        "Implies",
        "Invariant",
        "LowEvent",
        "LowExit",
        "MustTerminate",
        "Opaque",
        "Place",
        "Predicate",
        "Pure",
        "Rd",
        "Requires",
        "Result",
        "ResultT",
        "TerminationMeasure",
        "Terminates",
        "Unfold",
        "Unfolding",
        "list_pred",
        "token",
    ]
}

fn collect_function_declaration(function: &ast::StmtFunctionDef, bindings: &mut Bindings) {
    bindings.predicates.remove(function.name.as_str());
    bindings.pure_functions.remove(function.name.as_str());
    bindings.io_operations.remove(function.name.as_str());
    bindings
        .declared_functions
        .insert(function.name.to_string());
    if has_decorator(&function.decorator_list, bindings, "Predicate") {
        bindings.predicates.insert(function.name.to_string());
    }
    if has_decorator(&function.decorator_list, bindings, "Pure") {
        bindings.pure_functions.insert(function.name.to_string());
    }
    if has_decorator(&function.decorator_list, bindings, "IOOperation") {
        bindings.io_operations.insert(function.name.to_string());
    }
}

fn collect_module_predicate_declaration(function: &ast::StmtFunctionDef, bindings: &mut Bindings) {
    bindings.module_predicates.remove(function.name.as_str());
    if has_decorator(&function.decorator_list, bindings, "Predicate") {
        let kind = if has_decorator(&function.decorator_list, bindings, "ContractOnly") {
            PredicateKind::Abstract
        } else {
            PredicateKind::Concrete
        };
        bindings
            .module_predicates
            .insert(function.name.to_string(), kind);
    }
}

fn remove_target_binding(target: &ast::Expr, bindings: &mut Bindings) {
    match target {
        ast::Expr::Name(name) => {
            remove_name_binding(name.id.as_str(), bindings);
        }
        ast::Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                remove_target_binding(element, bindings);
            }
        }
        _ => {}
    }
}

fn remove_name_binding(name: &str, bindings: &mut Bindings) {
    bindings.canonical.remove(name);
    bindings.predicates.remove(name);
    bindings.pure_functions.remove(name);
    bindings.declared_functions.remove(name);
    bindings.io_operations.remove(name);
    bindings.typing_types.remove(name);
    bindings.adt_markers.remove(name);
    bindings.adt_roots.remove(name);
    bindings.classes.remove(name);
    bindings.active_class_values.remove(name);
    bindings.module_predicates.remove(name);
    bindings.nominal_values.remove(name);
    bindings.nonextendable_builtin_types.remove(name);
}

fn validate_nonextendable_builtin_subclass(
    class: &ast::StmtClassDef,
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    let Some(base) = class.bases.first() else {
        return Ok(());
    };
    let local_name = match base {
        ast::Expr::Name(name) => Some(name.id.as_str()),
        ast::Expr::Subscript(subscript) => match subscript.value.as_ref() {
            ast::Expr::Name(name) => Some(name.id.as_str()),
            _ => None,
        },
        _ => None,
    };
    let Some(local_name) = local_name else {
        return Ok(());
    };
    let canonical = bindings
        .nonextendable_builtin_types
        .get(local_name)
        .map(String::as_str)
        .or_else(|| {
            bindings
                .typing_types
                .get(local_name)
                .and_then(|typing_name| match typing_name.as_str() {
                    "Dict" => Some("dict"),
                    "FrozenSet" => Some("frozenset"),
                    "List" => Some("list"),
                    "Set" => Some("set"),
                    "Tuple" => Some("tuple"),
                    _ => None,
                })
        });
    if let Some(canonical) = canonical {
        return invalid_code(
            class,
            source,
            BUILTIN_SUBCLASS_UNSUPPORTED,
            format!(
                "class {:?} subclasses nonextendable builtin type {canonical:?}",
                class.name
            ),
        );
    }
    Ok(())
}

fn has_decorator(decorators: &[ast::Expr], bindings: &Bindings, canonical: &str) -> bool {
    canonical_decorator(decorators, bindings, canonical).is_some()
}

fn canonical_decorator<'a>(
    decorators: &'a [ast::Expr],
    bindings: &Bindings,
    canonical: &str,
) -> Option<&'a ast::Expr> {
    decorators.iter().find(|decorator| {
        matches!(decorator, ast::Expr::Name(name)
            if canonical_name(bindings, name.id.as_str()) == Some(canonical))
    })
}

fn collect_class_declaration(class: &ast::StmtClassDef, bindings: &Bindings) -> ClassDeclaration {
    let mut declaration = ClassDeclaration::default();
    for base in &class.bases {
        let ast::Expr::Name(base) = base else {
            continue;
        };
        declaration.bases.insert(base.id.to_string());
        if let Some(inherited) = bindings.classes.get(base.id.as_str()) {
            declaration.methods.extend(inherited.methods.clone());
            declaration
                .zero_argument_factories
                .extend(inherited.zero_argument_factories.clone());
            declaration
                .dynamic_class_factories
                .extend(inherited.dynamic_class_factories.clone());
            declaration
                .predicate_methods
                .extend(inherited.predicate_methods.clone());
        }
    }
    let mut class_bindings = bindings.clone();
    for statement in &class.body {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                declaration
                    .dynamic_class_factories
                    .remove(function.name.as_str());
                if is_verified_dynamic_class_factory(function, &class_bindings) {
                    declaration
                        .dynamic_class_factories
                        .insert(function.name.to_string());
                }
                declaration.predicate_methods.remove(function.name.as_str());
                if has_decorator(&function.decorator_list, &class_bindings, "Predicate") {
                    let kind =
                        if has_decorator(&function.decorator_list, &class_bindings, "ContractOnly")
                        {
                            PredicateKind::Abstract
                        } else {
                            PredicateKind::Concrete
                        };
                    declaration
                        .predicate_methods
                        .insert(function.name.to_string(), kind);
                }
                declaration
                    .zero_argument_factories
                    .remove(function.name.as_str());
                if is_zero_argument_class_factory(function, &class_bindings) {
                    declaration
                        .zero_argument_factories
                        .insert(function.name.to_string());
                }
                declaration.methods.insert(
                    function.name.to_string(),
                    collect_method_declaration(function, &class_bindings),
                );
                class_bindings.canonical.remove(function.name.as_str());
                class_bindings.typing_types.remove(function.name.as_str());
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    remove_predicate_method_target_bindings(
                        target,
                        &mut declaration.predicate_methods,
                    );
                    remove_factory_target_bindings(
                        target,
                        &mut declaration.zero_argument_factories,
                    );
                    remove_factory_target_bindings(
                        target,
                        &mut declaration.dynamic_class_factories,
                    );
                    remove_target_binding(target, &mut class_bindings);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                remove_predicate_method_target_bindings(
                    &assignment.target,
                    &mut declaration.predicate_methods,
                );
                remove_factory_target_bindings(
                    &assignment.target,
                    &mut declaration.zero_argument_factories,
                );
                remove_factory_target_bindings(
                    &assignment.target,
                    &mut declaration.dynamic_class_factories,
                );
                remove_target_binding(&assignment.target, &mut class_bindings);
            }
            _ => {}
        }
    }
    declaration
}

fn is_zero_argument_class_factory(function: &ast::StmtFunctionDef, bindings: &Bindings) -> bool {
    if !has_decorator(&function.decorator_list, bindings, "classmethod")
        || !method_accepts_zero_explicit_arguments(function)
    {
        return false;
    }
    let Some(receiver) = function
        .args
        .posonlyargs
        .first()
        .or_else(|| function.args.args.first())
        .map(|argument| argument.def.arg.as_str())
    else {
        return false;
    };
    let Some(ast::Stmt::Return(return_statement)) = function.body.last() else {
        return false;
    };
    let Some(ast::Expr::Call(call)) = return_statement.value.as_deref() else {
        return false;
    };
    call.args.is_empty()
        && call.keywords.is_empty()
        && matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == receiver)
}

fn is_verified_dynamic_class_factory(function: &ast::StmtFunctionDef, bindings: &Bindings) -> bool {
    if !has_decorator(&function.decorator_list, bindings, "classmethod") {
        return false;
    }
    let Some(receiver) = function
        .args
        .posonlyargs
        .first()
        .or_else(|| function.args.args.first())
        .map(|argument| argument.def.arg.as_str())
    else {
        return false;
    };
    if function.body.iter().any(|statement| {
        matches!(statement, ast::Stmt::Return(returned)
            if matches!(returned.value.as_deref(), Some(ast::Expr::Call(call))
                if matches!(call.func.as_ref(), ast::Expr::Name(name)
                    if name.id.as_str() == receiver)))
    }) {
        return true;
    }
    let constructed = function
        .body
        .iter()
        .filter_map(|statement| {
            let ast::Stmt::Assign(assignment) = statement else {
                return None;
            };
            let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
                return None;
            };
            let ast::Expr::Call(call) = assignment.value.as_ref() else {
                return None;
            };
            matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == receiver)
                .then(|| target.id.to_string())
        })
        .collect::<BTreeSet<_>>();
    function.body.iter().any(|statement| {
        matches!(statement, ast::Stmt::Return(returned)
            if matches!(returned.value.as_deref(), Some(ast::Expr::Name(name))
                if constructed.contains(name.id.as_str())))
    })
}

fn remove_factory_target_bindings(target: &ast::Expr, factories: &mut BTreeSet<String>) {
    let mut names = BTreeSet::new();
    collect_target_names(target, &mut names);
    for name in names {
        factories.remove(&name);
    }
}

fn remove_predicate_method_target_bindings(
    target: &ast::Expr,
    predicates: &mut BTreeMap<String, PredicateKind>,
) {
    let mut names = BTreeSet::new();
    collect_target_names(target, &mut names);
    for name in names {
        predicates.remove(&name);
    }
}

fn class_requires_zero_argument_constructor(
    class: &ast::StmtClassDef,
    bindings: &Bindings,
) -> bool {
    let mut factories = BTreeSet::new();
    for base in &class.bases {
        let ast::Expr::Name(base) = base else {
            continue;
        };
        if let Some(inherited) = bindings.classes.get(base.id.as_str()) {
            factories.extend(inherited.zero_argument_factories.iter().cloned());
        }
    }
    let mut class_bindings = bindings.clone();
    for statement in &class.body {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                factories.remove(function.name.as_str());
                if is_zero_argument_class_factory(function, &class_bindings) {
                    factories.insert(function.name.to_string());
                }
                class_bindings.canonical.remove(function.name.as_str());
                class_bindings.typing_types.remove(function.name.as_str());
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    remove_factory_target_bindings(target, &mut factories);
                    remove_target_binding(target, &mut class_bindings);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                remove_factory_target_bindings(&assignment.target, &mut factories);
                remove_target_binding(&assignment.target, &mut class_bindings);
            }
            _ => {}
        }
    }
    !factories.is_empty()
}

fn method_accepts_zero_explicit_arguments(function: &ast::StmtFunctionDef) -> bool {
    function
        .args
        .posonlyargs
        .iter()
        .chain(&function.args.args)
        .skip(1)
        .all(|argument| argument.default.is_some())
        && function
            .args
            .kwonlyargs
            .iter()
            .all(|argument| argument.default.is_some())
}

fn collect_method_declaration(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
) -> MethodDeclaration {
    MethodDeclaration {
        inline: has_decorator(&function.decorator_list, bindings, "Inline"),
        pure: has_decorator(&function.decorator_list, bindings, "Pure"),
        keyword_parameters: function
            .args
            .args
            .iter()
            .skip(1)
            .chain(function.args.kwonlyargs.iter())
            .map(|argument| argument.def.arg.to_string())
            .collect(),
        parameter_has_default: function
            .args
            .posonlyargs
            .iter()
            .chain(&function.args.args)
            .skip(1)
            .chain(&function.args.kwonlyargs)
            .map(|argument| argument.default.is_some())
            .collect(),
        exceptional_types: declared_exception_types(function, bindings),
    }
}

fn override_defaults_are_incompatible(current: &[bool], inherited: &[bool]) -> bool {
    current.len() == inherited.len()
        && current
            .iter()
            .zip(inherited)
            .any(|(current, inherited)| current != inherited)
}

fn declared_exception_types(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
) -> BTreeSet<String> {
    function
        .body
        .iter()
        .filter_map(|statement| {
            let ast::Stmt::Expr(expression) = statement else {
                return None;
            };
            let call = direct_contract_call(&expression.value, bindings)?;
            if call_name(call, bindings) != Some("Exsures") {
                return None;
            }
            let ast::Expr::Name(exception_type) = call.args.first()? else {
                return None;
            };
            Some(exception_type.id.to_string())
        })
        .collect()
}

fn is_local_type_alias_expression(expression: &ast::Expr, bindings: &Bindings) -> bool {
    let ast::Expr::Subscript(subscript) = expression else {
        return false;
    };
    let ast::Expr::Name(name) = subscript.value.as_ref() else {
        return false;
    };
    bindings
        .typing_types
        .get(name.id.as_str())
        .is_some_and(|canonical| typing_alias_constructors().contains(&canonical.as_str()))
}

fn validate_inline_method_declaration(
    class: &ast::StmtClassDef,
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    let inline = canonical_decorator(&function.decorator_list, bindings, "Inline");
    if function.name.as_str() == "__init__" && inline.is_some() {
        return invalid_code(
            function,
            source,
            INLINE_CONSTRUCTOR_UNSUPPORTED,
            "constructors cannot be inlined",
        );
    }
    let overrides_inline_boundary = class.bases.iter().any(|base| {
        let ast::Expr::Name(base) = base else {
            return false;
        };
        bindings
            .classes
            .get(base.id.as_str())
            .and_then(|declaration| declaration.methods.get(function.name.as_str()))
            .is_some_and(|inherited| inherited.inline || inline.is_some())
    });
    if overrides_inline_boundary {
        if inline.is_some() {
            return invalid_code(
                function,
                source,
                OVERRIDING_INLINE_METHOD,
                "an inline method cannot override a source method",
            );
        }
        return invalid_code(
            function,
            source,
            OVERRIDING_INLINE_METHOD,
            "a source method cannot override an inline method",
        );
    }
    Ok(())
}

fn validate_behavioral_override_declaration(
    class: &ast::StmtClassDef,
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    let current = collect_method_declaration(function, bindings);
    if function.name.as_str() == "__init__"
        && class_requires_zero_argument_constructor(class, bindings)
        && !method_accepts_zero_explicit_arguments(function)
    {
        return invalid_code(
            function,
            source,
            INVALID_OVERRIDE,
            "constructor requires arguments even though an effective inherited class factory calls cls() without arguments",
        );
    }
    for base in &class.bases {
        let ast::Expr::Name(base) = base else {
            continue;
        };
        let Some(inherited) = bindings
            .classes
            .get(base.id.as_str())
            .and_then(|declaration| declaration.methods.get(function.name.as_str()))
        else {
            continue;
        };
        if current.pure || inherited.pure {
            return invalid_code(
                function,
                source,
                INVALID_OVERRIDE,
                "Pure methods are statically bound mathematical functions and cannot participate in runtime method overriding",
            );
        }
        if function.name.as_str() != "__init__"
            && current.keyword_parameters != inherited.keyword_parameters
        {
            return invalid_code(
                function,
                source,
                INVALID_OVERRIDE,
                "overriding method changes keyword-callable parameter names",
            );
        }
        if function.name.as_str() != "__init__"
            && override_defaults_are_incompatible(
                &current.parameter_has_default,
                &inherited.parameter_has_default,
            )
        {
            return invalid_code(
                function,
                source,
                INVALID_OVERRIDE,
                "overriding method changes whether a parameter is required or defaulted",
            );
        }
        if let Some(exception_type) = current.exceptional_types.iter().find(|exception_type| {
            !inherited
                .exceptional_types
                .iter()
                .any(|allowed| is_class_subtype(exception_type, allowed, bindings))
        }) {
            return invalid_code(
                function,
                source,
                INVALID_OVERRIDE,
                format!(
                    "overriding method widens its declared exceptional outcomes with {exception_type:?}"
                ),
            );
        }
    }
    Ok(())
}

fn is_class_subtype(actual: &str, expected: &str, bindings: &Bindings) -> bool {
    if actual == expected {
        return true;
    }
    let mut pending = vec![actual];
    let mut visited = BTreeSet::new();
    while let Some(current) = pending.pop() {
        if !visited.insert(current.to_owned()) {
            continue;
        }
        let Some(declaration) = bindings.classes.get(current) else {
            continue;
        };
        if declaration.bases.contains(expected) {
            return true;
        }
        pending.extend(declaration.bases.iter().map(String::as_str));
    }
    false
}

fn is_non_runtime_class_base(base: &ast::Expr, bindings: &Bindings) -> bool {
    matches!(
        base,
        ast::Expr::Name(name)
            if bindings.typing_types.get(name.id.as_str()).map(String::as_str) == Some("Sized")
    ) || matches!(
        base,
        ast::Expr::Subscript(subscript)
            if matches!(subscript.value.as_ref(), ast::Expr::Name(name)
                if bindings.typing_types.get(name.id.as_str()).map(String::as_str) == Some("Generic"))
    )
}

fn is_canonical_adt_product_class(class: &ast::StmtClassDef, bindings: &Bindings) -> bool {
    let [ast::Expr::Name(root), ast::Expr::Call(product)] = class.bases.as_slice() else {
        return false;
    };
    bindings.adt_roots.contains(root.id.as_str())
        && matches!(product.func.as_ref(), ast::Expr::Name(factory)
            if bindings.typing_types.get(factory.id.as_str()).map(String::as_str)
                == Some("NamedTuple"))
}

fn validate_class_declaration_shape(
    class: &ast::StmtClassDef,
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    let runtime_bases = class
        .bases
        .iter()
        .filter(|base| !is_non_runtime_class_base(base, bindings))
        .count();
    if runtime_bases > 1 && !is_canonical_adt_product_class(class, bindings) {
        return invalid_code(
            class,
            source,
            MULTIPLE_INHERITANCE_UNSUPPORTED,
            format!(
                "class {:?} declares {runtime_bases} runtime base classes",
                class.name
            ),
        );
    }
    if let Some(keyword) = class.keywords.iter().find(|keyword| {
        keyword
            .arg
            .as_ref()
            .is_some_and(|name| name.as_str() == "metaclass")
            && !matches!(&keyword.value, ast::Expr::Name(name)
                if canonical_name(bindings, name.id.as_str()) == Some("ABCMeta"))
    }) {
        return invalid_code(
            keyword,
            source,
            METACLASS_UNSUPPORTED,
            "only the built-in ABCMeta metaclass is supported",
        );
    }
    Ok(())
}

fn is_illegal_magic_method_name(name: &str) -> bool {
    name.starts_with("__") && name.ends_with("__") && !is_legal_magic_method_name(name)
}

fn is_legal_magic_method_name(name: &str) -> bool {
    matches!(
        name,
        "__eq__"
            | "__ne__"
            | "__gt__"
            | "__ge__"
            | "__lt__"
            | "__le__"
            | "__add__"
            | "__sub__"
            | "__mul__"
            | "__matmul__"
            | "__truediv__"
            | "__floordiv__"
            | "__mod__"
            | "__divmod__"
            | "__pow__"
            | "__lshift__"
            | "__rshift__"
            | "__and__"
            | "__or__"
            | "__xor__"
            | "__neg__"
            | "__pos__"
            | "__invert__"
            | "__radd__"
            | "__rsub__"
            | "__rmul__"
            | "__rmatmul__"
            | "__rtruediv__"
            | "__rfloordiv__"
            | "__rmod__"
            | "__rdivmod__"
            | "__rpow__"
            | "__rlshift__"
            | "__rrshift__"
            | "__rand__"
            | "__rxor__"
            | "__ror__"
            | "__init__"
            | "__post_init__"
            | "__enter__"
            | "__exit__"
            | "__str__"
            | "__repr__"
            | "__len__"
            | "__bool__"
            | "__format__"
            | "__hash__"
            | "__getitem__"
            | "__setitem__"
            | "__iadd__"
            | "__isub__"
            | "__imul__"
            | "__imatmul__"
            | "__itruediv__"
            | "__ifloordiv__"
            | "__imod__"
            | "__ipow__"
            | "__ilshift__"
            | "__irshift__"
            | "__iand__"
            | "__ior__"
            | "__ixor__"
    )
}

fn validate_module_statement(
    statement: &ast::Stmt,
    bindings: &Bindings,
    final_function_bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    match statement {
        ast::Stmt::FunctionDef(function) => {
            let runtime_bindings =
                bindings_with_final_function_catalog(bindings, final_function_bindings);
            validate_function(function, &runtime_bindings, None, source)
        }
        ast::Stmt::ClassDef(class) => {
            validate_class_declaration_shape(class, bindings, source)?;
            let mut class_bindings = bindings.clone();
            let current_class_declaration = collect_class_declaration(class, bindings);
            for item in &class.body {
                match item {
                    ast::Stmt::FunctionDef(function) => {
                        validate_behavioral_override_declaration(
                            class,
                            function,
                            &class_bindings,
                            source,
                        )?;
                        let mut runtime_bindings = bindings_with_final_function_catalog(
                            &class_bindings,
                            final_function_bindings,
                        );
                        runtime_bindings
                            .classes
                            .insert(class.name.to_string(), current_class_declaration.clone());
                        validate_function(
                            function,
                            &runtime_bindings,
                            Some(class.name.as_str()),
                            source,
                        )?;
                        validate_inline_method_declaration(
                            class,
                            function,
                            &class_bindings,
                            source,
                        )?;
                        class_bindings.canonical.remove(function.name.as_str());
                        class_bindings.typing_types.remove(function.name.as_str());
                    }
                    ast::Stmt::Expr(expression) => validate_expression(
                        &expression.value,
                        &class_bindings,
                        ExpressionContext::Runtime,
                        source,
                    )?,
                    ast::Stmt::Import(_) | ast::Stmt::ImportFrom(_) => {
                        return invalid_code(
                            item,
                            source,
                            LOCAL_IMPORT,
                            "imports are supported only at module scope",
                        );
                    }
                    ast::Stmt::Assign(assignment) => {
                        if is_local_type_alias_expression(&assignment.value, &class_bindings) {
                            return invalid_code(
                                item,
                                source,
                                LOCAL_TYPE_ALIAS,
                                "type aliases are supported only at module scope",
                            );
                        }
                        validate_expression(
                            &assignment.value,
                            &class_bindings,
                            ExpressionContext::Runtime,
                            source,
                        )?;
                        for target in &assignment.targets {
                            remove_target_binding(target, &mut class_bindings);
                        }
                    }
                    ast::Stmt::AnnAssign(assignment) => {
                        if let Some(value) = assignment.value.as_deref() {
                            if is_local_type_alias_expression(value, &class_bindings) {
                                return invalid_code(
                                    item,
                                    source,
                                    LOCAL_TYPE_ALIAS,
                                    "type aliases are supported only at module scope",
                                );
                            }
                            validate_expression(
                                value,
                                &class_bindings,
                                ExpressionContext::Runtime,
                                source,
                            )?;
                        }
                        remove_target_binding(&assignment.target, &mut class_bindings);
                    }
                    ast::Stmt::ClassDef(nested) => {
                        return invalid_code(
                            nested,
                            source,
                            NESTED_CLASS_DECLARATION,
                            "nested class declarations are outside the verified source graph",
                        );
                    }
                    _ => {}
                }
            }
            Ok(())
        }
        ast::Stmt::Expr(expression) => {
            if let Some(call) = direct_contract_call(&expression.value, bindings) {
                if matches!(
                    call_name(call, bindings),
                    Some("Terminates" | "TerminationMeasure")
                ) {
                    // IO properties have more specific placement and dependency rules.
                    // Their source-bound validator runs after every IO declaration has
                    // passed signature validation, preserving declaration precedence.
                    return Ok(());
                }
                if call_name(call, bindings) == Some("Assert") {
                    return validate_call_argument(
                        call,
                        bindings,
                        ExpressionContext::Runtime,
                        source,
                    );
                }
                if matches!(call_name(call, bindings), Some("Fold" | "Unfold")) {
                    return validate_call_argument(
                        call,
                        bindings,
                        ExpressionContext::LoopInvariant,
                        source,
                    );
                }
                return invalid(
                    call,
                    source,
                    "contract primitives cannot execute at module scope",
                );
            }
            validate_expression(
                &expression.value,
                bindings,
                ExpressionContext::Runtime,
                source,
            )
        }
        _ => Ok(()),
    }
}

#[derive(Default)]
struct PureBodyExitCollector {
    has_return: bool,
    has_raise: bool,
}

impl Visitor for PureBodyExitCollector {
    fn visit_stmt_return(&mut self, _node: ast::StmtReturn) {
        self.has_return = true;
    }

    fn visit_stmt_raise(&mut self, _node: ast::StmtRaise) {
        self.has_raise = true;
    }

    fn visit_stmt_match(&mut self, node: ast::StmtMatch) {
        for case in node.cases {
            for statement in case.body {
                self.visit_stmt(statement);
            }
        }
    }
}

fn block_definitely_exits(block: &[ast::Stmt]) -> bool {
    block.last().is_some_and(statement_definitely_exits)
}

fn statement_definitely_exits(statement: &ast::Stmt) -> bool {
    match statement {
        ast::Stmt::Return(_)
        | ast::Stmt::Raise(_)
        | ast::Stmt::Break(_)
        | ast::Stmt::Continue(_) => true,
        ast::Stmt::If(branch) => {
            !branch.orelse.is_empty()
                && block_definitely_exits(&branch.body)
                && block_definitely_exits(&branch.orelse)
        }
        _ => false,
    }
}

enum DeadCode<'a> {
    UnreachableReturn(&'a ast::Stmt),
    UnreachableStatement(&'a ast::Stmt),
}

impl<'a> DeadCode<'a> {
    fn statement(&self) -> &'a ast::Stmt {
        match *self {
            Self::UnreachableReturn(statement) | Self::UnreachableStatement(statement) => statement,
        }
    }

    fn ordinary_return_avoids_type_lookup(&self) -> bool {
        let Self::UnreachableReturn(ast::Stmt::Return(returned)) = *self else {
            return false;
        };
        returned
            .value
            .as_deref()
            .is_none_or(|value| matches!(value, ast::Expr::Constant(_)))
    }
}

fn first_dead_code(block: &[ast::Stmt]) -> Option<DeadCode<'_>> {
    let mut previous_exits = false;
    for statement in block {
        if previous_exits {
            return Some(if matches!(statement, ast::Stmt::Return(_)) {
                DeadCode::UnreachableReturn(statement)
            } else {
                DeadCode::UnreachableStatement(statement)
            });
        }
        if let Some(dead) = statement_dead_code(statement) {
            return Some(dead);
        }
        previous_exits = statement_definitely_exits(statement);
    }
    None
}

fn statement_dead_code(statement: &ast::Stmt) -> Option<DeadCode<'_>> {
    match statement {
        ast::Stmt::If(branch) => {
            first_dead_code(&branch.body).or_else(|| first_dead_code(&branch.orelse))
        }
        ast::Stmt::While(loop_statement) => first_dead_code(&loop_statement.body)
            .or_else(|| first_dead_code(&loop_statement.orelse)),
        ast::Stmt::For(loop_statement) => first_dead_code(&loop_statement.body)
            .or_else(|| first_dead_code(&loop_statement.orelse)),
        ast::Stmt::Try(try_statement) => first_dead_code(&try_statement.body)
            .or_else(|| first_dead_code(&try_statement.orelse))
            .or_else(|| first_dead_code(&try_statement.finalbody))
            .or_else(|| {
                try_statement.handlers.iter().find_map(|handler| {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    first_dead_code(&handler.body)
                })
            }),
        ast::Stmt::Match(match_statement) => match_statement
            .cases
            .iter()
            .find_map(|case| first_dead_code(&case.body)),
        _ => None,
    }
}

fn validate_io_operation_declaration(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    debug_assert!(
        canonical_decorator(&function.decorator_list, bindings, "IOOperation").is_some(),
        "caller established the canonical IOOperation decorator"
    );

    if !function
        .returns
        .as_deref()
        .is_some_and(|annotation| canonical_annotation_name(annotation, bindings) == Some("bool"))
    {
        return invalid_code(
            function,
            source,
            IO_OPERATION_RETURN_TYPE_NOT_BOOL,
            "IO operations must declare a bool return type",
        );
    }
    if function.args.vararg.is_some() {
        return invalid_code(
            function,
            source,
            IO_OPERATION_VARARG,
            "IO operations cannot declare variadic positional arguments",
        );
    }
    if function.args.kwarg.is_some() {
        return invalid_code(
            function,
            source,
            IO_OPERATION_KWARG,
            "IO operations cannot declare variadic keyword arguments",
        );
    }

    let positional = function
        .args
        .posonlyargs
        .iter()
        .chain(&function.args.args)
        .collect::<Vec<_>>();
    if positional
        .iter()
        .filter_map(|argument| argument.default.as_deref())
        .any(|default| !is_result_default(default, bindings))
    {
        return invalid_code(
            function,
            source,
            IO_OPERATION_DEFAULT_ARGUMENT,
            "IO operation output defaults must be canonical Result() calls",
        );
    }

    let first_output = positional
        .iter()
        .position(|argument| argument.default.is_some())
        .unwrap_or(positional.len());
    let (inputs, outputs) = positional.split_at(first_output);
    if inputs
        .first()
        .is_none_or(|argument| !argument_is_canonical_place(argument, bindings))
        || inputs
            .iter()
            .skip(1)
            .any(|argument| argument_is_canonical_place(argument, bindings))
    {
        return invalid_code(
            function,
            source,
            IO_OPERATION_INVALID_PRESET,
            "IO operations require exactly one leading non-default Place input",
        );
    }

    let place_outputs = outputs
        .iter()
        .enumerate()
        .filter_map(|(index, argument)| {
            argument_is_canonical_place(argument, bindings).then_some(index)
        })
        .collect::<Vec<_>>();
    if place_outputs.len() > 1
        || place_outputs
            .first()
            .is_some_and(|index| *index + 1 != outputs.len())
    {
        return invalid_code(
            function,
            source,
            IO_OPERATION_INVALID_POSTSET,
            "an IO operation may have at most one Place output and it must be last",
        );
    }
    Ok(())
}

fn canonical_annotation_name<'a>(
    annotation: &'a ast::Expr,
    bindings: &'a Bindings,
) -> Option<&'a str> {
    let ast::Expr::Name(name) = annotation else {
        return None;
    };
    canonical_name(bindings, name.id.as_str())
}

fn argument_is_canonical_place(argument: &ast::ArgWithDefault, bindings: &Bindings) -> bool {
    argument
        .def
        .annotation
        .as_deref()
        .is_some_and(|annotation| canonical_annotation_name(annotation, bindings) == Some("Place"))
}

fn is_result_default(expression: &ast::Expr, bindings: &Bindings) -> bool {
    let ast::Expr::Call(call) = expression else {
        return false;
    };
    call.args.is_empty() && call.keywords.is_empty() && call_name(call, bindings) == Some("Result")
}

fn validate_function(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    enclosing_class: Option<&str>,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    if is_illegal_magic_method_name(function.name.as_str()) {
        return invalid_code(
            function,
            source,
            ILLEGAL_MAGIC_METHOD,
            format!(
                "magic method {:?} is outside Nagini's supported method protocol",
                function.name
            ),
        );
    }
    let pure = has_decorator(&function.decorator_list, bindings, "Pure");
    let predicate = has_decorator(&function.decorator_list, bindings, "Predicate");
    let io_operation = has_decorator(&function.decorator_list, bindings, "IOOperation");
    let inline = canonical_decorator(&function.decorator_list, bindings, "Inline");
    if pure && io_operation {
        return invalid_code(
            function,
            source,
            DECORATORS_INCOMPATIBLE,
            "Pure and IOOperation cannot decorate the same function",
        );
    }
    if inline.is_some() && (pure || predicate) {
        return invalid_code(
            function,
            source,
            DECORATORS_INCOMPATIBLE,
            "Inline cannot be combined with Pure or Predicate",
        );
    }
    if canonical_decorator(&function.decorator_list, bindings, "Opaque").is_some() && !pure {
        return invalid_code(
            function,
            source,
            DECORATORS_INCOMPATIBLE,
            "Opaque functions must also be Pure",
        );
    }
    if io_operation {
        validate_io_operation_declaration(function, bindings, source)?;
    }
    let mut function_bindings =
        bindings_without_function_locals(function, bindings, enclosing_class);
    function_bindings.allow_abstract_predicate_operations =
        has_decorator(&function.decorator_list, bindings, "ContractOnly");
    let bindings = &function_bindings;
    let dead_code = first_dead_code(&function.body);
    if pure {
        if function.returns.as_deref().and_then(annotation_name) == Some("None") {
            return invalid_code(
                function,
                source,
                PURE_FUNCTION_TYPE_NONE,
                "pure functions must return a value",
            );
        }
        let declares_exception = function.body.iter().any(|statement| {
            let ast::Stmt::Expr(expression) = statement else {
                return false;
            };
            direct_contract_call(&expression.value, bindings)
                .is_some_and(|call| call_name(call, bindings) == Some("Exsures"))
        });
        let mut exits = PureBodyExitCollector::default();
        for statement in &function.body {
            exits.visit_stmt(statement.clone());
        }
        if declares_exception || exits.has_raise {
            return invalid_code(
                function,
                source,
                PURE_FUNCTION_THROWS_EXCEPTION,
                "pure functions cannot declare or raise exceptions",
            );
        }
        if let Some(dead) = dead_code {
            return match dead {
                DeadCode::UnreachableReturn(_) => invalid_code(
                    function,
                    source,
                    PURE_FUNCTION_DEAD_CODE,
                    "pure function contains an unreachable return statement",
                ),
                DeadCode::UnreachableStatement(statement) => invalid_code(
                    statement,
                    source,
                    TYPE_ERROR_DEAD_CODE,
                    "statement is statically unreachable after an unconditional control-flow exit",
                ),
            };
        }
    } else if let Some(dead) = dead_code {
        // Nagini's ordinary-function `type.error:dead.code` is not a blanket
        // unreachable-code diagnostic. It is raised when translation asks its
        // mypy type map for an unreachable node that mypy did not type. A
        // literal return does not require that lookup, whereas an IO operation
        // body is translated as a typed relation and does. Keep pure-function
        // handling above separate because its translator has its own explicit
        // duplicate-return rule.
        if io_operation || !dead.ordinary_return_avoids_type_lookup() {
            return invalid_code(
                dead.statement(),
                source,
                TYPE_ERROR_DEAD_CODE,
                "unreachable statement requires type information unavailable after an unconditional control-flow exit",
            );
        }
    }
    let contains_io_property = function.body.iter().any(|statement| {
        contains_canonical_call_in_statement(statement, bindings, "Terminates")
            || contains_canonical_call_in_statement(statement, bindings, "TerminationMeasure")
    });
    if predicate && !contains_io_property {
        validate_predicate_declaration(function, bindings, source)?;
    }
    let constructor = function.name.as_str() == "__init__";
    let mut body_started = false;
    let mut postcondition_seen = false;
    for (index, statement) in function.body.iter().enumerate() {
        if matches!(statement, ast::Stmt::Global(_) | ast::Stmt::Nonlocal(_)) {
            continue;
        }
        if index == 0 && is_docstring_statement(statement) {
            continue;
        }
        if let ast::Stmt::Expr(expression) = statement
            && let Some(call) = direct_contract_call(&expression.value, bindings)
        {
            let canonical = call_name(call, bindings).unwrap_or_default();
            if inline.is_some()
                && matches!(canonical, "Requires" | "Ensures" | "Exsures" | "Decreases")
            {
                return invalid_code(
                    call,
                    source,
                    CONTRACT_IN_INLINE_METHOD,
                    "inline functions cannot declare modular contracts",
                );
            }
            match canonical {
                "Requires" => {
                    if body_started || postcondition_seen {
                        return invalid(
                            call,
                            source,
                            "Requires must precede postconditions and executable statements",
                        );
                    }
                    validate_call_argument(
                        call,
                        bindings,
                        ExpressionContext::Precondition { pure },
                        source,
                    )?;
                    continue;
                }
                "Ensures" | "Exsures" => {
                    postcondition_seen = true;
                    if canonical == "Ensures" {
                        validate_result_contract(function, call, bindings, source)?;
                    }
                    validate_call_argument(
                        call,
                        bindings,
                        ExpressionContext::Postcondition { pure },
                        source,
                    )?;
                    continue;
                }
                "Decreases" => {
                    if !pure || body_started {
                        return invalid(
                            call,
                            source,
                            "Decreases is supported only in a pure-function contract prefix",
                        );
                    }
                    validate_call_argument(
                        call,
                        bindings,
                        ExpressionContext::Precondition { pure },
                        source,
                    )?;
                    continue;
                }
                "Invariant" => {
                    return invalid(call, source, "Invariant must be a loop-body prefix");
                }
                "Assert" => {
                    body_started = true;
                    validate_call_argument(
                        call,
                        bindings,
                        ExpressionContext::LoopInvariant,
                        source,
                    )?;
                    continue;
                }
                "Fold" | "Unfold" => {
                    validate_call_argument(
                        call,
                        bindings,
                        ExpressionContext::LoopInvariant,
                        source,
                    )?;
                    continue;
                }
                "Acc" | "Rd" | "Unfolding" => {
                    return invalid(
                        call,
                        source,
                        "permission expressions cannot be standalone runtime statements",
                    );
                }
                _ => {}
            }
        }
        if constructor && is_constructor_field_initialization(statement) {
            validate_runtime_statement(statement, bindings, source)?;
            continue;
        }
        if pure
            && let ast::Stmt::Assign(assignment) = statement
            && (assignment.targets.len() != 1
                || !matches!(assignment.targets.first(), Some(ast::Expr::Name(_))))
        {
            return invalid_code(
                statement,
                source,
                PURE_MULTI_ASSIGN_UNSUPPORTED,
                "pure functions require one simple assignment target",
            );
        }
        body_started = true;
        if predicate
            && let ast::Stmt::Return(returned) = statement
            && let Some(value) = returned.value.as_deref()
        {
            validate_expression(value, bindings, ExpressionContext::LoopInvariant, source)?;
            continue;
        }
        validate_runtime_statement(statement, bindings, source)?;
    }
    if pure {
        let mut exits = PureBodyExitCollector::default();
        for statement in &function.body {
            exits.visit_stmt(statement.clone());
        }
        if !exits.has_return {
            return invalid_code(
                function,
                source,
                PURE_FUNCTION_RETURN_MISSING,
                "pure functions with a value result must return a value",
            );
        }
    }
    Ok(())
}

fn validate_result_contract(
    function: &ast::StmtFunctionDef,
    call: &ast::ExprCall,
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    let declared = function.returns.as_deref().and_then(annotation_name);
    let returns_none = declared == Some("None");
    if returns_none && contains_canonical_call_in_call(call, bindings, "Result") {
        return invalid_code(
            call,
            source,
            INVALID_RESULT,
            "Result() is invalid for a function returning None",
        );
    }
    if let Some(result_type) = typed_result_ensures_type(call) {
        if returns_none {
            return invalid_code(
                call,
                source,
                INVALID_RESULT,
                "typed result postconditions are invalid for a function returning None",
            );
        }
        if let (Some(declared), Some(result_type)) = (declared, annotation_name(result_type))
            && declared != result_type
        {
            return invalid_code(
                call,
                source,
                INVALID_RESULT_TYPE,
                format!(
                    "typed result postcondition declares {result_type}, but the function returns {declared}"
                ),
            );
        }
    }
    if let Some(result_type) = first_canonical_call_argument(call, bindings, "ResultT")
        && let (Some(declared), Some(result_type)) = (declared, annotation_name(&result_type))
        && declared != result_type
    {
        return invalid_code(
            call,
            source,
            INCORRECT_DECLARED_TYPE,
            format!("ResultT declares {result_type}, but the function returns {declared}"),
        );
    }
    Ok(())
}

fn annotation_name(annotation: &ast::Expr) -> Option<&str> {
    match annotation {
        ast::Expr::Name(name) => Some(name.id.as_str()),
        ast::Expr::Constant(constant) if constant.value == ast::Constant::None => Some("None"),
        _ => None,
    }
}

fn typed_result_ensures_type(call: &ast::ExprCall) -> Option<&ast::Expr> {
    if call.args.len() == 2
        && call.keywords.is_empty()
        && matches!(call.args.get(1), Some(ast::Expr::Lambda(_)))
    {
        call.args.first()
    } else {
        None
    }
}

fn validate_predicate_declaration(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    if function.returns.as_deref().and_then(annotation_name) != Some("bool") {
        return invalid_code(
            function,
            source,
            INVALID_PREDICATE,
            "predicate functions must declare a bool return type",
        );
    }
    let executable = function
        .body
        .iter()
        .enumerate()
        .filter_map(|(index, statement)| {
            (index != 0 || !is_docstring_statement(statement)).then_some(statement)
        })
        .collect::<Vec<_>>();
    let [ast::Stmt::Return(returned)] = executable.as_slice() else {
        return invalid_code(
            function,
            source,
            INVALID_PREDICATE,
            "predicate bodies must consist of one return expression",
        );
    };
    let Some(value) = returned.value.as_deref() else {
        return invalid_code(
            function,
            source,
            INVALID_PREDICATE,
            "predicate bodies must return a boolean expression",
        );
    };
    let mut calls = PredicateCallValidator {
        bindings,
        invalid: false,
    };
    calls.visit_expr(value.clone());
    if calls.invalid {
        return invalid_code(
            function,
            source,
            INVALID_PREDICATE,
            "predicate bodies cannot call source-owned impure functions",
        );
    }
    Ok(())
}

fn is_docstring_statement(statement: &ast::Stmt) -> bool {
    matches!(statement, ast::Stmt::Expr(expression)
        if matches!(expression.value.as_ref(), ast::Expr::Constant(constant)
            if matches!(constant.value, ast::Constant::Str(_))))
}

struct PredicateCallValidator<'a> {
    bindings: &'a Bindings,
    invalid: bool,
}

impl Visitor for PredicateCallValidator<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if self.invalid {
            return;
        }
        let source_name = match node.func.as_ref() {
            ast::Expr::Name(name) => Some(name.id.as_str()),
            ast::Expr::Attribute(attribute) => Some(attribute.attr.as_str()),
            _ => None,
        };
        if source_name.is_some_and(|name| {
            self.bindings.declared_functions.contains(name)
                && !self.bindings.predicates.contains(name)
                && !self.bindings.pure_functions.contains(name)
        }) {
            self.invalid = true;
            return;
        }
        self.generic_visit_expr_call(node);
    }
}

fn bindings_without_function_locals(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    enclosing_class: Option<&str>,
) -> Bindings {
    let mut result = bindings.clone();
    result.nominal_values.clear();
    let parameters = function
        .args
        .posonlyargs
        .iter()
        .chain(&function.args.args)
        .chain(&function.args.kwonlyargs)
        .collect::<Vec<_>>();
    let mut locals = parameters
        .iter()
        .map(|argument| argument.def.arg.to_string())
        .collect::<BTreeSet<_>>();
    if let Some(argument) = function.args.vararg.as_deref() {
        locals.insert(argument.arg.to_string());
    }
    if let Some(argument) = function.args.kwarg.as_deref() {
        locals.insert(argument.arg.to_string());
    }
    let parameter_names = locals.clone();
    let mut collector = LocalBindingCollector::default();
    for statement in &function.body {
        collector.visit_stmt(statement.clone());
    }
    locals.extend(collector.names.iter().cloned());
    let mut provenance_bindings = result.clone();
    for local in &locals {
        provenance_bindings.active_class_values.remove(local);
    }
    for argument in &parameters {
        let name = argument.def.arg.as_str();
        if collector.names.contains(name) {
            continue;
        }
        if let Some(classes) = argument
            .def
            .annotation
            .as_deref()
            .and_then(|annotation| annotation_nominal_classes(annotation, bindings))
        {
            result
                .nominal_values
                .insert(name.to_owned(), NominalProvenance::UpperBound(classes));
        }
    }
    if let Some(enclosing_class) = enclosing_class
        && !has_decorator(&function.decorator_list, bindings, "classmethod")
        && !has_decorator(&function.decorator_list, bindings, "staticmethod")
        && let Some(receiver) = function
            .args
            .posonlyargs
            .first()
            .or_else(|| function.args.args.first())
        && !collector.names.contains(receiver.def.arg.as_str())
    {
        result.nominal_values.insert(
            receiver.def.arg.to_string(),
            NominalProvenance::UpperBound(BTreeSet::from([enclosing_class.to_owned()])),
        );
    }
    let mut earlier_loads = BTreeSet::new();
    for statement in &function.body {
        if let Some((target, value)) = direct_nominal_assignment(statement)
            && !parameter_names.contains(target)
            && collector.store_counts.get(target) == Some(&1)
            && !earlier_loads.contains(target)
        {
            let provenance =
                nominal_expression_provenance(value, &result.nominal_values, &provenance_bindings);
            result.nominal_values.insert(target.to_owned(), provenance);
        } else if let Some((target, provenance, stores)) =
            joined_if_nominal_provenance(statement, &result.nominal_values, &provenance_bindings)
            && !parameter_names.contains(target.as_str())
            && collector.store_counts.get(target.as_str()) == Some(&stores)
            && !earlier_loads.contains(target.as_str())
        {
            result.nominal_values.insert(target, provenance);
        }
        let mut loads = NameLoadCollector::default();
        loads.visit_stmt(statement.clone());
        earlier_loads.extend(loads.names);
    }
    for name in locals {
        result.canonical.remove(&name);
        result.predicates.remove(&name);
        result.pure_functions.remove(&name);
        result.declared_functions.remove(&name);
        result.io_operations.remove(&name);
        result.typing_types.remove(&name);
        result.module_predicates.remove(&name);
        result.active_class_values.remove(&name);
    }
    result
}

fn direct_nominal_assignment(statement: &ast::Stmt) -> Option<(&str, &ast::Expr)> {
    match statement {
        ast::Stmt::Assign(assignment) => {
            let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
                return None;
            };
            Some((target.id.as_str(), assignment.value.as_ref()))
        }
        ast::Stmt::AnnAssign(assignment) => {
            let ast::Expr::Name(target) = assignment.target.as_ref() else {
                return None;
            };
            Some((target.id.as_str(), assignment.value.as_deref()?))
        }
        _ => None,
    }
}

fn nominal_expression_provenance(
    expression: &ast::Expr,
    values: &BTreeMap<String, NominalProvenance>,
    bindings: &Bindings,
) -> NominalProvenance {
    match expression {
        ast::Expr::Name(name) => values
            .get(name.id.as_str())
            .cloned()
            .unwrap_or(NominalProvenance::Unknown),
        ast::Expr::IfExp(branch) => {
            nominal_expression_provenance(branch.body.as_ref(), values, bindings).join(
                nominal_expression_provenance(branch.orelse.as_ref(), values, bindings),
            )
        }
        ast::Expr::Call(construction) => match construction.func.as_ref() {
            ast::Expr::Name(class) if bindings.active_class_values.contains(class.id.as_str()) => {
                NominalProvenance::Exact(BTreeSet::from([class.id.to_string()]))
            }
            ast::Expr::Attribute(factory) => {
                let ast::Expr::Name(class) = factory.value.as_ref() else {
                    return NominalProvenance::Unknown;
                };
                let Some(declaration) = bindings.classes.get(class.id.as_str()) else {
                    return NominalProvenance::Unknown;
                };
                if bindings.active_class_values.contains(class.id.as_str())
                    && declaration
                        .dynamic_class_factories
                        .contains(factory.attr.as_str())
                {
                    NominalProvenance::Exact(BTreeSet::from([class.id.to_string()]))
                } else {
                    NominalProvenance::Unknown
                }
            }
            _ => NominalProvenance::Unknown,
        },
        _ => NominalProvenance::Unknown,
    }
}

fn joined_if_nominal_provenance(
    statement: &ast::Stmt,
    values: &BTreeMap<String, NominalProvenance>,
    bindings: &Bindings,
) -> Option<(String, NominalProvenance, usize)> {
    let ast::Stmt::If(branch) = statement else {
        return None;
    };
    let (left_target, left, left_stores) =
        branch_nominal_assignment(&branch.body, values, bindings)?;
    let (right_target, right, right_stores) =
        branch_nominal_assignment(&branch.orelse, values, bindings)?;
    let mut loads = NameLoadCollector::default();
    loads.visit_stmt(statement.clone());
    if loads.names.contains(left_target.as_str()) {
        return None;
    }
    if left_target != right_target {
        return None;
    }
    Some((
        left_target,
        left.join(right),
        left_stores.checked_add(right_stores)?,
    ))
}

fn branch_nominal_assignment(
    statements: &[ast::Stmt],
    values: &BTreeMap<String, NominalProvenance>,
    bindings: &Bindings,
) -> Option<(String, NominalProvenance, usize)> {
    let [statement] = statements else {
        return None;
    };
    match statement {
        ast::Stmt::Assign(assignment) => {
            let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
                return None;
            };
            Some((
                target.id.to_string(),
                nominal_expression_provenance(assignment.value.as_ref(), values, bindings),
                1,
            ))
        }
        ast::Stmt::AnnAssign(assignment) => {
            let ast::Expr::Name(target) = assignment.target.as_ref() else {
                return None;
            };
            let value = assignment.value.as_deref()?;
            Some((
                target.id.to_string(),
                nominal_expression_provenance(value, values, bindings),
                1,
            ))
        }
        ast::Stmt::If(_) => joined_if_nominal_provenance(statement, values, bindings),
        _ => None,
    }
}

fn annotation_nominal_classes(
    annotation: &ast::Expr,
    bindings: &Bindings,
) -> Option<BTreeSet<String>> {
    match annotation {
        ast::Expr::Name(name) if bindings.classes.contains_key(name.id.as_str()) => {
            Some(BTreeSet::from([name.id.to_string()]))
        }
        ast::Expr::Subscript(subscript)
            if matches!(subscript.value.as_ref(), ast::Expr::Name(name)
                if bindings.typing_types.get(name.id.as_str()).map(String::as_str) == Some("Union")) =>
        {
            let arms = match subscript.slice.as_ref() {
                ast::Expr::Tuple(tuple) => tuple.elts.as_slice(),
                arm => std::slice::from_ref(arm),
            };
            let mut classes = BTreeSet::new();
            for arm in arms {
                classes.extend(annotation_nominal_classes(arm, bindings)?);
            }
            (!classes.is_empty()).then_some(classes)
        }
        _ => None,
    }
}

#[derive(Default)]
struct LocalBindingCollector {
    names: BTreeSet<String>,
    store_counts: BTreeMap<String, usize>,
}

impl Visitor for LocalBindingCollector {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if node.ctx == ast::ExprContext::Store {
            self.names.insert(node.id.to_string());
            *self.store_counts.entry(node.id.to_string()).or_default() += 1;
        }
    }
}

#[derive(Default)]
struct NameLoadCollector {
    names: BTreeSet<String>,
}

impl Visitor for NameLoadCollector {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if node.ctx == ast::ExprContext::Load {
            self.names.insert(node.id.to_string());
        }
    }
}

fn is_constructor_field_initialization(statement: &ast::Stmt) -> bool {
    match statement {
        ast::Stmt::Assign(assignment) => assignment.targets.iter().all(|target| {
            matches!(target, ast::Expr::Attribute(attribute)
                if matches!(attribute.value.as_ref(), ast::Expr::Name(name)
                    if name.id.as_str() == "self"))
        }),
        ast::Stmt::AnnAssign(assignment) => {
            matches!(assignment.target.as_ref(), ast::Expr::Attribute(attribute)
                if matches!(attribute.value.as_ref(), ast::Expr::Name(name)
                    if name.id.as_str() == "self"))
        }
        _ => false,
    }
}

fn validate_runtime_statement(
    statement: &ast::Stmt,
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    match statement {
        ast::Stmt::FunctionDef(function) => invalid_code(
            function,
            source,
            NESTED_FUNCTION_DECLARATION,
            "nested function declarations are outside the verified source graph",
        ),
        ast::Stmt::ClassDef(class) => invalid_code(
            class,
            source,
            NESTED_CLASS_DECLARATION,
            "nested class declarations are outside the verified source graph",
        ),
        ast::Stmt::Import(_) | ast::Stmt::ImportFrom(_) => invalid_code(
            statement,
            source,
            LOCAL_IMPORT,
            "imports are supported only at module scope",
        ),
        ast::Stmt::Expr(expression) => {
            if let Some(call) = direct_contract_call(&expression.value, bindings) {
                match call_name(call, bindings) {
                    Some("Assert" | "Fold" | "Unfold") => {
                        return validate_call_argument(
                            call,
                            bindings,
                            ExpressionContext::LoopInvariant,
                            source,
                        );
                    }
                    Some(
                        "Requires" | "Ensures" | "Exsures" | "Invariant" | "Decreases" | "Acc"
                        | "Rd" | "Unfolding",
                    ) => {
                        return invalid(
                            call,
                            source,
                            "contract primitive is illegal in an executable nested block",
                        );
                    }
                    _ => {}
                }
            }
            validate_expression(
                &expression.value,
                bindings,
                ExpressionContext::Runtime,
                source,
            )
        }
        ast::Stmt::Assign(assignment) => {
            if is_local_type_alias_expression(&assignment.value, bindings) {
                return invalid_code(
                    statement,
                    source,
                    LOCAL_TYPE_ALIAS,
                    "type aliases are supported only at module scope",
                );
            }
            validate_expression(
                &assignment.value,
                bindings,
                ExpressionContext::Runtime,
                source,
            )
        }
        ast::Stmt::AnnAssign(assignment) => {
            if let Some(value) = assignment.value.as_deref() {
                if is_local_type_alias_expression(value, bindings) {
                    return invalid_code(
                        statement,
                        source,
                        LOCAL_TYPE_ALIAS,
                        "type aliases are supported only at module scope",
                    );
                }
                validate_expression(value, bindings, ExpressionContext::Runtime, source)?;
            }
            Ok(())
        }
        ast::Stmt::If(branch) => {
            validate_expression(&branch.test, bindings, ExpressionContext::Runtime, source)?;
            for item in branch.body.iter().chain(&branch.orelse) {
                validate_runtime_statement(item, bindings, source)?;
            }
            Ok(())
        }
        ast::Stmt::While(loop_statement) => {
            validate_expression(
                &loop_statement.test,
                bindings,
                ExpressionContext::Runtime,
                source,
            )?;
            validate_loop_body(&loop_statement.body, bindings, source)?;
            for item in &loop_statement.orelse {
                validate_runtime_statement(item, bindings, source)?;
            }
            Ok(())
        }
        ast::Stmt::For(loop_statement) => {
            validate_expression(
                &loop_statement.iter,
                bindings,
                ExpressionContext::Runtime,
                source,
            )?;
            validate_loop_body(&loop_statement.body, bindings, source)?;
            for item in &loop_statement.orelse {
                validate_runtime_statement(item, bindings, source)?;
            }
            Ok(())
        }
        ast::Stmt::Return(returned) => {
            if let Some(value) = returned.value.as_deref() {
                validate_expression(value, bindings, ExpressionContext::Runtime, source)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn validate_loop_body(
    body: &[ast::Stmt],
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    let mut executable_seen = false;
    for statement in body {
        if let ast::Stmt::Expr(expression) = statement
            && let Some(call) = direct_contract_call(&expression.value, bindings)
            && call_name(call, bindings) == Some("Invariant")
        {
            if executable_seen {
                return invalid(call, source, "Invariant must precede the loop body");
            }
            validate_call_argument(call, bindings, ExpressionContext::LoopInvariant, source)?;
        } else {
            executable_seen = true;
            validate_runtime_statement(statement, bindings, source)?;
        }
    }
    Ok(())
}

fn validate_call_argument(
    call: &ast::ExprCall,
    bindings: &Bindings,
    context: ExpressionContext,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    match call_name(call, bindings) {
        Some("Fold" | "Unfold") => {
            validate_predicate_contract_operand(call, 1, bindings, source)?;
            return validate_expression(
                &call.args[0],
                bindings,
                ExpressionContext::LoopInvariant,
                source,
            );
        }
        Some("Unfolding") => {
            validate_predicate_contract_operand(call, 2, bindings, source)?;
            validate_expression(
                &call.args[0],
                bindings,
                ExpressionContext::LoopInvariant,
                source,
            )?;
            return validate_expression(
                &call.args[1],
                bindings,
                ExpressionContext::UnfoldingValue,
                source,
            );
        }
        _ => {}
    }
    for argument in &call.args {
        validate_expression(argument, bindings, context, source)?;
    }
    for keyword in &call.keywords {
        validate_expression(&keyword.value, bindings, context, source)?;
    }
    Ok(())
}

fn validate_predicate_contract_operand(
    call: &ast::ExprCall,
    expected_arguments: usize,
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    if call.args.len() != expected_arguments || !call.keywords.is_empty() {
        return invalid_code(
            call,
            source,
            INVALID_CONTRACT_CALL,
            format!(
                "{} requires exactly {expected_arguments} positional argument{}",
                call_name(call, bindings).unwrap_or("predicate contract"),
                if expected_arguments == 1 { "" } else { "s" }
            ),
        );
    }
    let Some(operand) = call.args.first() else {
        return invalid_code(
            call,
            source,
            INVALID_CONTRACT_CALL,
            "Fold, Unfold, and Unfolding require a source-declared @Predicate call",
        );
    };
    let ast::Expr::Call(operand_call) = operand else {
        return invalid_code(
            call,
            source,
            INVALID_CONTRACT_CALL,
            "Fold, Unfold, and Unfolding require a source-declared @Predicate call",
        );
    };
    let predicate = if matches!(call_name(operand_call, bindings), Some("Acc" | "Rd")) {
        if operand_call.keywords.is_empty()
            && matches!(operand_call.args.len(), 1 | 2)
            && let Some(ast::Expr::Call(predicate)) = operand_call.args.first()
        {
            predicate
        } else {
            return invalid_code(
                operand_call,
                source,
                INVALID_CONTRACT_CALL,
                "permission-wrapped predicate operands require Acc/Rd(predicate_call[, amount])",
            );
        }
    } else {
        operand_call
    };
    match resolve_predicate_kind(predicate, bindings) {
        Some(PredicateKind::Concrete) => {}
        Some(PredicateKind::Abstract) if bindings.allow_abstract_predicate_operations => {}
        Some(PredicateKind::Abstract) => {
            return invalid_code(
                call,
                source,
                ABSTRACT_PREDICATE_FOLD,
                "ContractOnly predicates are abstract specifications and cannot be folded or unfolded",
            );
        }
        None => {
            return invalid_code(
                call,
                source,
                INVALID_CONTRACT_CALL,
                "predicate contract operand is not bound to an exact source-declared @Predicate function or method",
            );
        }
    }
    Ok(())
}

fn resolve_predicate_kind(call: &ast::ExprCall, bindings: &Bindings) -> Option<PredicateKind> {
    match call.func.as_ref() {
        ast::Expr::Name(name) => bindings.module_predicates.get(name.id.as_str()).copied(),
        ast::Expr::Attribute(attribute) => {
            let ast::Expr::Name(receiver) = attribute.value.as_ref() else {
                return None;
            };
            let classes = bindings
                .nominal_values
                .get(receiver.id.as_str())?
                .classes()?;
            let mut kinds = classes.iter().map(|class| {
                bindings
                    .classes
                    .get(class)?
                    .predicate_methods
                    .get(attribute.attr.as_str())
                    .copied()
            });
            let first = kinds.next()??;
            kinds.all(|kind| kind == Some(first)).then_some(first)
        }
        _ => None,
    }
}

fn validate_expression(
    expression: &ast::Expr,
    bindings: &Bindings,
    context: ExpressionContext,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    let mut validator = ExpressionValidator {
        bindings,
        context,
        source,
        failure: None,
    };
    validator.visit_expr(expression.clone());
    validator.failure.map_or(Ok(()), Err)
}

struct ExpressionValidator<'a> {
    bindings: &'a Bindings,
    context: ExpressionContext,
    source: &'a str,
    failure: Option<ContractPositionFailure>,
}

impl ExpressionValidator<'_> {
    fn reject(&mut self, expression: &impl Ranged, message: impl Into<String>) {
        if self.failure.is_none() {
            self.failure = Some(failure_at(expression, self.source, message));
        }
    }
}

/// Return true only when an ASCII character proves that Python's `float(str)` parser cannot
/// accept the literal.  Unknown spellings deliberately return false and continue to the semantic
/// frontend; this preflight must never reject a Python-valid spelling merely because Rust's float
/// parser differs.  The accepted alphabet covers decimal/exponent syntax plus the case-insensitive
/// `inf`, `infinity`, and `nan` spellings.  Non-ASCII text is left unknown because Python accepts
/// some Unicode decimal digits.
fn definitely_invalid_python_float_literal(value: &str) -> bool {
    value.chars().any(|character| {
        if !character.is_ascii() {
            return false;
        }
        character.is_ascii_graphic()
            && !matches!(
                character,
                '0'..='9'
                    | '+'
                    | '-'
                    | '.'
                    | '_'
                    | 'e'
                    | 'E'
                    | 'i'
                    | 'I'
                    | 'n'
                    | 'N'
                    | 'f'
                    | 'F'
                    | 'a'
                    | 'A'
                    | 't'
                    | 'T'
                    | 'y'
                    | 'Y'
            )
    })
}

impl Visitor for ExpressionValidator<'_> {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if self.failure.is_none()
            && node.id.as_str() == "_"
            && matches!(node.ctx, ast::ExprContext::Load | ast::ExprContext::Del)
        {
            self.failure = Some(failure_at_code(
                &node,
                self.source,
                WILDCARD_VARIABLE_READ,
                "the wildcard assignment target cannot be read as a value",
            ));
        }
    }

    fn visit_expr_tuple(&mut self, node: ast::ExprTuple) {
        if self.failure.is_some() {
            return;
        }
        if node.elts.len() > 9 {
            self.failure = Some(failure_at_code(
                &node,
                self.source,
                LARGE_TUPLE_UNSUPPORTED,
                format!(
                    "tuple expression has {} elements; Nagini supports at most 9",
                    node.elts.len()
                ),
            ));
            return;
        }
        self.generic_visit_expr_tuple(node);
    }

    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if self.failure.is_some() {
            return;
        }
        if let Some(lambda) = io_exists_lambda(&node, self.bindings) {
            if let Err(failure) = validate_io_exists_lambda(lambda, self.bindings, self.source) {
                self.failure = Some(failure);
            }
            return;
        }
        let canonical = call_name(&node, self.bindings);
        if canonical == Some("float") && node.args.len() == 1 && node.keywords.is_empty() {
            match &node.args[0] {
                ast::Expr::Constant(ast::ExprConstant {
                    value: ast::Constant::Str(value),
                    ..
                }) if definitely_invalid_python_float_literal(value) => {
                    self.failure = Some(failure_at_code(
                        &node,
                        self.source,
                        INVALID_FLOAT_VALUE,
                        format!(
                            "float literal {value:?} is not a valid Python floating-point value"
                        ),
                    ));
                    return;
                }
                ast::Expr::Constant(ast::ExprConstant {
                    value: ast::Constant::Str(_),
                    ..
                }) => {}
                _ => {
                    self.failure = Some(failure_at_code(
                        &node,
                        self.source,
                        FLOAT_CONVERSION_UNSUPPORTED,
                        "the verified float constructor requires a source string literal",
                    ));
                    return;
                }
            }
        }
        if canonical.is_some_and(is_contract_declaration) {
            self.reject(
                &node,
                "contract declarations cannot be nested inside expressions",
            );
            return;
        }
        if matches!(canonical, Some("Acc" | "Rd")) {
            if self.context == ExpressionContext::Runtime
                || self.context == ExpressionContext::UnfoldingValue
            {
                self.reject(&node, "permission expressions are illegal in this context");
                return;
            }
            let first = node.args.first();
            let valid_target = matches!(
                first,
                Some(
                    ast::Expr::Name(_)
                        | ast::Expr::Attribute(_)
                        | ast::Expr::Subscript(_)
                        | ast::Expr::Call(_)
                )
            );
            if !valid_target
                || !node.keywords.is_empty()
                || !(node.args.len() == 1 || node.args.len() == 2)
            {
                self.reject(
                    &node,
                    "permission target is not a supported location or predicate",
                );
                return;
            }
            if let Some(amount) = node.args.get(1)
                && let Err(failure) =
                    validate_expression(amount, self.bindings, self.context, self.source)
            {
                self.failure = Some(failure);
            }
            return;
        }
        if canonical == Some("Unfolding") {
            if let Err(failure) =
                validate_call_argument(&node, self.bindings, self.context, self.source)
            {
                self.failure = Some(failure);
            }
            return;
        }
        if matches!(canonical, Some("LowEvent" | "LowExit"))
            && !matches!(
                self.context,
                ExpressionContext::Precondition { .. } | ExpressionContext::LoopInvariant
            )
        {
            self.reject(
                &node,
                "LowEvent and LowExit are valid only in preconditions",
            );
            return;
        }
        if canonical == Some("MustTerminate")
            && matches!(self.context, ExpressionContext::Precondition { pure: true })
        {
            self.reject(
                &node,
                "MustTerminate cannot appear in a pure-function precondition",
            );
            return;
        }
        if canonical == Some("list_pred")
            && matches!(
                self.context,
                ExpressionContext::Postcondition { pure: true }
            )
        {
            self.reject(
                &node,
                "bare list permission predicates cannot appear in pure postconditions",
            );
            return;
        }
        if canonical == Some("Implies")
            && node.args.first().is_some_and(|antecedent| {
                contains_canonical_call(antecedent, self.bindings, "Acc")
                    || contains_canonical_call(antecedent, self.bindings, "Rd")
            })
        {
            self.reject(
                node.args.first().expect("checked above"),
                "permission assertions cannot be implication conditions",
            );
            return;
        }
        if self.context == ExpressionContext::Runtime && is_predicate_call(&node, self.bindings) {
            self.reject(
                &node,
                "predicate calls cannot be evaluated as runtime values",
            );
            return;
        }
        self.generic_visit_expr_call(node);
    }

    fn visit_expr_compare(&mut self, node: ast::ExprCompare) {
        if contains_canonical_call(&node.left, self.bindings, "Acc")
            || node
                .comparators
                .iter()
                .any(|item| contains_canonical_call(item, self.bindings, "Acc"))
        {
            self.reject(
                &node,
                "Acc is a permission assertion, not a comparable value",
            );
            return;
        }
        self.generic_visit_expr_compare(node);
    }

    fn visit_expr_unary_op(&mut self, node: ast::ExprUnaryOp) {
        if node.op == ast::UnaryOp::Not
            && (contains_canonical_call(&node.operand, self.bindings, "token")
                || contains_io_operation_call(&node.operand, self.bindings))
        {
            self.reject(
                node.operand.as_ref(),
                "IO permissions and operations cannot be negated in contracts",
            );
            return;
        }
        self.generic_visit_expr_unary_op(node);
    }
}

fn io_exists_lambda<'a>(
    call: &'a ast::ExprCall,
    bindings: &Bindings,
) -> Option<&'a ast::ExprLambda> {
    let ast::Expr::Call(factory) = call.func.as_ref() else {
        return None;
    };
    if !call_name(factory, bindings).is_some_and(|name| name.starts_with("IOExists")) {
        return None;
    }
    let [ast::Expr::Lambda(lambda)] = call.args.as_slice() else {
        return None;
    };
    Some(lambda)
}

fn validate_io_exists_lambda(
    lambda: &ast::ExprLambda,
    bindings: &Bindings,
    source: &str,
) -> Result<(), ContractPositionFailure> {
    let ast::Expr::Tuple(tuple) = lambda.body.as_ref() else {
        return Ok(());
    };
    for item in &tuple.elts {
        let ast::Expr::Call(contract) = item else {
            continue;
        };
        let context = match call_name(contract, bindings) {
            Some("Requires") => ExpressionContext::Precondition { pure: false },
            Some("Ensures") => ExpressionContext::Postcondition { pure: false },
            _ => continue,
        };
        validate_call_argument(contract, bindings, context, source)?;
    }
    Ok(())
}

fn direct_contract_call<'a>(
    expression: &'a ast::Expr,
    bindings: &Bindings,
) -> Option<&'a ast::ExprCall> {
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    call_name(call, bindings).map(|_| call)
}

fn call_name<'a>(call: &ast::ExprCall, bindings: &'a Bindings) -> Option<&'a str> {
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return None;
    };
    canonical_name(bindings, name.id.as_str())
}

fn canonical_name<'a>(bindings: &'a Bindings, name: &str) -> Option<&'a str> {
    bindings.canonical.get(name).map(String::as_str)
}

fn is_contract_declaration(name: &str) -> bool {
    matches!(
        name,
        "Requires" | "Ensures" | "Exsures" | "Invariant" | "Assert" | "Decreases"
    )
}

fn is_predicate_call(call: &ast::ExprCall, bindings: &Bindings) -> bool {
    match call.func.as_ref() {
        ast::Expr::Name(name) => bindings.predicates.contains(name.id.as_str()),
        ast::Expr::Attribute(attribute) => bindings.predicates.contains(attribute.attr.as_str()),
        _ => false,
    }
}

struct CanonicalCallCollector<'a> {
    bindings: Option<&'a Bindings>,
    canonical: &'a str,
    found: bool,
}

impl Visitor for CanonicalCallCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if self
            .bindings
            .is_some_and(|bindings| call_name(&node, bindings) == Some(self.canonical))
        {
            self.found = true;
            return;
        }
        self.generic_visit_expr_call(node);
    }
}

fn contains_canonical_call(expression: &ast::Expr, bindings: &Bindings, canonical: &str) -> bool {
    let mut collector = CanonicalCallCollector {
        bindings: Some(bindings),
        canonical,
        found: false,
    };
    collector.visit_expr(expression.clone());
    collector.found
}

fn contains_canonical_call_in_statement(
    statement: &ast::Stmt,
    bindings: &Bindings,
    canonical: &str,
) -> bool {
    let mut collector = CanonicalCallCollector {
        bindings: Some(bindings),
        canonical,
        found: false,
    };
    collector.visit_stmt(statement.clone());
    collector.found
}

fn contains_canonical_call_in_call(
    call: &ast::ExprCall,
    bindings: &Bindings,
    canonical: &str,
) -> bool {
    call.args
        .iter()
        .any(|argument| contains_canonical_call(argument, bindings, canonical))
        || call
            .keywords
            .iter()
            .any(|keyword| contains_canonical_call(&keyword.value, bindings, canonical))
}

struct FirstCanonicalCallArgumentCollector<'a> {
    bindings: &'a Bindings,
    canonical: &'a str,
    argument: Option<ast::Expr>,
}

impl Visitor for FirstCanonicalCallArgumentCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if self.argument.is_some() {
            return;
        }
        if call_name(&node, self.bindings) == Some(self.canonical) {
            self.argument = node.args.first().cloned();
            return;
        }
        self.generic_visit_expr_call(node);
    }
}

fn first_canonical_call_argument(
    call: &ast::ExprCall,
    bindings: &Bindings,
    canonical: &str,
) -> Option<ast::Expr> {
    let mut collector = FirstCanonicalCallArgumentCollector {
        bindings,
        canonical,
        argument: None,
    };
    for argument in &call.args {
        collector.visit_expr(argument.clone());
        if collector.argument.is_some() {
            return collector.argument;
        }
    }
    for keyword in &call.keywords {
        collector.visit_expr(keyword.value.clone());
        if collector.argument.is_some() {
            return collector.argument;
        }
    }
    None
}

struct IoOperationCollector<'a> {
    bindings: &'a Bindings,
    found: bool,
}

impl Visitor for IoOperationCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if matches!(node.func.as_ref(), ast::Expr::Name(name)
            if self.bindings.io_operations.contains(name.id.as_str()))
        {
            self.found = true;
            return;
        }
        self.generic_visit_expr_call(node);
    }
}

fn contains_io_operation_call(expression: &ast::Expr, bindings: &Bindings) -> bool {
    let mut collector = IoOperationCollector {
        bindings,
        found: false,
    };
    collector.visit_expr(expression.clone());
    collector.found
}

fn invalid<T>(
    ranged: &impl Ranged,
    source: &str,
    message: impl Into<String>,
) -> Result<T, ContractPositionFailure> {
    Err(failure_at(ranged, source, message))
}

fn invalid_code<T>(
    ranged: &impl Ranged,
    source: &str,
    code: &'static str,
    message: impl Into<String>,
) -> Result<T, ContractPositionFailure> {
    Err(failure_at_code(ranged, source, code, message))
}

fn failure_at(
    ranged: &impl Ranged,
    source: &str,
    message: impl Into<String>,
) -> ContractPositionFailure {
    failure_at_code(ranged, source, INVALID_CONTRACT_POSITION, message)
}

fn failure_at_code(
    ranged: &impl Ranged,
    source: &str,
    code: &'static str,
    message: impl Into<String>,
) -> ContractPositionFailure {
    let byte_offset = u32::from(ranged.range().start());
    let prefix = &source[..usize::try_from(byte_offset)
        .unwrap_or(source.len())
        .min(source.len())];
    ContractPositionFailure {
        code,
        message: message.into(),
        byte_offset,
        line: u32::try_from(prefix.bytes().filter(|byte| *byte == b'\n').count() + 1)
            .unwrap_or(u32::MAX),
        column: u32::try_from(
            prefix
                .rsplit_once('\n')
                .map_or(prefix.len(), |(_, suffix)| suffix.len())
                + 1,
        )
        .unwrap_or(u32::MAX),
    }
}

#[cfg(test)]
mod dead_code_tests {
    use std::{fs, path::Path};

    use super::{TYPE_ERROR_DEAD_CODE, validate_contract_positions};

    #[test]
    fn ordinary_unreachable_statements_are_rejected_at_the_first_dead_statement() {
        for (source, expected_line) in [
            (
                "def direct() -> None:\n    raise Exception()\n    value = 1\n",
                3,
            ),
            (
                "def in_try() -> None:\n    try:\n        raise Exception()\n        value = 1\n    except Exception:\n        pass\n",
                4,
            ),
            (
                "def in_handler() -> None:\n    try:\n        pass\n    except Exception:\n        return\n        value = 1\n",
                6,
            ),
            (
                "def in_finally() -> None:\n    try:\n        pass\n    finally:\n        raise Exception()\n        value = 1\n",
                6,
            ),
        ] {
            let failure = validate_contract_positions(source, "fixture.py").unwrap_err();
            assert_eq!(failure.code, TYPE_ERROR_DEAD_CODE, "{source}");
            assert_eq!(failure.line, expected_line, "{source}");
        }
    }

    #[test]
    fn conditional_exit_does_not_make_following_code_unreachable() {
        let source = "def conditional(flag: bool) -> int:\n    if flag:\n        return 1\n    value = 2\n    return value\n";
        validate_contract_positions(source, "fixture.py").unwrap();
    }

    #[test]
    fn ordinary_literal_return_does_not_invent_a_dead_code_type_error() {
        let source = "def ordinary() -> int:\n    return 1\n    return 2\n";
        validate_contract_positions(source, "fixture.py").unwrap();
    }

    #[test]
    fn pinned_sif_literal_return_is_not_a_source_wellformedness_failure() {
        let fixture = "tests/sif-true/verification/test_return.py";
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join(".upstream/nagini")
            .join(fixture);
        let source = fs::read_to_string(path).unwrap();

        validate_contract_positions(&source, fixture).unwrap();
    }

    #[test]
    fn ordinary_typed_return_still_requires_the_missing_type_map_entry() {
        let source = "def ordinary(value: int) -> int:\n    return 1\n    return value\n";
        let failure = validate_contract_positions(source, "fixture.py").unwrap_err();
        assert_eq!(failure.code, TYPE_ERROR_DEAD_CODE);
        assert_eq!(failure.line, 3);
    }

    #[test]
    fn io_operation_duplicate_return_still_requires_missing_type_information() {
        let source = "from nagini_contracts.contracts import Result\nfrom nagini_contracts.io_contracts import IOOperation, Place\n\n@IOOperation\ndef io_relation(t_pre: Place, t_post: Place = Result()) -> bool:\n    return True\n    return False\n";
        let failure = validate_contract_positions(source, "fixture.py").unwrap_err();
        assert_eq!(failure.code, TYPE_ERROR_DEAD_CODE);
        assert_eq!(failure.line, 7);
    }
}

#[cfg(test)]
mod float_literal_tests {
    use super::{INVALID_FLOAT_VALUE, validate_contract_positions};

    #[test]
    fn certainly_invalid_builtin_literal_has_a_located_typed_failure() {
        let source = "def run() -> None:\n    value = float('asdasd')\n";
        let failure = validate_contract_positions(source, "fixture.py").unwrap_err();
        assert_eq!(failure.code, INVALID_FLOAT_VALUE);
        assert_eq!(failure.line, 2);
        assert_eq!(failure.column, 13);
    }

    #[test]
    fn valid_unknown_and_shadowed_literals_are_not_reclassified_as_invalid() {
        for source in [
            "def run() -> None:\n    value = float('1.25e-3')\n",
            "def run() -> None:\n    value = float('-Infinity')\n",
            "def run() -> None:\n    value = float('NaN')\n",
            "def run() -> None:\n    value = float('١٢٣')\n",
            "def run(float: object) -> None:\n    value = float('asdasd')\n",
            "float = lambda value: value\ndef run() -> None:\n    value = float('asdasd')\n",
        ] {
            let result = validate_contract_positions(source, "fixture.py");
            assert!(
                result
                    .as_ref()
                    .err()
                    .is_none_or(|failure| failure.code != INVALID_FLOAT_VALUE),
                "{source}\n{result:#?}"
            );
        }
    }
}

#[cfg(test)]
mod adt_product_tests {
    use std::{fs, path::Path};

    use super::{MULTIPLE_INHERITANCE_UNSUPPORTED, validate_contract_positions};

    #[test]
    fn canonical_adt_products_do_not_count_the_named_tuple_descriptor_as_a_runtime_mixin() {
        let source = "from nagini_contracts.adt import ADT\nfrom typing import NamedTuple\nclass Tree(ADT):\n    pass\nclass Leaf(Tree, NamedTuple('Leaf', [('value', int)])):\n    pass\n";
        validate_contract_positions(source, "adt.py").unwrap();
    }

    #[test]
    fn ordinary_multiple_inheritance_remains_rejected() {
        let source =
            "class Left:\n    pass\nclass Right:\n    pass\nclass Both(Left, Right):\n    pass\n";
        let failure = validate_contract_positions(source, "ordinary_mi.py").unwrap_err();
        assert_eq!(failure.code, MULTIPLE_INHERITANCE_UNSUPPORTED);
    }

    #[test]
    fn pinned_sif_adt_products_reach_semantic_analysis() {
        let fixture = "tests/sif-prob/verification/examples/no_obligations/secc-cddc.py";
        let source = fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join(".upstream/nagini")
                .join(fixture),
        )
        .unwrap();
        validate_contract_positions(&source, fixture).unwrap();
    }
}

#[cfg(test)]
mod nominal_provenance_tests {
    use std::collections::{BTreeMap, BTreeSet};

    use rustpython_parser::{Parse, ast};

    use super::*;

    fn provenance(source: &str, target: &str) -> BTreeMap<String, NominalProvenance> {
        let suite = ast::Suite::parse(source, "nominal_provenance.py").unwrap();
        let ambiguous = module_rebound_names(&suite);
        let mut bindings = Bindings::default();
        bindings
            .canonical
            .insert("classmethod".to_owned(), "classmethod".to_owned());
        bindings
            .canonical
            .insert("staticmethod".to_owned(), "staticmethod".to_owned());
        for statement in &suite {
            if let ast::Stmt::ImportFrom(import) = statement
                && (bind_contract_import(import, &ambiguous, &mut bindings)
                    || bind_typing_import(import, &ambiguous, &mut bindings))
            {
                continue;
            }
            match statement {
                ast::Stmt::ClassDef(class) => {
                    let declaration = collect_class_declaration(class, &bindings);
                    bindings.classes.insert(class.name.to_string(), declaration);
                    bindings.active_class_values.insert(class.name.to_string());
                }
                ast::Stmt::FunctionDef(function) if function.name.as_str() == target => {
                    return bindings_without_function_locals(function, &bindings, None)
                        .nominal_values;
                }
                ast::Stmt::FunctionDef(function) => {
                    bindings.active_class_values.remove(function.name.as_str());
                    bindings.classes.remove(function.name.as_str());
                }
                ast::Stmt::Assign(assignment) => {
                    for target in &assignment.targets {
                        remove_target_binding(target, &mut bindings);
                    }
                }
                ast::Stmt::AnnAssign(assignment) => {
                    remove_target_binding(&assignment.target, &mut bindings);
                }
                ast::Stmt::Import(import) => {
                    for alias in &import.names {
                        let local = alias.asname.as_ref().map_or_else(
                            || alias.name.as_str().split('.').next().unwrap_or_default(),
                            |name| name.as_str(),
                        );
                        remove_name_binding(local, &mut bindings);
                    }
                }
                ast::Stmt::ImportFrom(import) => {
                    for alias in &import.names {
                        if alias.name.as_str() != "*" {
                            remove_name_binding(
                                alias.asname.as_ref().unwrap_or(&alias.name).as_str(),
                                &mut bindings,
                            );
                        }
                    }
                }
                _ => {}
            }
        }
        panic!("function {target:?} was not found")
    }

    fn names(items: &[&str]) -> BTreeSet<String> {
        items.iter().map(|item| (*item).to_owned()).collect()
    }

    #[test]
    fn constructors_assignments_annotations_and_subclasses_keep_distinct_provenance() {
        let values = provenance(
            "class Base:\n    pass\nclass Child(Base):\n    pass\ndef use(parameter: Base) -> None:\n    made = Child()\n    declared: Base = Child()\n    alias = made\n",
            "use",
        );
        assert_eq!(
            values.get("parameter"),
            Some(&NominalProvenance::UpperBound(names(&["Base"])))
        );
        assert_eq!(
            values.get("made"),
            Some(&NominalProvenance::Exact(names(&["Child"])))
        );
        assert_eq!(values.get("declared"), values.get("made"));
        assert_eq!(values.get("alias"), values.get("made"));
    }

    #[test]
    fn verified_dynamic_factory_preserves_the_invoked_subclass_exactly() {
        let values = provenance(
            "class Base:\n    @classmethod\n    def make(cls) -> 'Base':\n        value = cls()\n        return value\nclass Child(Base):\n    pass\ndef use() -> None:\n    made = Child.make()\n",
            "use",
        );
        assert_eq!(
            values.get("made"),
            Some(&NominalProvenance::Exact(names(&["Child"])))
        );
    }

    #[test]
    fn conditional_expressions_and_closed_if_branches_join_finite_exact_classes() {
        let values = provenance(
            "class Left:\n    pass\nclass Right:\n    pass\ndef use(flag: bool) -> None:\n    expression = Left() if flag else Right()\n    if flag:\n        statement = Left()\n    else:\n        statement = Right()\n",
            "use",
        );
        let expected = NominalProvenance::Exact(names(&["Left", "Right"]));
        assert_eq!(values.get("expression"), Some(&expected));
        assert_eq!(values.get("statement"), Some(&expected));
    }

    #[test]
    fn union_annotations_are_upper_bounds_and_never_exact_runtime_sets() {
        let values = provenance(
            "from typing import Union\nclass Left:\n    pass\nclass Right:\n    pass\ndef use(value: Union[Left, Right]) -> None:\n    alias = value\n",
            "use",
        );
        let expected = NominalProvenance::UpperBound(names(&["Left", "Right"]));
        assert_eq!(values.get("value"), Some(&expected));
        assert_eq!(values.get("alias"), Some(&expected));
    }

    #[test]
    fn rebound_and_function_local_shadowed_class_values_do_not_invent_exactness() {
        for source in [
            "class Item:\n    pass\nItem = lambda: object()\ndef use() -> None:\n    value = Item()\n",
            "class Item:\n    pass\ndef use(Item: object) -> None:\n    value = Item()\n",
            "class Item:\n    pass\ndef use(factory: object) -> None:\n    Item = factory\n    value = Item()\n",
        ] {
            let values = provenance(source, "use");
            assert_eq!(
                values.get("value"),
                Some(&NominalProvenance::Unknown),
                "{source}"
            );
        }
    }

    #[test]
    fn incomplete_or_value_dependent_branches_remain_unknown() {
        let values = provenance(
            "class Item:\n    pass\ndef use(flag: bool, incoming: Item) -> None:\n    expression = Item() if flag else incoming\n    if flag:\n        branch = Item()\n",
            "use",
        );
        assert_eq!(
            values.get("expression"),
            Some(&NominalProvenance::UpperBound(names(&["Item"])))
        );
        assert!(!values.contains_key("branch"));
    }
}
