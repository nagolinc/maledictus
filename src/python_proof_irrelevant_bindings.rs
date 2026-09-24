//! Source analysis for module bindings that may be ignored by a proof provider.
//!
//! A binding is eligible only when its value is a finite, closed literal container and the
//! complete provider module never observes, aliases, mutates, rebinds, or exports it.  Resolved
//! direct consumer imports are supplied by the caller so this module does not duplicate Python
//! import resolution.  The analysis deliberately retains no literal contents: an eligible
//! binding is evidence only that the binding is proof-irrelevant, never obligation authority or
//! a solver value.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_ast::{Ranged, Visitor};
use rustpython_parser::{Parse, ast};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ClosedContainerKind {
    List,
    Tuple,
    Set,
    Dictionary,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum InitializerRejection {
    NotContainer,
    Name,
    Call,
    Comprehension,
    Starred,
    DictionaryUnpack,
    DynamicExpression,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ClosedContainerDeclaration {
    pub name: String,
    pub kind: Result<ClosedContainerKind, InitializerRejection>,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BindingViolationKind {
    LexicalLoad,
    Alias,
    Mutation,
    Rebinding,
    Escape,
    DirectConsumerImport,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BindingViolation {
    pub binding: String,
    pub kind: BindingViolationKind,
    pub path: String,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ImportedBinding {
    Named(String),
    Wildcard,
}

/// A source-resolver-owned import edge from the provider module into one consumer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DirectConsumerImport {
    pub consumer_path: String,
    pub binding: ImportedBinding,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofIrrelevantBindingAnalysis {
    pub declarations: Vec<ClosedContainerDeclaration>,
    pub violations: Vec<BindingViolation>,
}

impl ProofIrrelevantBindingAnalysis {
    /// Return only bindings justified as irrelevant. Literal contents never cross this API.
    pub fn eligible_bindings(&self) -> BTreeSet<String> {
        let mut declaration_counts = BTreeMap::<&str, usize>::new();
        let mut accepted = BTreeSet::<&str>::new();
        for declaration in &self.declarations {
            *declaration_counts.entry(&declaration.name).or_default() += 1;
            if declaration.kind.is_ok() {
                accepted.insert(&declaration.name);
            }
        }
        let violated = self
            .violations
            .iter()
            .map(|violation| violation.binding.as_str())
            .collect::<BTreeSet<_>>();
        accepted
            .into_iter()
            .filter(|name| declaration_counts.get(name) == Some(&1) && !violated.contains(name))
            .map(str::to_owned)
            .collect()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofIrrelevantBindingParseFailure {
    pub path: String,
    pub message: String,
}

/// Analyze all direct module assignments without evaluating or retaining their literal contents.
pub fn analyze_proof_irrelevant_closed_container_bindings(
    source: &str,
    path: &str,
    direct_consumer_imports: &[DirectConsumerImport],
) -> Result<ProofIrrelevantBindingAnalysis, ProofIrrelevantBindingParseFailure> {
    let suite =
        ast::Suite::parse(source, path).map_err(|error| ProofIrrelevantBindingParseFailure {
            path: path.to_owned(),
            message: error.to_string(),
        })?;
    let declarations = collect_declarations(&suite, source);
    let accepted_names = declarations
        .iter()
        .filter(|declaration| declaration.kind.is_ok())
        .map(|declaration| declaration.name.clone())
        .collect::<BTreeSet<_>>();

    // Exactly one target -- the first closed declaration -- is the defining store. Every other
    // store with that spelling is a rebind, including a second closed literal declaration.
    let mut defining_stores = BTreeMap::<String, u32>::new();
    for statement in &suite {
        let Some((name, target, value)) = direct_assignment(statement) else {
            continue;
        };
        if accepted_names.contains(name)
            && closed_container_kind(value).is_ok()
            && !defining_stores.contains_key(name)
        {
            defining_stores.insert(name.to_owned(), u32::from(target.range().start()));
        }
    }

    let mut collector = UsageCollector {
        source,
        path,
        bindings: &accepted_names,
        defining_stores: &defining_stores,
        violations: BTreeSet::new(),
    };
    for statement in suite {
        collector.visit_stmt(statement);
    }
    for direct_import in direct_consumer_imports {
        match &direct_import.binding {
            ImportedBinding::Named(name) if accepted_names.contains(name) => {
                collector.violations.insert(BindingViolation {
                    binding: name.clone(),
                    kind: BindingViolationKind::DirectConsumerImport,
                    path: direct_import.consumer_path.clone(),
                    byte_offset: direct_import.byte_offset,
                    line: direct_import.line,
                    column: direct_import.column,
                });
            }
            ImportedBinding::Wildcard => {
                for name in &accepted_names {
                    collector.violations.insert(BindingViolation {
                        binding: name.clone(),
                        kind: BindingViolationKind::DirectConsumerImport,
                        path: direct_import.consumer_path.clone(),
                        byte_offset: direct_import.byte_offset,
                        line: direct_import.line,
                        column: direct_import.column,
                    });
                }
            }
            ImportedBinding::Named(_) => {}
        }
    }

    Ok(ProofIrrelevantBindingAnalysis {
        declarations,
        violations: collector.violations.into_iter().collect(),
    })
}

fn collect_declarations(suite: &[ast::Stmt], source: &str) -> Vec<ClosedContainerDeclaration> {
    suite
        .iter()
        .filter_map(|statement| {
            let (name, target, value) = direct_assignment(statement)?;
            let (byte_offset, line, column) = source_position(target, source);
            Some(ClosedContainerDeclaration {
                name: name.to_owned(),
                kind: closed_container_kind(value),
                byte_offset,
                line,
                column,
            })
        })
        .collect()
}

fn direct_assignment(statement: &ast::Stmt) -> Option<(&str, &ast::Expr, &ast::Expr)> {
    match statement {
        ast::Stmt::Assign(assignment) => {
            let [target] = assignment.targets.as_slice() else {
                return None;
            };
            let ast::Expr::Name(name) = target else {
                return None;
            };
            Some((name.id.as_str(), target, assignment.value.as_ref()))
        }
        ast::Stmt::AnnAssign(assignment) => {
            let ast::Expr::Name(name) = assignment.target.as_ref() else {
                return None;
            };
            Some((
                name.id.as_str(),
                assignment.target.as_ref(),
                assignment.value.as_deref()?,
            ))
        }
        _ => None,
    }
}

fn closed_container_kind(
    expression: &ast::Expr,
) -> Result<ClosedContainerKind, InitializerRejection> {
    match expression {
        ast::Expr::List(list) => {
            validate_closed_elements(&list.elts)?;
            Ok(ClosedContainerKind::List)
        }
        ast::Expr::Tuple(tuple) => {
            validate_closed_elements(&tuple.elts)?;
            Ok(ClosedContainerKind::Tuple)
        }
        ast::Expr::Set(set) => {
            validate_closed_elements(&set.elts)?;
            Ok(ClosedContainerKind::Set)
        }
        ast::Expr::Dict(dictionary) => {
            for key in &dictionary.keys {
                validate_closed_value(key.as_ref().ok_or(InitializerRejection::DictionaryUnpack)?)?;
            }
            validate_closed_elements(&dictionary.values)?;
            Ok(ClosedContainerKind::Dictionary)
        }
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Tuple(values) if values.iter().all(closed_constant) => {
                Ok(ClosedContainerKind::Tuple)
            }
            _ => Err(InitializerRejection::NotContainer),
        },
        expression => Err(rejection_for(expression)),
    }
}

fn validate_closed_elements(elements: &[ast::Expr]) -> Result<(), InitializerRejection> {
    for element in elements {
        validate_closed_value(element)?;
    }
    Ok(())
}

fn validate_closed_value(expression: &ast::Expr) -> Result<(), InitializerRejection> {
    match expression {
        ast::Expr::Constant(constant) if closed_constant(&constant.value) => Ok(()),
        ast::Expr::List(list) => validate_closed_elements(&list.elts),
        ast::Expr::Tuple(tuple) => validate_closed_elements(&tuple.elts),
        ast::Expr::Set(set) => validate_closed_elements(&set.elts),
        ast::Expr::Dict(dictionary) => {
            for key in &dictionary.keys {
                validate_closed_value(key.as_ref().ok_or(InitializerRejection::DictionaryUnpack)?)?;
            }
            validate_closed_elements(&dictionary.values)
        }
        ast::Expr::UnaryOp(unary)
            if matches!(unary.op, ast::UnaryOp::UAdd | ast::UnaryOp::USub)
                && matches!(
                    unary.operand.as_ref(),
                    ast::Expr::Constant(ast::ExprConstant {
                        value: ast::Constant::Int(_)
                            | ast::Constant::Float(_)
                            | ast::Constant::Complex { .. },
                        ..
                    })
                ) =>
        {
            Ok(())
        }
        expression => Err(rejection_for(expression)),
    }
}

fn closed_constant(constant: &ast::Constant) -> bool {
    match constant {
        ast::Constant::None
        | ast::Constant::Bool(_)
        | ast::Constant::Str(_)
        | ast::Constant::Bytes(_)
        | ast::Constant::Int(_)
        | ast::Constant::Float(_)
        | ast::Constant::Complex { .. }
        | ast::Constant::Ellipsis => true,
        ast::Constant::Tuple(values) => values.iter().all(closed_constant),
    }
}

fn rejection_for(expression: &ast::Expr) -> InitializerRejection {
    match expression {
        ast::Expr::Name(_) => InitializerRejection::Name,
        ast::Expr::Call(_) => InitializerRejection::Call,
        ast::Expr::ListComp(_)
        | ast::Expr::SetComp(_)
        | ast::Expr::DictComp(_)
        | ast::Expr::GeneratorExp(_) => InitializerRejection::Comprehension,
        ast::Expr::Starred(_) => InitializerRejection::Starred,
        _ => InitializerRejection::DynamicExpression,
    }
}

struct UsageCollector<'a> {
    source: &'a str,
    path: &'a str,
    bindings: &'a BTreeSet<String>,
    defining_stores: &'a BTreeMap<String, u32>,
    violations: BTreeSet<BindingViolation>,
}

impl UsageCollector<'_> {
    fn record(&mut self, binding: &str, kind: BindingViolationKind, ranged: &impl Ranged) {
        let (byte_offset, line, column) = source_position(ranged, self.source);
        self.violations.insert(BindingViolation {
            binding: binding.to_owned(),
            kind,
            path: self.path.to_owned(),
            byte_offset,
            line,
            column,
        });
    }

    fn record_loaded_bindings(&mut self, expression: &ast::Expr, kind: BindingViolationKind) {
        for (binding, range_start) in binding_loads(expression, self.bindings) {
            let marker = OffsetMarker(range_start);
            self.record(&binding, kind, &marker);
        }
    }

    fn record_rebinding_name(&mut self, name: &str, ranged: &impl Ranged) {
        if self.bindings.contains(name) {
            self.record(name, BindingViolationKind::Rebinding, ranged);
        }
    }
}

impl Visitor for UsageCollector<'_> {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        let name = node.id.as_str();
        if !self.bindings.contains(name) {
            return;
        }
        let offset = u32::from(node.range.start());
        match node.ctx {
            ast::ExprContext::Load => self.record(name, BindingViolationKind::LexicalLoad, &node),
            ast::ExprContext::Store if self.defining_stores.get(name).copied() != Some(offset) => {
                self.record(name, BindingViolationKind::Rebinding, &node);
            }
            ast::ExprContext::Del => self.record(name, BindingViolationKind::Mutation, &node),
            ast::ExprContext::Store => {}
        }
    }

    fn visit_stmt_assign(&mut self, node: ast::StmtAssign) {
        for target in &node.targets {
            if let Some(binding) = mutated_binding(target, self.bindings) {
                self.record(binding, BindingViolationKind::Mutation, target);
            }
        }
        if let ast::Expr::Name(name) = node.value.as_ref()
            && self.bindings.contains(name.id.as_str())
        {
            self.record(
                name.id.as_str(),
                BindingViolationKind::Alias,
                node.value.as_ref(),
            );
        } else {
            self.record_loaded_bindings(&node.value, BindingViolationKind::Escape);
        }
        self.generic_visit_stmt_assign(node);
    }

    fn visit_stmt_ann_assign(&mut self, node: ast::StmtAnnAssign) {
        if let Some(binding) = mutated_binding(&node.target, self.bindings) {
            self.record(
                binding,
                BindingViolationKind::Mutation,
                node.target.as_ref(),
            );
        }
        if let Some(value) = node.value.as_deref() {
            if let ast::Expr::Name(name) = value
                && self.bindings.contains(name.id.as_str())
            {
                self.record(name.id.as_str(), BindingViolationKind::Alias, value);
            } else {
                self.record_loaded_bindings(value, BindingViolationKind::Escape);
            }
        }
        self.generic_visit_stmt_ann_assign(node);
    }

    fn visit_stmt_aug_assign(&mut self, node: ast::StmtAugAssign) {
        if let Some(binding) = root_binding(&node.target, self.bindings) {
            self.record(
                binding,
                BindingViolationKind::Mutation,
                node.target.as_ref(),
            );
        }
        self.generic_visit_stmt_aug_assign(node);
    }

    fn visit_stmt_delete(&mut self, node: ast::StmtDelete) {
        for target in &node.targets {
            if let Some(binding) = root_binding(target, self.bindings) {
                self.record(binding, BindingViolationKind::Mutation, target);
            }
        }
        self.generic_visit_stmt_delete(node);
    }

    fn visit_stmt_return(&mut self, node: ast::StmtReturn) {
        if let Some(value) = node.value.as_deref() {
            self.record_loaded_bindings(value, BindingViolationKind::Escape);
        }
        self.generic_visit_stmt_return(node);
    }

    fn visit_expr_yield(&mut self, node: ast::ExprYield) {
        if let Some(value) = node.value.as_deref() {
            self.record_loaded_bindings(value, BindingViolationKind::Escape);
        }
        self.generic_visit_expr_yield(node);
    }

    fn visit_expr_yield_from(&mut self, node: ast::ExprYieldFrom) {
        self.record_loaded_bindings(&node.value, BindingViolationKind::Escape);
        self.generic_visit_expr_yield_from(node);
    }

    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if let ast::Expr::Attribute(attribute) = node.func.as_ref()
            && mutating_method(attribute.attr.as_str())
            && let Some(binding) = root_binding(&attribute.value, self.bindings)
        {
            self.record(
                binding,
                BindingViolationKind::Mutation,
                attribute.value.as_ref(),
            );
        } else {
            self.record_loaded_bindings(&node.func, BindingViolationKind::Escape);
        }
        for argument in &node.args {
            self.record_loaded_bindings(argument, BindingViolationKind::Escape);
        }
        for keyword in &node.keywords {
            self.record_loaded_bindings(&keyword.value, BindingViolationKind::Escape);
        }
        self.generic_visit_expr_call(node);
    }

    fn visit_stmt_function_def(&mut self, node: ast::StmtFunctionDef) {
        self.record_rebinding_name(node.name.as_str(), &node);
        self.generic_visit_stmt_function_def(node);
    }

    fn visit_stmt_async_function_def(&mut self, node: ast::StmtAsyncFunctionDef) {
        self.record_rebinding_name(node.name.as_str(), &node);
        self.generic_visit_stmt_async_function_def(node);
    }

    fn visit_stmt_class_def(&mut self, node: ast::StmtClassDef) {
        self.record_rebinding_name(node.name.as_str(), &node);
        self.generic_visit_stmt_class_def(node);
    }

    fn visit_stmt_import(&mut self, node: ast::StmtImport) {
        for alias in &node.names {
            let local = alias.asname.as_ref().map_or_else(
                || alias.name.as_str().split('.').next().unwrap_or_default(),
                |name| name.as_str(),
            );
            self.record_rebinding_name(local, &node);
        }
        self.generic_visit_stmt_import(node);
    }

    fn visit_stmt_import_from(&mut self, node: ast::StmtImportFrom) {
        for alias in &node.names {
            if alias.name.as_str() != "*" {
                self.record_rebinding_name(
                    alias.asname.as_ref().unwrap_or(&alias.name).as_str(),
                    &node,
                );
            }
        }
        self.generic_visit_stmt_import_from(node);
    }

    fn visit_stmt_match(&mut self, node: ast::StmtMatch) {
        for case in &node.cases {
            let mut names = BTreeSet::new();
            collect_pattern_bindings(&case.pattern, &mut names);
            for name in names {
                self.record_rebinding_name(&name, &case.pattern);
            }
        }
        self.generic_visit_stmt_match(node);
    }
}

#[derive(Clone, Copy)]
struct OffsetMarker(u32);

impl Ranged for OffsetMarker {
    fn range(&self) -> rustpython_ast::text_size::TextRange {
        let offset = rustpython_ast::text_size::TextSize::from(self.0);
        rustpython_ast::text_size::TextRange::empty(offset)
    }
}

struct BindingLoadCollector<'a> {
    bindings: &'a BTreeSet<String>,
    loads: BTreeSet<(String, u32)>,
}

impl Visitor for BindingLoadCollector<'_> {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if node.ctx == ast::ExprContext::Load && self.bindings.contains(node.id.as_str()) {
            self.loads
                .insert((node.id.to_string(), u32::from(node.range.start())));
        }
    }
}

fn binding_loads(expression: &ast::Expr, bindings: &BTreeSet<String>) -> BTreeSet<(String, u32)> {
    let mut collector = BindingLoadCollector {
        bindings,
        loads: BTreeSet::new(),
    };
    collector.visit_expr(expression.clone());
    collector.loads
}

fn root_binding<'a>(expression: &'a ast::Expr, bindings: &'a BTreeSet<String>) -> Option<&'a str> {
    match expression {
        ast::Expr::Name(name) if bindings.contains(name.id.as_str()) => Some(name.id.as_str()),
        ast::Expr::Attribute(attribute) => root_binding(&attribute.value, bindings),
        ast::Expr::Subscript(subscript) => root_binding(&subscript.value, bindings),
        _ => None,
    }
}

fn mutated_binding<'a>(target: &'a ast::Expr, bindings: &'a BTreeSet<String>) -> Option<&'a str> {
    match target {
        ast::Expr::Attribute(_) | ast::Expr::Subscript(_) => root_binding(target, bindings),
        _ => None,
    }
}

fn mutating_method(name: &str) -> bool {
    matches!(
        name,
        "__delitem__"
            | "__setitem__"
            | "add"
            | "append"
            | "clear"
            | "difference_update"
            | "discard"
            | "extend"
            | "insert"
            | "intersection_update"
            | "pop"
            | "popitem"
            | "remove"
            | "reverse"
            | "setdefault"
            | "sort"
            | "symmetric_difference_update"
            | "update"
    )
}

fn collect_pattern_bindings(pattern: &ast::Pattern, names: &mut BTreeSet<String>) {
    match pattern {
        ast::Pattern::MatchAs(as_pattern) => {
            if let Some(name) = &as_pattern.name {
                names.insert(name.to_string());
            }
            if let Some(inner) = as_pattern.pattern.as_deref() {
                collect_pattern_bindings(inner, names);
            }
        }
        ast::Pattern::MatchOr(or_pattern) => {
            for alternative in &or_pattern.patterns {
                collect_pattern_bindings(alternative, names);
            }
        }
        ast::Pattern::MatchSequence(sequence) => {
            for element in &sequence.patterns {
                collect_pattern_bindings(element, names);
            }
        }
        ast::Pattern::MatchMapping(mapping) => {
            for value in &mapping.patterns {
                collect_pattern_bindings(value, names);
            }
            if let Some(name) = &mapping.rest {
                names.insert(name.to_string());
            }
        }
        ast::Pattern::MatchClass(class_pattern) => {
            for element in class_pattern
                .patterns
                .iter()
                .chain(class_pattern.kwd_patterns.iter())
            {
                collect_pattern_bindings(element, names);
            }
        }
        ast::Pattern::MatchStar(star) => {
            if let Some(name) = &star.name {
                names.insert(name.to_string());
            }
        }
        ast::Pattern::MatchValue(_) | ast::Pattern::MatchSingleton(_) => {}
    }
}

fn source_position(ranged: &impl Ranged, source: &str) -> (u32, u32, u32) {
    let byte_offset = u32::from(ranged.range().start());
    let prefix = &source[..usize::try_from(byte_offset)
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
    (byte_offset, line, column)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn analyze(source: &str) -> ProofIrrelevantBindingAnalysis {
        analyze_proof_irrelevant_closed_container_bindings(source, "provider.py", &[]).unwrap()
    }

    fn kinds_for(
        analysis: &ProofIrrelevantBindingAnalysis,
        binding: &str,
    ) -> BTreeSet<BindingViolationKind> {
        analysis
            .violations
            .iter()
            .filter(|violation| violation.binding == binding)
            .map(|violation| violation.kind)
            .collect()
    }

    #[test]
    fn recursively_closed_literal_containers_are_eligible_without_exposing_contents() {
        let analysis = analyze(
            "VALUES = [None, True, -2, +3.5, 1j, 'text', b'bytes', ..., (1, {2, 3}), {'k': [4]}]\nEMPTY: object = {}\n",
        );
        assert_eq!(
            analysis.eligible_bindings(),
            BTreeSet::from(["EMPTY".to_owned(), "VALUES".to_owned()])
        );
        assert_eq!(analysis.declarations[0].kind, Ok(ClosedContainerKind::List));
        assert_eq!(
            analysis.declarations[1].kind,
            Ok(ClosedContainerKind::Dictionary)
        );
    }

    #[test]
    fn dynamic_names_calls_comprehensions_stars_unpacks_and_expressions_are_rejected() {
        let analysis = analyze(
            "NAME = [other]\nCALL = [make()]\nCOMP = [item for item in source]\nSTAR = [*source]\nUNPACK = {**mapping}\nDYNAMIC = [1 + 2]\nSCALAR = 1\n",
        );
        let rejected = analysis
            .declarations
            .iter()
            .map(|declaration| (declaration.name.as_str(), declaration.kind))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(rejected["NAME"], Err(InitializerRejection::Name));
        assert_eq!(rejected["CALL"], Err(InitializerRejection::Call));
        assert_eq!(rejected["COMP"], Err(InitializerRejection::Comprehension));
        assert_eq!(rejected["STAR"], Err(InitializerRejection::Starred));
        assert_eq!(
            rejected["UNPACK"],
            Err(InitializerRejection::DictionaryUnpack)
        );
        assert_eq!(
            rejected["DYNAMIC"],
            Err(InitializerRejection::DynamicExpression)
        );
        assert_eq!(rejected["SCALAR"], Err(InitializerRejection::NotContainer));
        assert!(analysis.eligible_bindings().is_empty());
    }

    #[test]
    fn loads_aliases_mutations_rebindings_and_escapes_each_invalidate_the_binding() {
        let analysis = analyze(
            "READ = [1]\nobserved = READ[0]\nALIAS = [2]\nother = ALIAS\nMUTATED = [3]\nMUTATED.append(4)\nREBOUND = [5]\nREBOUND = [6]\nESCAPED = [7]\ndef expose() -> object:\n    return ESCAPED\n",
        );
        assert!(kinds_for(&analysis, "READ").contains(&BindingViolationKind::LexicalLoad));
        assert!(kinds_for(&analysis, "READ").contains(&BindingViolationKind::Escape));
        assert!(kinds_for(&analysis, "ALIAS").contains(&BindingViolationKind::Alias));
        assert!(kinds_for(&analysis, "MUTATED").contains(&BindingViolationKind::Mutation));
        assert!(kinds_for(&analysis, "REBOUND").contains(&BindingViolationKind::Rebinding));
        assert!(kinds_for(&analysis, "ESCAPED").contains(&BindingViolationKind::Escape));
        assert!(analysis.eligible_bindings().is_empty());
    }

    #[test]
    fn subscript_delete_walrus_and_match_capture_cannot_hide_mutation_or_rebinding() {
        let analysis = analyze(
            "SUBSCRIPT = [1]\nSUBSCRIPT[0] = 2\nDELETED = [1]\ndel DELETED[0]\nWALRUS = [1]\nif (WALRUS := [2]):\n    pass\nCAPTURE = [1]\nmatch 1:\n    case CAPTURE:\n        pass\n",
        );
        assert!(kinds_for(&analysis, "SUBSCRIPT").contains(&BindingViolationKind::Mutation));
        assert!(kinds_for(&analysis, "DELETED").contains(&BindingViolationKind::Mutation));
        assert!(kinds_for(&analysis, "WALRUS").contains(&BindingViolationKind::Rebinding));
        assert!(kinds_for(&analysis, "CAPTURE").contains(&BindingViolationKind::Rebinding));
    }

    #[test]
    fn resolved_named_and_wildcard_consumer_imports_invalidate_provider_bindings() {
        let imports = [
            DirectConsumerImport {
                consumer_path: "named_consumer.py".to_owned(),
                binding: ImportedBinding::Named("NAMED".to_owned()),
                byte_offset: 7,
                line: 2,
                column: 3,
            },
            DirectConsumerImport {
                consumer_path: "wildcard_consumer.py".to_owned(),
                binding: ImportedBinding::Wildcard,
                byte_offset: 11,
                line: 4,
                column: 1,
            },
        ];
        let analysis = analyze_proof_irrelevant_closed_container_bindings(
            "NAMED = [1]\nOTHER = {'x': 2}\n",
            "provider.py",
            &imports,
        )
        .unwrap();
        for binding in ["NAMED", "OTHER"] {
            assert!(
                kinds_for(&analysis, binding).contains(&BindingViolationKind::DirectConsumerImport)
            );
        }
        assert!(analysis.eligible_bindings().is_empty());
    }

    #[test]
    fn duplicate_closed_declarations_are_not_mistaken_for_one_inert_binding() {
        let analysis = analyze("VALUES = [1]\nVALUES = [2]\n");
        assert_eq!(
            analysis
                .declarations
                .iter()
                .filter(|declaration| declaration.name == "VALUES")
                .count(),
            2
        );
        assert!(kinds_for(&analysis, "VALUES").contains(&BindingViolationKind::Rebinding));
        assert!(analysis.eligible_bindings().is_empty());
    }

    #[test]
    fn parser_failures_name_the_source_instead_of_silently_producing_no_bindings() {
        let error = analyze_proof_irrelevant_closed_container_bindings(
            "BROKEN = [",
            "broken_provider.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(error.path, "broken_provider.py");
        assert!(!error.message.is_empty());
    }
}
