//! Closed source rule for Python name-mangled instance fields.
//!
//! This pass does not guess receiver types. It reports an access only when final source bindings,
//! an explicit annotation, or one unreassigned direct source constructor proves the receiver's
//! class and the closed class hierarchy identifies the field's declaring class.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_ast::{Ranged, Visitor};
use rustpython_parser::ast;

pub(crate) const PRIVATE_FIELD_ACCESS: &str = "invalid.program:private.field.access";

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PrivateFieldFailure {
    pub message: String,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

#[derive(Default)]
struct SourceClass {
    direct_base: Option<String>,
    private_fields: BTreeSet<String>,
}

pub(crate) fn validate_private_field_access(
    suite: &[ast::Stmt],
    source: &str,
) -> Result<(), PrivateFieldFailure> {
    let definitions = final_source_classes(suite);
    if definitions.is_empty() {
        return Ok(());
    }
    let class_names = definitions.keys().cloned().collect::<BTreeSet<_>>();
    let mut classes = BTreeMap::new();
    for (name, definition) in &definitions {
        let direct_base = match definition.bases.as_slice() {
            [ast::Expr::Name(base)] if class_names.contains(base.id.as_str()) => {
                Some(base.id.to_string())
            }
            _ => None,
        };
        let mut private_fields = BTreeSet::new();
        for function in final_source_methods(definition).into_values() {
            if method_is_static_or_class(function) {
                continue;
            }
            let Some(receiver) = first_parameter_name(&function.args) else {
                continue;
            };
            let mut collector = PrivateFieldDeclarationCollector {
                receiver,
                fields: &mut private_fields,
            };
            for statement in &function.body {
                collector.visit_stmt(statement.clone());
            }
        }
        classes.insert(
            name.clone(),
            SourceClass {
                direct_base,
                private_fields,
            },
        );
    }

    let mut failure = None;
    for function in final_source_functions(suite).into_values() {
        inspect_function_private_accesses(
            function,
            None,
            &class_names,
            &classes,
            source,
            &mut failure,
        );
    }
    for statement in suite {
        if let ast::Stmt::ClassDef(class) = statement {
            let Some(final_definition) = definitions.get(class.name.as_str()) else {
                continue;
            };
            if !std::ptr::eq(*final_definition, class) {
                continue;
            }
            for function in final_source_methods(class).into_values() {
                inspect_function_private_accesses(
                    function,
                    Some(class.name.as_str()),
                    &class_names,
                    &classes,
                    source,
                    &mut failure,
                );
            }
        }
    }
    failure.map_or(Ok(()), Err)
}

fn final_source_functions(suite: &[ast::Stmt]) -> BTreeMap<String, &ast::StmtFunctionDef> {
    let mut bindings: BTreeMap<String, Option<&ast::StmtFunctionDef>> = BTreeMap::new();
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                bindings.insert(function.name.to_string(), Some(function));
            }
            ast::Stmt::ClassDef(class) => {
                bindings.insert(class.name.to_string(), None);
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    clear_target_bindings(target, &mut bindings);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                clear_target_bindings(&assignment.target, &mut bindings);
            }
            ast::Stmt::Import(import) => {
                for alias in &import.names {
                    let local = alias.asname.as_ref().map_or_else(
                        || alias.name.split('.').next().unwrap_or_default(),
                        |name| name.as_str(),
                    );
                    bindings.insert(local.to_owned(), None);
                }
            }
            ast::Stmt::ImportFrom(import) => {
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        for binding in bindings.values_mut() {
                            *binding = None;
                        }
                    } else {
                        bindings.insert(
                            alias.asname.as_ref().unwrap_or(&alias.name).to_string(),
                            None,
                        );
                    }
                }
            }
            _ => {}
        }
    }
    bindings
        .into_iter()
        .filter_map(|(name, definition)| definition.map(|definition| (name, definition)))
        .collect()
}

fn final_source_classes(suite: &[ast::Stmt]) -> BTreeMap<String, &ast::StmtClassDef> {
    let mut bindings: BTreeMap<String, Option<&ast::StmtClassDef>> = BTreeMap::new();
    for statement in suite {
        match statement {
            ast::Stmt::ClassDef(class) => {
                bindings.insert(class.name.to_string(), Some(class));
            }
            ast::Stmt::FunctionDef(function) => {
                bindings.insert(function.name.to_string(), None);
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    clear_target_bindings(target, &mut bindings);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                clear_target_bindings(&assignment.target, &mut bindings);
            }
            ast::Stmt::Import(import) => {
                for alias in &import.names {
                    let local = alias.asname.as_ref().map_or_else(
                        || alias.name.split('.').next().unwrap_or_default(),
                        |name| name.as_str(),
                    );
                    bindings.insert(local.to_owned(), None);
                }
            }
            ast::Stmt::ImportFrom(import) => {
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        for binding in bindings.values_mut() {
                            *binding = None;
                        }
                    } else {
                        bindings.insert(
                            alias.asname.as_ref().unwrap_or(&alias.name).to_string(),
                            None,
                        );
                    }
                }
            }
            _ => {}
        }
    }
    bindings
        .into_iter()
        .filter_map(|(name, definition)| definition.map(|definition| (name, definition)))
        .collect()
}

fn final_source_methods(class: &ast::StmtClassDef) -> BTreeMap<String, &ast::StmtFunctionDef> {
    let mut bindings: BTreeMap<String, Option<&ast::StmtFunctionDef>> = BTreeMap::new();
    for statement in &class.body {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                bindings.insert(function.name.to_string(), Some(function));
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    clear_target_bindings(target, &mut bindings);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                clear_target_bindings(&assignment.target, &mut bindings);
            }
            _ => {}
        }
    }
    bindings
        .into_iter()
        .filter_map(|(name, definition)| definition.map(|definition| (name, definition)))
        .collect()
}

fn clear_target_bindings<T>(target: &ast::Expr, bindings: &mut BTreeMap<String, Option<T>>) {
    match target {
        ast::Expr::Name(name) => {
            bindings.insert(name.id.to_string(), None);
        }
        ast::Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                clear_target_bindings(element, bindings);
            }
        }
        _ => {}
    }
}

fn first_parameter_name(arguments: &ast::Arguments) -> Option<&str> {
    arguments
        .posonlyargs
        .first()
        .or_else(|| arguments.args.first())
        .map(|argument| argument.def.arg.as_str())
}

fn method_is_static_or_class(function: &ast::StmtFunctionDef) -> bool {
    function.decorator_list.iter().any(|decorator| {
        matches!(decorator, ast::Expr::Name(name)
            if matches!(name.id.as_str(), "staticmethod" | "classmethod"))
    })
}

fn is_private_field(name: &str) -> bool {
    name.starts_with("__") && !name.ends_with("__")
}

struct PrivateFieldDeclarationCollector<'a> {
    receiver: &'a str,
    fields: &'a mut BTreeSet<String>,
}

impl Visitor for PrivateFieldDeclarationCollector<'_> {
    fn visit_expr_attribute(&mut self, node: ast::ExprAttribute) {
        if matches!(node.ctx, ast::ExprContext::Store)
            && is_private_field(node.attr.as_str())
            && matches!(node.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == self.receiver)
        {
            self.fields.insert(node.attr.to_string());
        }
        self.generic_visit_expr_attribute(node);
    }

    fn visit_stmt_function_def(&mut self, _node: ast::StmtFunctionDef) {}

    fn visit_stmt_class_def(&mut self, _node: ast::StmtClassDef) {}
}

fn inspect_function_private_accesses(
    function: &ast::StmtFunctionDef,
    lexical_class: Option<&str>,
    class_names: &BTreeSet<String>,
    classes: &BTreeMap<String, SourceClass>,
    source: &str,
    failure: &mut Option<PrivateFieldFailure>,
) {
    if failure.is_some() {
        return;
    }
    let mut bindings = FunctionTypeBindings::default();
    collect_all_parameter_names(&function.args, &mut bindings.bound_names);
    collect_annotated_parameters(&function.args, class_names, &mut bindings.types);
    if let Some(class_name) = lexical_class
        && !method_is_static_or_class(function)
        && let Some(receiver) = first_parameter_name(&function.args)
    {
        bindings
            .types
            .insert(receiver.to_owned(), class_name.to_owned());
    }
    for statement in &function.body {
        bindings.visit_stmt(statement.clone());
    }
    for (name, candidate) in bindings.constructor_candidates {
        if bindings.store_counts.get(&name) == Some(&1)
            && class_names.contains(&candidate)
            && !bindings.bound_names.contains(&candidate)
        {
            bindings.types.entry(name).or_insert(candidate);
        }
    }

    let mut collector = PrivateFieldAccessCollector {
        lexical_class,
        variable_types: &bindings.types,
        shadowed_class_names: &bindings.bound_names,
        class_names,
        classes,
        source,
        failure,
    };
    for statement in &function.body {
        collector.visit_stmt(statement.clone());
    }
}

fn collect_all_parameter_names(arguments: &ast::Arguments, names: &mut BTreeSet<String>) {
    for parameter in arguments
        .posonlyargs
        .iter()
        .chain(&arguments.args)
        .chain(&arguments.kwonlyargs)
    {
        names.insert(parameter.def.arg.to_string());
    }
    for parameter in [&arguments.vararg, &arguments.kwarg].into_iter().flatten() {
        names.insert(parameter.arg.to_string());
    }
}

fn collect_annotated_parameters(
    arguments: &ast::Arguments,
    class_names: &BTreeSet<String>,
    types: &mut BTreeMap<String, String>,
) {
    for parameter in arguments
        .posonlyargs
        .iter()
        .chain(&arguments.args)
        .chain(&arguments.kwonlyargs)
    {
        if let Some(class_name) =
            source_class_annotation(parameter.def.annotation.as_deref(), class_names)
        {
            types.insert(parameter.def.arg.to_string(), class_name);
        }
    }
    for parameter in [&arguments.vararg, &arguments.kwarg].into_iter().flatten() {
        if let Some(class_name) =
            source_class_annotation(parameter.annotation.as_deref(), class_names)
        {
            types.insert(parameter.arg.to_string(), class_name);
        }
    }
}

fn source_class_annotation(
    annotation: Option<&ast::Expr>,
    class_names: &BTreeSet<String>,
) -> Option<String> {
    let ast::Expr::Name(name) = annotation? else {
        return None;
    };
    class_names
        .contains(name.id.as_str())
        .then(|| name.id.to_string())
}

#[derive(Default)]
struct FunctionTypeBindings {
    types: BTreeMap<String, String>,
    bound_names: BTreeSet<String>,
    store_counts: BTreeMap<String, usize>,
    constructor_candidates: BTreeMap<String, String>,
}

impl Visitor for FunctionTypeBindings {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if matches!(node.ctx, ast::ExprContext::Store | ast::ExprContext::Del) {
            self.bound_names.insert(node.id.to_string());
            *self.store_counts.entry(node.id.to_string()).or_default() += 1;
        }
    }

    fn visit_stmt_assign(&mut self, node: ast::StmtAssign) {
        if let ([ast::Expr::Name(target)], ast::Expr::Call(call)) =
            (node.targets.as_slice(), node.value.as_ref())
            && let ast::Expr::Name(constructor) = call.func.as_ref()
        {
            self.constructor_candidates
                .insert(target.id.to_string(), constructor.id.to_string());
        }
        self.generic_visit_stmt_assign(node);
    }

    fn visit_stmt_ann_assign(&mut self, node: ast::StmtAnnAssign) {
        if let ast::Expr::Name(target) = node.target.as_ref()
            && let ast::Expr::Name(annotation) = node.annotation.as_ref()
        {
            self.types
                .insert(target.id.to_string(), annotation.id.to_string());
        }
        self.generic_visit_stmt_ann_assign(node);
    }

    fn visit_stmt_function_def(&mut self, _node: ast::StmtFunctionDef) {}

    fn visit_stmt_class_def(&mut self, _node: ast::StmtClassDef) {}
}

struct PrivateFieldAccessCollector<'a> {
    lexical_class: Option<&'a str>,
    variable_types: &'a BTreeMap<String, String>,
    shadowed_class_names: &'a BTreeSet<String>,
    class_names: &'a BTreeSet<String>,
    classes: &'a BTreeMap<String, SourceClass>,
    source: &'a str,
    failure: &'a mut Option<PrivateFieldFailure>,
}

impl PrivateFieldAccessCollector<'_> {
    fn receiver_class(&self, expression: &ast::Expr) -> Option<String> {
        match expression {
            ast::Expr::Name(name) => self.variable_types.get(name.id.as_str()).cloned(),
            ast::Expr::Call(call) => {
                let ast::Expr::Name(constructor) = call.func.as_ref() else {
                    return None;
                };
                (self.class_names.contains(constructor.id.as_str())
                    && !self.shadowed_class_names.contains(constructor.id.as_str()))
                .then(|| constructor.id.to_string())
            }
            _ => None,
        }
    }
}

impl Visitor for PrivateFieldAccessCollector<'_> {
    fn visit_expr_attribute(&mut self, node: ast::ExprAttribute) {
        if self.failure.is_some() {
            return;
        }
        if is_private_field(node.attr.as_str())
            && let Some(receiver_class) = self.receiver_class(&node.value)
            && let Some(declaring_class) =
                private_field_declarer(&receiver_class, node.attr.as_str(), self.classes)
            && self.lexical_class != Some(declaring_class)
        {
            *self.failure = Some(failure_at(
                &node,
                self.source,
                format!(
                    "private field {}.{} is accessed outside its declaring class",
                    declaring_class, node.attr
                ),
            ));
            return;
        }
        self.generic_visit_expr_attribute(node);
    }

    fn visit_stmt_function_def(&mut self, _node: ast::StmtFunctionDef) {}

    fn visit_stmt_class_def(&mut self, _node: ast::StmtClassDef) {}
}

fn private_field_declarer<'a>(
    receiver_class: &'a str,
    field: &str,
    classes: &'a BTreeMap<String, SourceClass>,
) -> Option<&'a str> {
    let mut current = receiver_class;
    let mut visited = BTreeSet::new();
    while visited.insert(current) {
        let class = classes.get(current)?;
        if class.private_fields.contains(field) {
            return Some(current);
        }
        current = class.direct_base.as_deref()?;
    }
    None
}

fn failure_at(
    ranged: &impl Ranged,
    source: &str,
    message: impl Into<String>,
) -> PrivateFieldFailure {
    let byte_offset = u32::from(ranged.range().start());
    let prefix = &source[..usize::try_from(byte_offset)
        .unwrap_or(source.len())
        .min(source.len())];
    PrivateFieldFailure {
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
