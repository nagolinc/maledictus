//! Source-bound well-formedness rules for Python constructs that Nagini rejects before VC
//! generation.
//!
//! These checks operate on parsed syntax and report the first prohibited construct in source
//! order. They do not inspect fixture comments or infer restrictions from identifier spelling.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_ast::{Ranged, Visitor};
use rustpython_parser::{Mode, Parse, Tok, ast, lexer::lex};

pub const CONTINUE_IN_FINALLY: &str = "invalid.program:continue.in.finally";
pub const MULTIPLE_LIST_GENERATORS: &str = "unsupported:Multiple generators in list comprehension.";
pub const MULTIPLE_DICT_GENERATORS: &str = "unsupported:Multiple generators in dict comprehension.";
pub const MULTIPLE_SET_GENERATORS: &str = "unsupported:Multiple generators in set comprehension.";
pub const MAPPING_PATTERN_UNSUPPORTED: &str = "unsupported:mapping patterns not yet supported";
pub const POSITIONAL_CLASS_PATTERN_UNSUPPORTED: &str =
    "unsupported:positional class patterns not yet supported";
pub const PARAMETERIZED_CLASS_PATTERN_UNSUPPORTED: &str =
    "unsupported:class patterns with parameters not yet supported";
pub const SLICE_ASSIGNMENT_UNSUPPORTED: &str = "unsupported:assignment to slice";
pub const MULTI_ITEM_WITH_UNSUPPORTED: &str = "unsupported:with block may only have one item";
pub const PARTIAL_TYPE: &str = "invalid.program:partial.type";
pub const GENERIC_CONSTRUCTOR_WITHOUT_TYPE: &str =
    "invalid.program:generic.constructor.without.type";
pub const IMPURE_LIST_COMPREHENSION_BODY: &str = "invalid.program:impure.list.comprehension.body";
pub const IMPURE_DISJUNCTION: &str = "invalid.program:impure.disjunction";
pub const INVALID_LET: &str = "invalid.program:invalid.let";
pub const INVALID_PREVIOUS: &str = "invalid.program:invalid.previous";
pub const INVALID_REVEAL_NO_FUNCTION: &str = "invalid.program:invalid.reveal.no.function";
pub const INVALID_REVEAL_NO_PURE_FUNCTION: &str = "invalid.program:invalid.reveal.no.pure.function";
pub const INVALID_REVEAL_NO_OPAQUE_FUNCTION: &str =
    "invalid.program:invalid.reveal.no.opaque.function";
pub const INVALID_MAY_CREATE: &str = "invalid.program:invalid.may.create";
pub const INVALID_MAY_SET: &str = "invalid.program:invalid.may.set";
pub const INVALID_ACC: &str = "invalid.program:invalid.acc";
pub const PERMISSION_TO_FINAL_VAR: &str = "invalid.program:permission.to.final.var";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LanguageWellformednessFailure {
    pub code: &'static str,
    pub message: String,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Copy)]
struct Candidate {
    code: &'static str,
    message: &'static str,
    byte_offset: u32,
    priority: u8,
}

struct LanguageRestrictionCollector<'a> {
    candidates: Vec<Candidate>,
    finally_depth: usize,
    generic_classes: BTreeSet<String>,
    impure_functions: BTreeSet<String>,
    predicate_functions: BTreeSet<String>,
    pure_functions: BTreeSet<String>,
    opaque_functions: BTreeSet<String>,
    let_functions: BTreeSet<String>,
    previous_functions: BTreeSet<String>,
    reveal_functions: BTreeSet<String>,
    may_create_functions: BTreeSet<String>,
    may_set_functions: BTreeSet<String>,
    acc_functions: BTreeSet<String>,
    contract_modules: BTreeSet<String>,
    class_fields: BTreeMap<String, ClassFieldCatalog>,
    current_class: Option<String>,
    current_method_receiver: Option<String>,
    class_function_depth: usize,
    final_module_globals: BTreeSet<String>,
    local_nominal_scopes: Vec<BTreeMap<String, String>>,
    previous_loop_targets: Vec<String>,
    function_scopes: Vec<BTreeSet<String>>,
    explicit_type_comment_lines: BTreeSet<u32>,
    source: &'a str,
}

impl<'a> LanguageRestrictionCollector<'a> {
    fn new(suite: &ast::Suite, source: &'a str) -> Self {
        let module = collect_module_semantics(suite);
        let pure_functions = module
            .functions
            .iter()
            .filter_map(|(name, pure)| (*pure).then_some(name.clone()))
            .collect();
        Self {
            candidates: Vec::new(),
            finally_depth: 0,
            generic_classes: module.generic_classes,
            impure_functions: module
                .functions
                .into_iter()
                .filter_map(|(name, pure)| (!pure).then_some(name))
                .collect(),
            predicate_functions: module.predicates,
            pure_functions,
            opaque_functions: module.opaque_functions,
            let_functions: module.let_names,
            previous_functions: module.previous_names,
            reveal_functions: module.reveal_names,
            may_create_functions: module.may_create_names,
            may_set_functions: module.may_set_names,
            acc_functions: module.acc_names,
            contract_modules: module.contract_modules,
            class_fields: module.class_fields,
            current_class: None,
            current_method_receiver: None,
            class_function_depth: 0,
            final_module_globals: collect_final_module_globals(suite),
            local_nominal_scopes: Vec::new(),
            previous_loop_targets: Vec::new(),
            function_scopes: Vec::new(),
            explicit_type_comment_lines: collect_explicit_type_comment_lines(source),
            source,
        }
    }

    fn record(
        &mut self,
        ranged: &impl Ranged,
        code: &'static str,
        message: &'static str,
        priority: u8,
    ) {
        self.candidates.push(Candidate {
            code,
            message,
            byte_offset: u32::from(ranged.range().start()),
            priority,
        });
    }

    fn visit_statements(&mut self, statements: Vec<ast::Stmt>) {
        for statement in statements {
            self.visit_stmt(statement);
        }
    }

    fn visit_function_with_fresh_context(
        &mut self,
        local_bindings: BTreeSet<String>,
        nominal_bindings: BTreeMap<String, String>,
        visit: impl FnOnce(&mut Self),
    ) {
        let enclosing_depth = self.finally_depth;
        self.finally_depth = 0;
        self.function_scopes.push(local_bindings);
        self.local_nominal_scopes.push(nominal_bindings);
        visit(self);
        self.local_nominal_scopes.pop();
        self.function_scopes.pop();
        self.finally_depth = enclosing_depth;
    }

    fn current_name_is_local(&self, name: &str) -> bool {
        self.function_scopes
            .last()
            .is_some_and(|bindings| bindings.contains(name))
    }

    fn local_nominal_class(&self, name: &str) -> Option<&str> {
        self.local_nominal_scopes
            .last()
            .and_then(|bindings| bindings.get(name))
            .map(String::as_str)
    }

    fn canonical_contract_function(
        &self,
        expression: &ast::Expr,
        direct_names: &BTreeSet<String>,
        attribute_name: &str,
    ) -> bool {
        match expression {
            ast::Expr::Name(name) => {
                direct_names.contains(name.id.as_str())
                    && !self.current_name_is_local(name.id.as_str())
            }
            ast::Expr::Attribute(attribute) if attribute.attr.as_str() == attribute_name => {
                matches!(attribute.value.as_ref(), ast::Expr::Name(module)
                    if self.contract_modules.contains(module.id.as_str())
                        && !self.current_name_is_local(module.id.as_str()))
            }
            _ => false,
        }
    }

    fn validate_may_field_call(&mut self, node: &ast::ExprCall) {
        let code = if self.canonical_contract_function(
            &node.func,
            &self.may_create_functions,
            "MayCreate",
        ) {
            INVALID_MAY_CREATE
        } else if self.canonical_contract_function(&node.func, &self.may_set_functions, "MaySet") {
            INVALID_MAY_SET
        } else {
            return;
        };
        if node.args.len() != 2 || !node.keywords.is_empty() {
            return;
        }
        let (Some(class), Some(receiver)) = (
            self.current_class.as_deref(),
            self.current_method_receiver.as_deref(),
        ) else {
            return;
        };
        if !matches!(&node.args[0], ast::Expr::Name(name) if name.id.as_str() == receiver) {
            return;
        }
        let Some(catalog) = self.class_fields.get(class) else {
            return;
        };
        let invalid = match &node.args[1] {
            ast::Expr::Constant(constant) => match &constant.value {
                ast::Constant::Str(field) => {
                    catalog.complete && !catalog.fields.contains(field.as_str())
                }
                _ => true,
            },
            _ => true,
        };
        if invalid {
            self.record(
                node,
                code,
                "MayCreate and MaySet require a literal declared field name",
                0,
            );
        }
    }

    fn validate_acc_call(&mut self, node: &ast::ExprCall) {
        if !self.canonical_contract_function(&node.func, &self.acc_functions, "Acc")
            || node.args.len() != 1
            || !node.keywords.is_empty()
        {
            return;
        }
        let target = &node.args[0];
        match target {
            ast::Expr::Name(name)
                if !self.current_name_is_local(name.id.as_str())
                    && self.final_module_globals.contains(name.id.as_str()) =>
            {
                self.record(
                    target,
                    PERMISSION_TO_FINAL_VAR,
                    "permissions cannot target a final module variable",
                    0,
                );
            }
            ast::Expr::Call(call) => {
                let ast::Expr::Attribute(attribute) = call.func.as_ref() else {
                    return;
                };
                let ast::Expr::Name(receiver) = attribute.value.as_ref() else {
                    return;
                };
                let Some(class) = self.local_nominal_class(receiver.id.as_str()) else {
                    return;
                };
                let Some(catalog) = self.class_fields.get(class) else {
                    return;
                };
                if catalog.methods.contains(attribute.attr.as_str())
                    && !catalog.predicates.contains(attribute.attr.as_str())
                {
                    self.record(
                        target,
                        INVALID_ACC,
                        "Acc call targets must be predicates",
                        0,
                    );
                }
            }
            ast::Expr::Attribute(attribute) => {
                let ast::Expr::Name(receiver) = attribute.value.as_ref() else {
                    return;
                };
                let Some(class) = self.local_nominal_class(receiver.id.as_str()) else {
                    return;
                };
                let Some(catalog) = self.class_fields.get(class) else {
                    return;
                };
                let member = attribute.attr.as_str();
                if !catalog.fields.contains(member)
                    && (catalog.properties.contains(member)
                        || (catalog.methods.contains(member)
                            && !catalog.predicates.contains(member)))
                {
                    self.record(
                        target,
                        INVALID_ACC,
                        "Acc attribute targets must be declared fields",
                        0,
                    );
                }
            }
            _ => {}
        }
    }
}

impl Visitor for LanguageRestrictionCollector<'_> {
    fn visit_stmt_class_def(&mut self, node: ast::StmtClassDef) {
        let enclosing_class = self.current_class.replace(node.name.to_string());
        let enclosing_receiver = self.current_method_receiver.take();
        let enclosing_function_depth = std::mem::take(&mut self.class_function_depth);
        self.generic_visit_stmt_class_def(node);
        self.class_function_depth = enclosing_function_depth;
        self.current_method_receiver = enclosing_receiver;
        self.current_class = enclosing_class;
    }

    fn visit_match_case(&mut self, node: ast::MatchCase) {
        // rustpython-ast 0.4's generated `generic_visit_match_case` is empty, so descend through
        // every case field explicitly. Depending on that generated no-op would silently skip
        // prohibited nested patterns and constructs in guards or case bodies.
        self.visit_pattern(node.pattern);
        if let Some(guard) = node.guard {
            self.visit_expr(*guard);
        }
        self.visit_statements(node.body);
    }

    fn visit_stmt_function_def(&mut self, node: ast::StmtFunctionDef) {
        let local_bindings = collect_function_scope_bindings(&node.args, &node.body);
        let mut nominal_bindings = collect_nominal_argument_bindings(&node.args);
        let enclosing_receiver = self.current_method_receiver.take();
        let direct_method = self.current_class.is_some() && self.class_function_depth == 0;
        self.class_function_depth = self.class_function_depth.saturating_add(1);
        self.current_method_receiver = if direct_method {
            first_parameter_name(&node.args)
        } else {
            None
        };
        if let (Some(receiver), Some(class)) = (&self.current_method_receiver, &self.current_class)
        {
            nominal_bindings.insert(receiver.clone(), class.clone());
        }
        self.visit_function_with_fresh_context(local_bindings, nominal_bindings, |collector| {
            collector.generic_visit_stmt_function_def(node);
        });
        self.class_function_depth = self.class_function_depth.saturating_sub(1);
        self.current_method_receiver = enclosing_receiver;
    }

    fn visit_stmt_async_function_def(&mut self, node: ast::StmtAsyncFunctionDef) {
        let local_bindings = collect_function_scope_bindings(&node.args, &node.body);
        let mut nominal_bindings = collect_nominal_argument_bindings(&node.args);
        let enclosing_receiver = self.current_method_receiver.take();
        let direct_method = self.current_class.is_some() && self.class_function_depth == 0;
        self.class_function_depth = self.class_function_depth.saturating_add(1);
        self.current_method_receiver = if direct_method {
            first_parameter_name(&node.args)
        } else {
            None
        };
        if let (Some(receiver), Some(class)) = (&self.current_method_receiver, &self.current_class)
        {
            nominal_bindings.insert(receiver.clone(), class.clone());
        }
        self.visit_function_with_fresh_context(local_bindings, nominal_bindings, |collector| {
            collector.generic_visit_stmt_async_function_def(node);
        });
        self.class_function_depth = self.class_function_depth.saturating_sub(1);
        self.current_method_receiver = enclosing_receiver;
    }

    fn visit_stmt_try(&mut self, node: ast::StmtTry) {
        self.visit_statements(node.body);
        for handler in node.handlers {
            self.visit_excepthandler(handler);
        }
        self.visit_statements(node.orelse);
        self.finally_depth = self.finally_depth.saturating_add(1);
        self.visit_statements(node.finalbody);
        self.finally_depth = self.finally_depth.saturating_sub(1);
    }

    fn visit_stmt_try_star(&mut self, node: ast::StmtTryStar) {
        self.visit_statements(node.body);
        for handler in node.handlers {
            self.visit_excepthandler(handler);
        }
        self.visit_statements(node.orelse);
        self.finally_depth = self.finally_depth.saturating_add(1);
        self.visit_statements(node.finalbody);
        self.finally_depth = self.finally_depth.saturating_sub(1);
    }

    fn visit_stmt_continue(&mut self, node: ast::StmtContinue) {
        if self.finally_depth > 0 {
            self.record(
                &node,
                CONTINUE_IN_FINALLY,
                "continue may not exit a finally block",
                0,
            );
        }
    }

    fn visit_stmt_for(&mut self, node: ast::StmtFor) {
        let target = previous_loop_target_name(&node.target);
        self.visit_expr(*node.target);
        self.visit_expr(*node.iter);
        if let Some(target) = target.as_ref() {
            self.previous_loop_targets.push(target.clone());
        }
        self.visit_statements(node.body);
        self.visit_statements(node.orelse);
        if target.is_some() {
            self.previous_loop_targets.pop();
        }
    }

    fn visit_stmt_assign(&mut self, node: ast::StmtAssign) {
        let line = source_line(self.source, u32::from(node.range.start()));
        if node.type_comment.is_none()
            && !self.explicit_type_comment_lines.contains(&line)
            && node.targets.iter().any(|target| {
                assignment_has_unresolved_empty_container(target, node.value.as_ref())
            })
        {
            self.record(
                node.value.as_ref(),
                PARTIAL_TYPE,
                "empty container assignment requires an explicit element type",
                0,
            );
        }
        if let Some(target) = node.targets.iter().find_map(slice_assignment_target) {
            self.record(
                target,
                SLICE_ASSIGNMENT_UNSUPPORTED,
                "assignment to a slice is unsupported",
                0,
            );
        }
        self.generic_visit_stmt_assign(node);
    }

    fn visit_stmt_expr(&mut self, node: ast::StmtExpr) {
        if !self.function_scopes.is_empty()
            && let ast::Expr::Call(call) = node.value.as_ref()
            && let ast::Expr::Name(name) = call.func.as_ref()
            && self.generic_classes.contains(name.id.as_str())
            && !self.current_name_is_local(name.id.as_str())
        {
            self.record(
                call,
                GENERIC_CONSTRUCTOR_WITHOUT_TYPE,
                "discarded generic source-class construction requires explicit type arguments",
                0,
            );
        }
        self.generic_visit_stmt_expr(node);
    }

    fn visit_stmt_ann_assign(&mut self, node: ast::StmtAnnAssign) {
        if let Some(target) = slice_assignment_target(&node.target) {
            self.record(
                target,
                SLICE_ASSIGNMENT_UNSUPPORTED,
                "assignment to a slice is unsupported",
                0,
            );
        }
        self.generic_visit_stmt_ann_assign(node);
    }

    fn visit_stmt_aug_assign(&mut self, node: ast::StmtAugAssign) {
        if let Some(target) = slice_assignment_target(&node.target) {
            self.record(
                target,
                SLICE_ASSIGNMENT_UNSUPPORTED,
                "assignment to a slice is unsupported",
                0,
            );
        }
        self.generic_visit_stmt_aug_assign(node);
    }

    fn visit_stmt_with(&mut self, node: ast::StmtWith) {
        if node.items.len() > 1 {
            self.record(
                &node,
                MULTI_ITEM_WITH_UNSUPPORTED,
                "with statements may contain only one context-manager item",
                0,
            );
        }
        self.generic_visit_stmt_with(node);
    }

    fn visit_stmt_async_with(&mut self, node: ast::StmtAsyncWith) {
        if node.items.len() > 1 {
            self.record(
                &node,
                MULTI_ITEM_WITH_UNSUPPORTED,
                "with statements may contain only one context-manager item",
                0,
            );
        }
        self.generic_visit_stmt_async_with(node);
    }

    fn visit_expr_list_comp(&mut self, node: ast::ExprListComp) {
        if node.generators.len() > 1 {
            self.record(
                &node,
                MULTIPLE_LIST_GENERATORS,
                "list comprehensions may contain only one generator",
                0,
            );
        }
        let mut locally_bound = self.function_scopes.last().cloned().unwrap_or_default();
        for generator in &node.generators {
            collect_assignment_target_names(&generator.target, &mut locally_bound);
        }
        let mut calls = ExecutedImpureCallCollector {
            impure_functions: &self.impure_functions,
            locally_bound: &locally_bound,
            first_call: None,
        };
        calls.visit_expr(node.elt.as_ref().clone());
        if let Some(byte_offset) = calls.first_call {
            self.candidates.push(Candidate {
                code: IMPURE_LIST_COMPREHENSION_BODY,
                message: "list-comprehension element expression calls an impure source function",
                byte_offset,
                priority: 0,
            });
        }
        self.generic_visit_expr_list_comp(node);
    }

    fn visit_expr_dict_comp(&mut self, node: ast::ExprDictComp) {
        if node.generators.len() > 1 {
            self.record(
                &node,
                MULTIPLE_DICT_GENERATORS,
                "dictionary comprehensions may contain only one generator",
                0,
            );
        }
        self.generic_visit_expr_dict_comp(node);
    }

    fn visit_expr_set_comp(&mut self, node: ast::ExprSetComp) {
        if node.generators.len() > 1 {
            self.record(
                &node,
                MULTIPLE_SET_GENERATORS,
                "set comprehensions may contain only one generator",
                0,
            );
        }
        self.generic_visit_expr_set_comp(node);
    }

    fn visit_expr_bool_op(&mut self, node: ast::ExprBoolOp) {
        if node.op == ast::BoolOp::Or {
            let locally_bound = self.function_scopes.last().cloned().unwrap_or_default();
            let mut calls = PredicateCallCollector {
                predicate_functions: &self.predicate_functions,
                locally_bound: &locally_bound,
                found: false,
            };
            for value in &node.values {
                calls.visit_expr(value.clone());
            }
            if calls.found {
                self.record(
                    &node,
                    IMPURE_DISJUNCTION,
                    "predicate applications cannot occur inside short-circuit disjunctions",
                    0,
                );
            }
        }
        self.generic_visit_expr_bool_op(node);
    }

    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        self.validate_may_field_call(&node);
        self.validate_acc_call(&node);
        let canonical_reveal =
            self.canonical_contract_function(&node.func, &self.reveal_functions, "Reveal");
        if canonical_reveal && node.args.len() == 1 && node.keywords.is_empty() {
            match &node.args[0] {
                ast::Expr::Call(source_call) => {
                    if let ast::Expr::Name(target) = source_call.func.as_ref()
                        && !self.current_name_is_local(target.id.as_str())
                    {
                        if self.impure_functions.contains(target.id.as_str()) {
                            self.record(
                                &node,
                                INVALID_REVEAL_NO_PURE_FUNCTION,
                                "Reveal requires a pure source function",
                                0,
                            );
                        } else if self.pure_functions.contains(target.id.as_str())
                            && !self.opaque_functions.contains(target.id.as_str())
                        {
                            self.record(
                                &node,
                                INVALID_REVEAL_NO_OPAQUE_FUNCTION,
                                "Reveal requires an opaque source function",
                                0,
                            );
                        }
                    }
                }
                _ => self.record(
                    &node,
                    INVALID_REVEAL_NO_FUNCTION,
                    "Reveal requires a function call argument",
                    0,
                ),
            }
        }
        let canonical_previous =
            self.canonical_contract_function(&node.func, &self.previous_functions, "Previous");
        if canonical_previous {
            let valid_target = node.args.len() == 1
                && node.keywords.is_empty()
                && matches!(&node.args[0], ast::Expr::Name(name)
                if self.previous_loop_targets.iter().any(|target| target == name.id.as_str()));
            if !valid_target {
                self.record(
                    &node,
                    INVALID_PREVIOUS,
                    "Previous requires an enclosing for-loop iteration target",
                    0,
                );
            }
        }
        let canonical_let = match node.func.as_ref() {
            ast::Expr::Name(name) => {
                self.let_functions.contains(name.id.as_str())
                    && !self.current_name_is_local(name.id.as_str())
            }
            ast::Expr::Attribute(attribute) if attribute.attr.as_str() == "Let" => {
                matches!(attribute.value.as_ref(), ast::Expr::Name(module)
                    if self.contract_modules.contains(module.id.as_str())
                        && !self.current_name_is_local(module.id.as_str()))
            }
            _ => false,
        };
        if canonical_let && !valid_let_call_shape(&node) {
            self.record(
                &node,
                INVALID_LET,
                "Let requires a value, a result type, and an inline one-argument lambda",
                0,
            );
        }
        self.generic_visit_expr_call(node);
    }

    fn visit_pattern_match_mapping(&mut self, node: ast::PatternMatchMapping) {
        self.record(
            &node,
            MAPPING_PATTERN_UNSUPPORTED,
            "mapping patterns are unsupported",
            0,
        );
        self.generic_visit_pattern_match_mapping(node);
    }

    fn visit_pattern_match_class(&mut self, node: ast::PatternMatchClass) {
        if !node.patterns.is_empty() {
            self.record(
                &node,
                POSITIONAL_CLASS_PATTERN_UNSUPPORTED,
                "positional class patterns are unsupported",
                0,
            );
        } else if !node.kwd_patterns.is_empty() {
            self.record(
                &node,
                PARAMETERIZED_CLASS_PATTERN_UNSUPPORTED,
                "class patterns with parameters are unsupported",
                0,
            );
        }
        self.generic_visit_pattern_match_class(node);
    }
}

#[derive(Clone, Default)]
struct ClassFieldCatalog {
    fields: BTreeSet<String>,
    methods: BTreeSet<String>,
    predicates: BTreeSet<String>,
    properties: BTreeSet<String>,
    complete: bool,
}

#[derive(Default)]
struct ModuleSemantics {
    generic_classes: BTreeSet<String>,
    class_fields: BTreeMap<String, ClassFieldCatalog>,
    functions: BTreeMap<String, bool>,
    opaque_functions: BTreeSet<String>,
    predicates: BTreeSet<String>,
    let_names: BTreeSet<String>,
    previous_names: BTreeSet<String>,
    reveal_names: BTreeSet<String>,
    may_create_names: BTreeSet<String>,
    may_set_names: BTreeSet<String>,
    acc_names: BTreeSet<String>,
    contract_modules: BTreeSet<String>,
}

#[derive(Default)]
struct CanonicalModuleBindings {
    generic_names: BTreeSet<String>,
    pure_names: BTreeSet<String>,
    opaque_names: BTreeSet<String>,
    predicate_names: BTreeSet<String>,
    let_names: BTreeSet<String>,
    previous_names: BTreeSet<String>,
    reveal_names: BTreeSet<String>,
    may_create_names: BTreeSet<String>,
    may_set_names: BTreeSet<String>,
    acc_names: BTreeSet<String>,
    typing_modules: BTreeSet<String>,
    contract_modules: BTreeSet<String>,
}

fn collect_module_semantics(suite: &ast::Suite) -> ModuleSemantics {
    let mut canonical = CanonicalModuleBindings::default();
    let mut semantics = ModuleSemantics::default();
    for statement in suite {
        match statement {
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import.module.as_ref().map(|name| name.as_str()) == Some("typing") =>
            {
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        canonical.generic_names.insert("Generic".to_owned());
                    } else {
                        let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
                        remove_module_binding(&local, &mut canonical, &mut semantics);
                        if alias.name.as_str() == "Generic" {
                            canonical.generic_names.insert(local);
                        }
                    }
                }
            }
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import.module.as_ref().map(|name| name.as_str())
                        == Some("nagini_contracts.contracts") =>
            {
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        canonical.pure_names.insert("Pure".to_owned());
                        canonical.opaque_names.insert("Opaque".to_owned());
                        canonical.predicate_names.insert("Predicate".to_owned());
                        canonical.let_names.insert("Let".to_owned());
                        canonical.previous_names.insert("Previous".to_owned());
                        canonical.reveal_names.insert("Reveal".to_owned());
                        canonical.may_create_names.insert("MayCreate".to_owned());
                        canonical.may_set_names.insert("MaySet".to_owned());
                        canonical.acc_names.insert("Acc".to_owned());
                    } else {
                        let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
                        remove_module_binding(&local, &mut canonical, &mut semantics);
                        if alias.name.as_str() == "Pure" {
                            canonical.pure_names.insert(local);
                        } else if alias.name.as_str() == "Opaque" {
                            canonical.opaque_names.insert(local);
                        } else if alias.name.as_str() == "Predicate" {
                            canonical.predicate_names.insert(local);
                        } else if alias.name.as_str() == "Let" {
                            canonical.let_names.insert(local);
                        } else if alias.name.as_str() == "Previous" {
                            canonical.previous_names.insert(local);
                        } else if alias.name.as_str() == "Reveal" {
                            canonical.reveal_names.insert(local);
                        } else if alias.name.as_str() == "MayCreate" {
                            canonical.may_create_names.insert(local);
                        } else if alias.name.as_str() == "MaySet" {
                            canonical.may_set_names.insert(local);
                        } else if alias.name.as_str() == "Acc" {
                            canonical.acc_names.insert(local);
                        }
                    }
                }
            }
            ast::Stmt::Import(import) => {
                for alias in &import.names {
                    let imported = alias.name.as_str();
                    let local = alias.asname.as_ref().map_or_else(
                        || imported.split('.').next().unwrap_or_default(),
                        |name| name.as_str(),
                    );
                    remove_module_binding(local, &mut canonical, &mut semantics);
                    if imported == "typing" {
                        canonical.typing_modules.insert(local.to_owned());
                    } else if imported == "nagini_contracts.contracts" && alias.asname.is_some() {
                        canonical.contract_modules.insert(local.to_owned());
                    }
                }
            }
            ast::Stmt::ClassDef(class) => {
                let is_generic = class
                    .bases
                    .iter()
                    .any(|base| is_canonical_generic_base(base, &canonical));
                let (methods, predicates, properties) =
                    collect_direct_class_members(class, &canonical);
                let mut field_catalog = ClassFieldCatalog {
                    fields: collect_direct_class_fields(class),
                    methods,
                    predicates,
                    properties,
                    complete: true,
                };
                for base in &class.bases {
                    let ast::Expr::Name(base) = base else {
                        field_catalog.complete = false;
                        continue;
                    };
                    if base.id.as_str() == "object" {
                        continue;
                    }
                    if let Some(base_catalog) = semantics.class_fields.get(base.id.as_str()) {
                        field_catalog.fields.extend(base_catalog.fields.clone());
                        field_catalog.methods.extend(base_catalog.methods.clone());
                        field_catalog
                            .predicates
                            .extend(base_catalog.predicates.clone());
                        field_catalog
                            .properties
                            .extend(base_catalog.properties.clone());
                        field_catalog.complete &= base_catalog.complete;
                    } else {
                        field_catalog.complete = false;
                    }
                }
                remove_module_binding(class.name.as_str(), &mut canonical, &mut semantics);
                semantics
                    .class_fields
                    .insert(class.name.to_string(), field_catalog);
                if is_generic {
                    semantics.generic_classes.insert(class.name.to_string());
                }
            }
            ast::Stmt::FunctionDef(function) => {
                let pure = function
                    .decorator_list
                    .iter()
                    .any(|decorator| is_canonical_pure_decorator(decorator, &canonical));
                let opaque = function
                    .decorator_list
                    .iter()
                    .any(|decorator| is_canonical_opaque_decorator(decorator, &canonical));
                let predicate = function
                    .decorator_list
                    .iter()
                    .any(|decorator| is_canonical_predicate_decorator(decorator, &canonical));
                remove_module_binding(function.name.as_str(), &mut canonical, &mut semantics);
                semantics.functions.insert(function.name.to_string(), pure);
                if opaque {
                    semantics.opaque_functions.insert(function.name.to_string());
                }
                if predicate {
                    semantics.predicates.insert(function.name.to_string());
                }
            }
            ast::Stmt::AsyncFunctionDef(function) => {
                let pure = function
                    .decorator_list
                    .iter()
                    .any(|decorator| is_canonical_pure_decorator(decorator, &canonical));
                let opaque = function
                    .decorator_list
                    .iter()
                    .any(|decorator| is_canonical_opaque_decorator(decorator, &canonical));
                let predicate = function
                    .decorator_list
                    .iter()
                    .any(|decorator| is_canonical_predicate_decorator(decorator, &canonical));
                remove_module_binding(function.name.as_str(), &mut canonical, &mut semantics);
                semantics.functions.insert(function.name.to_string(), pure);
                if opaque {
                    semantics.opaque_functions.insert(function.name.to_string());
                }
                if predicate {
                    semantics.predicates.insert(function.name.to_string());
                }
            }
            ast::Stmt::Assign(assignment) => {
                let predicate_aliases = assignment
                    .targets
                    .iter()
                    .flat_map(|target| {
                        direct_name_assignment_aliases(
                            target,
                            &assignment.value,
                            &semantics.predicates,
                        )
                    })
                    .collect::<BTreeSet<_>>();
                let let_aliases = assignment
                    .targets
                    .iter()
                    .flat_map(|target| {
                        direct_name_assignment_aliases(
                            target,
                            &assignment.value,
                            &canonical.let_names,
                        )
                    })
                    .collect::<BTreeSet<_>>();
                let previous_aliases = assignment
                    .targets
                    .iter()
                    .flat_map(|target| {
                        direct_name_assignment_aliases(
                            target,
                            &assignment.value,
                            &canonical.previous_names,
                        )
                    })
                    .collect::<BTreeSet<_>>();
                let reveal_aliases = assignment
                    .targets
                    .iter()
                    .flat_map(|target| {
                        direct_name_assignment_aliases(
                            target,
                            &assignment.value,
                            &canonical.reveal_names,
                        )
                    })
                    .collect::<BTreeSet<_>>();
                let may_create_aliases = assignment
                    .targets
                    .iter()
                    .flat_map(|target| {
                        direct_name_assignment_aliases(
                            target,
                            &assignment.value,
                            &canonical.may_create_names,
                        )
                    })
                    .collect::<BTreeSet<_>>();
                let may_set_aliases = assignment
                    .targets
                    .iter()
                    .flat_map(|target| {
                        direct_name_assignment_aliases(
                            target,
                            &assignment.value,
                            &canonical.may_set_names,
                        )
                    })
                    .collect::<BTreeSet<_>>();
                let acc_aliases = assignment
                    .targets
                    .iter()
                    .flat_map(|target| {
                        direct_name_assignment_aliases(
                            target,
                            &assignment.value,
                            &canonical.acc_names,
                        )
                    })
                    .collect::<BTreeSet<_>>();
                let mut names = BTreeSet::new();
                for target in &assignment.targets {
                    collect_assignment_target_names(target, &mut names);
                }
                for name in names {
                    remove_module_binding(&name, &mut canonical, &mut semantics);
                }
                semantics.predicates.extend(predicate_aliases);
                canonical.let_names.extend(let_aliases);
                canonical.previous_names.extend(previous_aliases);
                canonical.reveal_names.extend(reveal_aliases);
                canonical.may_create_names.extend(may_create_aliases);
                canonical.may_set_names.extend(may_set_aliases);
                canonical.acc_names.extend(acc_aliases);
            }
            ast::Stmt::AnnAssign(assignment) => {
                let predicate_aliases =
                    assignment
                        .value
                        .as_deref()
                        .map_or_else(BTreeSet::new, |value| {
                            direct_name_assignment_aliases(
                                &assignment.target,
                                value,
                                &semantics.predicates,
                            )
                        });
                let let_aliases = assignment
                    .value
                    .as_deref()
                    .map_or_else(BTreeSet::new, |value| {
                        direct_name_assignment_aliases(
                            &assignment.target,
                            value,
                            &canonical.let_names,
                        )
                    });
                let previous_aliases =
                    assignment
                        .value
                        .as_deref()
                        .map_or_else(BTreeSet::new, |value| {
                            direct_name_assignment_aliases(
                                &assignment.target,
                                value,
                                &canonical.previous_names,
                            )
                        });
                let reveal_aliases =
                    assignment
                        .value
                        .as_deref()
                        .map_or_else(BTreeSet::new, |value| {
                            direct_name_assignment_aliases(
                                &assignment.target,
                                value,
                                &canonical.reveal_names,
                            )
                        });
                let may_create_aliases =
                    assignment
                        .value
                        .as_deref()
                        .map_or_else(BTreeSet::new, |value| {
                            direct_name_assignment_aliases(
                                &assignment.target,
                                value,
                                &canonical.may_create_names,
                            )
                        });
                let may_set_aliases =
                    assignment
                        .value
                        .as_deref()
                        .map_or_else(BTreeSet::new, |value| {
                            direct_name_assignment_aliases(
                                &assignment.target,
                                value,
                                &canonical.may_set_names,
                            )
                        });
                let acc_aliases = assignment
                    .value
                    .as_deref()
                    .map_or_else(BTreeSet::new, |value| {
                        direct_name_assignment_aliases(
                            &assignment.target,
                            value,
                            &canonical.acc_names,
                        )
                    });
                let mut names = BTreeSet::new();
                collect_assignment_target_names(&assignment.target, &mut names);
                for name in names {
                    remove_module_binding(&name, &mut canonical, &mut semantics);
                }
                semantics.predicates.extend(predicate_aliases);
                canonical.let_names.extend(let_aliases);
                canonical.previous_names.extend(previous_aliases);
                canonical.reveal_names.extend(reveal_aliases);
                canonical.may_create_names.extend(may_create_aliases);
                canonical.may_set_names.extend(may_set_aliases);
                canonical.acc_names.extend(acc_aliases);
            }
            ast::Stmt::ImportFrom(import) => {
                if import.names.iter().any(|alias| alias.name.as_str() == "*") {
                    // An unknown star import can replace every source-owned global used below.
                    semantics = ModuleSemantics::default();
                    canonical = CanonicalModuleBindings::default();
                } else {
                    for alias in &import.names {
                        let local = alias.asname.as_ref().unwrap_or(&alias.name);
                        remove_module_binding(local.as_str(), &mut canonical, &mut semantics);
                    }
                }
            }
            _ => {}
        }
    }
    semantics.let_names = canonical.let_names;
    semantics.previous_names = canonical.previous_names;
    semantics.reveal_names = canonical.reveal_names;
    semantics.may_create_names = canonical.may_create_names;
    semantics.may_set_names = canonical.may_set_names;
    semantics.acc_names = canonical.acc_names;
    semantics.contract_modules = canonical.contract_modules;
    semantics
}

fn remove_module_binding(
    name: &str,
    canonical: &mut CanonicalModuleBindings,
    semantics: &mut ModuleSemantics,
) {
    canonical.generic_names.remove(name);
    canonical.pure_names.remove(name);
    canonical.opaque_names.remove(name);
    canonical.predicate_names.remove(name);
    canonical.let_names.remove(name);
    canonical.previous_names.remove(name);
    canonical.reveal_names.remove(name);
    canonical.may_create_names.remove(name);
    canonical.may_set_names.remove(name);
    canonical.acc_names.remove(name);
    canonical.typing_modules.remove(name);
    canonical.contract_modules.remove(name);
    semantics.generic_classes.remove(name);
    semantics.class_fields.remove(name);
    semantics.functions.remove(name);
    semantics.opaque_functions.remove(name);
    semantics.predicates.remove(name);
}

fn is_canonical_generic_base(expression: &ast::Expr, canonical: &CanonicalModuleBindings) -> bool {
    let constructor = match expression {
        ast::Expr::Subscript(subscript) => subscript.value.as_ref(),
        other => other,
    };
    match constructor {
        ast::Expr::Name(name) => canonical.generic_names.contains(name.id.as_str()),
        ast::Expr::Attribute(attribute) => {
            attribute.attr.as_str() == "Generic"
                && matches!(attribute.value.as_ref(), ast::Expr::Name(module) if canonical.typing_modules.contains(module.id.as_str()))
        }
        _ => false,
    }
}

fn is_canonical_pure_decorator(
    expression: &ast::Expr,
    canonical: &CanonicalModuleBindings,
) -> bool {
    match expression {
        ast::Expr::Name(name) => canonical.pure_names.contains(name.id.as_str()),
        ast::Expr::Attribute(attribute) => {
            attribute.attr.as_str() == "Pure"
                && matches!(attribute.value.as_ref(), ast::Expr::Name(module) if canonical.contract_modules.contains(module.id.as_str()))
        }
        _ => false,
    }
}

fn is_canonical_opaque_decorator(
    expression: &ast::Expr,
    canonical: &CanonicalModuleBindings,
) -> bool {
    match expression {
        ast::Expr::Name(name) => canonical.opaque_names.contains(name.id.as_str()),
        ast::Expr::Attribute(attribute) => {
            attribute.attr.as_str() == "Opaque"
                && matches!(attribute.value.as_ref(), ast::Expr::Name(module) if canonical.contract_modules.contains(module.id.as_str()))
        }
        _ => false,
    }
}

fn is_canonical_predicate_decorator(
    expression: &ast::Expr,
    canonical: &CanonicalModuleBindings,
) -> bool {
    match expression {
        ast::Expr::Name(name) => canonical.predicate_names.contains(name.id.as_str()),
        ast::Expr::Attribute(attribute) => {
            attribute.attr.as_str() == "Predicate"
                && matches!(attribute.value.as_ref(), ast::Expr::Name(module) if canonical.contract_modules.contains(module.id.as_str()))
        }
        _ => false,
    }
}

fn assignment_has_unresolved_empty_container(target: &ast::Expr, value: &ast::Expr) -> bool {
    match (target, value) {
        (ast::Expr::Name(_), value) => is_empty_container_literal(value),
        (ast::Expr::Tuple(targets), ast::Expr::Tuple(values)) => targets
            .elts
            .iter()
            .zip(&values.elts)
            .any(|(target, value)| assignment_has_unresolved_empty_container(target, value)),
        (ast::Expr::List(targets), ast::Expr::List(values)) => targets
            .elts
            .iter()
            .zip(&values.elts)
            .any(|(target, value)| assignment_has_unresolved_empty_container(target, value)),
        _ => false,
    }
}

fn is_empty_container_literal(expression: &ast::Expr) -> bool {
    match expression {
        ast::Expr::List(list) => list.elts.is_empty(),
        ast::Expr::Dict(dict) => dict.keys.is_empty(),
        _ => false,
    }
}

fn collect_explicit_type_comment_lines(source: &str) -> BTreeSet<u32> {
    let mut lines = BTreeSet::new();
    for token in lex(source, Mode::Module) {
        let Ok((Tok::Comment(comment), range)) = token else {
            continue;
        };
        let comment = comment.trim_start_matches('#').trim_start();
        let Some(annotation) = comment.strip_prefix("type:") else {
            continue;
        };
        if !annotation.trim_start().starts_with("ignore") {
            lines.insert(source_line(source, u32::from(range.start())));
        }
    }
    lines
}

fn source_line(source: &str, byte_offset: u32) -> u32 {
    let offset = usize::try_from(byte_offset)
        .unwrap_or(source.len())
        .min(source.len());
    u32::try_from(
        source[..offset]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1,
    )
    .unwrap_or(u32::MAX)
}

fn collect_assignment_target_names(expression: &ast::Expr, names: &mut BTreeSet<String>) {
    match expression {
        ast::Expr::Name(name) => {
            names.insert(name.id.to_string());
        }
        ast::Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                collect_assignment_target_names(element, names);
            }
        }
        ast::Expr::List(list) => {
            for element in &list.elts {
                collect_assignment_target_names(element, names);
            }
        }
        ast::Expr::Starred(starred) => collect_assignment_target_names(&starred.value, names),
        _ => {}
    }
}

fn previous_loop_target_name(expression: &ast::Expr) -> Option<String> {
    match expression {
        ast::Expr::Name(name) => Some(name.id.to_string()),
        ast::Expr::Tuple(tuple) => tuple.elts.first().and_then(|element| match element {
            ast::Expr::Name(name) => Some(name.id.to_string()),
            _ => None,
        }),
        _ => None,
    }
}

fn direct_name_assignment_aliases(
    target: &ast::Expr,
    value: &ast::Expr,
    predicates: &BTreeSet<String>,
) -> BTreeSet<String> {
    match (target, value) {
        (ast::Expr::Name(target), ast::Expr::Name(value))
            if predicates.contains(value.id.as_str()) =>
        {
            BTreeSet::from([target.id.to_string()])
        }
        (ast::Expr::Tuple(targets), ast::Expr::Tuple(values))
            if targets.elts.len() == values.elts.len() =>
        {
            targets
                .elts
                .iter()
                .zip(&values.elts)
                .flat_map(|(target, value)| {
                    direct_name_assignment_aliases(target, value, predicates)
                })
                .collect()
        }
        (ast::Expr::List(targets), ast::Expr::List(values))
            if targets.elts.len() == values.elts.len() =>
        {
            targets
                .elts
                .iter()
                .zip(&values.elts)
                .flat_map(|(target, value)| {
                    direct_name_assignment_aliases(target, value, predicates)
                })
                .collect()
        }
        _ => BTreeSet::new(),
    }
}

fn valid_let_call_shape(call: &ast::ExprCall) -> bool {
    if call.args.len() != 3 || !call.keywords.is_empty() {
        return false;
    }
    let ast::Expr::Lambda(lambda) = &call.args[2] else {
        return false;
    };
    let positional = lambda
        .args
        .posonlyargs
        .iter()
        .chain(&lambda.args.args)
        .collect::<Vec<_>>();
    positional.len() == 1
        && positional[0].default.is_none()
        && lambda.args.vararg.is_none()
        && lambda.args.kwonlyargs.is_empty()
        && lambda.args.kwarg.is_none()
}

fn collect_function_scope_bindings(
    arguments: &ast::Arguments,
    body: &[ast::Stmt],
) -> BTreeSet<String> {
    let mut bindings = BTreeSet::new();
    for argument in arguments
        .posonlyargs
        .iter()
        .chain(&arguments.args)
        .chain(&arguments.kwonlyargs)
    {
        bindings.insert(argument.def.arg.to_string());
    }
    if let Some(argument) = &arguments.vararg {
        bindings.insert(argument.arg.to_string());
    }
    if let Some(argument) = &arguments.kwarg {
        bindings.insert(argument.arg.to_string());
    }
    let mut collector = ScopeBindingCollector {
        bindings,
        globals: BTreeSet::new(),
    };
    for statement in body {
        collector.visit_stmt(statement.clone());
    }
    for global in &collector.globals {
        collector.bindings.remove(global);
    }
    collector.bindings
}

fn collect_nominal_argument_bindings(arguments: &ast::Arguments) -> BTreeMap<String, String> {
    let mut bindings = BTreeMap::new();
    for argument in arguments
        .posonlyargs
        .iter()
        .chain(&arguments.args)
        .chain(&arguments.kwonlyargs)
    {
        if let Some(ast::Expr::Name(annotation)) = argument.def.annotation.as_deref() {
            bindings.insert(argument.def.arg.to_string(), annotation.id.to_string());
        }
    }
    bindings
}

fn collect_final_module_globals(suite: &ast::Suite) -> BTreeSet<String> {
    let mut candidates = BTreeSet::new();
    for statement in suite {
        match statement {
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    collect_assignment_target_names(target, &mut candidates);
                }
            }
            ast::Stmt::AnnAssign(assignment) if assignment.value.is_some() => {
                collect_assignment_target_names(&assignment.target, &mut candidates);
            }
            _ => {}
        }
    }

    let mut writes = ModuleWriteCollector::default();
    for statement in suite {
        writes.visit_stmt(statement.clone());
    }
    let mut global_declarations = GlobalDeclarationCollector::default();
    for statement in suite {
        global_declarations.visit_stmt(statement.clone());
    }
    candidates
        .into_iter()
        .filter(|name| writes.counts.get(name).copied() == Some(1))
        .filter(|name| !global_declarations.names.contains(name))
        .collect()
}

#[derive(Default)]
struct ModuleWriteCollector {
    counts: BTreeMap<String, usize>,
}

impl ModuleWriteCollector {
    fn record(&mut self, name: &str) {
        *self.counts.entry(name.to_owned()).or_default() += 1;
    }
}

impl Visitor for ModuleWriteCollector {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if node.ctx == ast::ExprContext::Store {
            self.record(node.id.as_str());
        }
    }

    fn visit_stmt_function_def(&mut self, node: ast::StmtFunctionDef) {
        self.record(node.name.as_str());
    }

    fn visit_stmt_async_function_def(&mut self, node: ast::StmtAsyncFunctionDef) {
        self.record(node.name.as_str());
    }

    fn visit_stmt_class_def(&mut self, node: ast::StmtClassDef) {
        self.record(node.name.as_str());
    }

    fn visit_stmt_import(&mut self, node: ast::StmtImport) {
        for alias in node.names {
            let imported = alias.name.as_str();
            let local = alias.asname.as_ref().map_or_else(
                || imported.split('.').next().unwrap_or_default(),
                |name| name.as_str(),
            );
            self.record(local);
        }
    }

    fn visit_stmt_import_from(&mut self, node: ast::StmtImportFrom) {
        for alias in node.names {
            if alias.name.as_str() != "*" {
                self.record(alias.asname.as_ref().unwrap_or(&alias.name).as_str());
            }
        }
    }
}

#[derive(Default)]
struct GlobalDeclarationCollector {
    names: BTreeSet<String>,
}

impl Visitor for GlobalDeclarationCollector {
    fn visit_stmt_global(&mut self, node: ast::StmtGlobal) {
        self.names
            .extend(node.names.into_iter().map(|name| name.to_string()));
    }
}

fn first_parameter_name(arguments: &ast::Arguments) -> Option<String> {
    arguments
        .posonlyargs
        .first()
        .or_else(|| arguments.args.first())
        .map(|argument| argument.def.arg.to_string())
}

fn collect_direct_class_fields(class: &ast::StmtClassDef) -> BTreeSet<String> {
    let mut fields = BTreeSet::new();
    for statement in &class.body {
        let (arguments, body) = match statement {
            ast::Stmt::FunctionDef(function) => (&function.args, function.body.as_slice()),
            ast::Stmt::AsyncFunctionDef(function) => (&function.args, function.body.as_slice()),
            _ => continue,
        };
        let Some(receiver) = first_parameter_name(arguments) else {
            continue;
        };
        let mut collector = DirectFieldCollector {
            receiver,
            fields: BTreeSet::new(),
        };
        for statement in body {
            collector.visit_stmt(statement.clone());
        }
        fields.extend(collector.fields);
    }
    fields
}

fn collect_direct_class_members(
    class: &ast::StmtClassDef,
    canonical: &CanonicalModuleBindings,
) -> (BTreeSet<String>, BTreeSet<String>, BTreeSet<String>) {
    let mut methods = BTreeSet::new();
    let mut predicates = BTreeSet::new();
    let mut properties = BTreeSet::new();
    for statement in &class.body {
        let (name, decorators) = match statement {
            ast::Stmt::FunctionDef(function) => {
                (function.name.as_str(), function.decorator_list.as_slice())
            }
            ast::Stmt::AsyncFunctionDef(function) => {
                (function.name.as_str(), function.decorator_list.as_slice())
            }
            _ => continue,
        };
        methods.insert(name.to_owned());
        if decorators
            .iter()
            .any(|decorator| is_canonical_predicate_decorator(decorator, canonical))
        {
            predicates.insert(name.to_owned());
        }
        if decorators
            .iter()
            .any(|decorator| matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "property"))
        {
            properties.insert(name.to_owned());
        }
    }
    (methods, predicates, properties)
}

struct DirectFieldCollector {
    receiver: String,
    fields: BTreeSet<String>,
}

impl Visitor for DirectFieldCollector {
    fn visit_expr_attribute(&mut self, node: ast::ExprAttribute) {
        if node.ctx == ast::ExprContext::Store
            && matches!(node.value.as_ref(), ast::Expr::Name(receiver)
                if receiver.id.as_str() == self.receiver)
        {
            self.fields.insert(node.attr.to_string());
        }
        self.generic_visit_expr_attribute(node);
    }

    fn visit_stmt_function_def(&mut self, _node: ast::StmtFunctionDef) {}

    fn visit_stmt_async_function_def(&mut self, _node: ast::StmtAsyncFunctionDef) {}

    fn visit_stmt_class_def(&mut self, _node: ast::StmtClassDef) {}

    fn visit_expr_lambda(&mut self, _node: ast::ExprLambda) {}
}

#[derive(Default)]
struct ScopeBindingCollector {
    bindings: BTreeSet<String>,
    globals: BTreeSet<String>,
}

impl Visitor for ScopeBindingCollector {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if node.ctx == ast::ExprContext::Store {
            self.bindings.insert(node.id.to_string());
        }
    }

    fn visit_stmt_function_def(&mut self, node: ast::StmtFunctionDef) {
        self.bindings.insert(node.name.to_string());
    }

    fn visit_stmt_async_function_def(&mut self, node: ast::StmtAsyncFunctionDef) {
        self.bindings.insert(node.name.to_string());
    }

    fn visit_stmt_class_def(&mut self, node: ast::StmtClassDef) {
        self.bindings.insert(node.name.to_string());
    }

    fn visit_stmt_import(&mut self, node: ast::StmtImport) {
        for alias in node.names {
            let imported = alias.name.as_str();
            let local = alias.asname.as_ref().map_or_else(
                || imported.split('.').next().unwrap_or_default(),
                |name| name.as_str(),
            );
            self.bindings.insert(local.to_owned());
        }
    }

    fn visit_stmt_import_from(&mut self, node: ast::StmtImportFrom) {
        for alias in node.names {
            if alias.name.as_str() != "*" {
                self.bindings
                    .insert(alias.asname.as_ref().unwrap_or(&alias.name).to_string());
            }
        }
    }

    fn visit_excepthandler_except_handler(&mut self, node: ast::ExceptHandlerExceptHandler) {
        if let Some(name) = node.name {
            self.bindings.insert(name.to_string());
        }
        if let Some(exception_type) = node.type_ {
            self.visit_expr(*exception_type);
        }
        for statement in node.body {
            self.visit_stmt(statement);
        }
    }

    fn visit_stmt_global(&mut self, node: ast::StmtGlobal) {
        self.globals
            .extend(node.names.iter().map(ToString::to_string));
    }

    fn visit_expr_lambda(&mut self, _node: ast::ExprLambda) {}
}

struct ExecutedImpureCallCollector<'a> {
    impure_functions: &'a BTreeSet<String>,
    locally_bound: &'a BTreeSet<String>,
    first_call: Option<u32>,
}

struct PredicateCallCollector<'a> {
    predicate_functions: &'a BTreeSet<String>,
    locally_bound: &'a BTreeSet<String>,
    found: bool,
}

impl Visitor for PredicateCallCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if matches!(node.func.as_ref(), ast::Expr::Name(name)
            if self.predicate_functions.contains(name.id.as_str())
                && !self.locally_bound.contains(name.id.as_str()))
        {
            self.found = true;
        }
        self.generic_visit_expr_call(node);
    }

    fn visit_expr_lambda(&mut self, _node: ast::ExprLambda) {}
}

impl Visitor for ExecutedImpureCallCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if let ast::Expr::Name(name) = node.func.as_ref()
            && self.impure_functions.contains(name.id.as_str())
            && !self.locally_bound.contains(name.id.as_str())
        {
            let offset = u32::from(node.range.start());
            self.first_call = Some(
                self.first_call
                    .map_or(offset, |current| current.min(offset)),
            );
        }
        self.generic_visit_expr_call(node);
    }

    fn visit_expr_lambda(&mut self, _node: ast::ExprLambda) {}
}

fn slice_assignment_target(expression: &ast::Expr) -> Option<&ast::Expr> {
    match expression {
        ast::Expr::Subscript(subscript)
            if matches!(subscript.slice.as_ref(), ast::Expr::Slice(_)) =>
        {
            Some(expression)
        }
        ast::Expr::Tuple(tuple) => tuple.elts.iter().find_map(slice_assignment_target),
        ast::Expr::List(list) => list.elts.iter().find_map(slice_assignment_target),
        ast::Expr::Starred(starred) => slice_assignment_target(&starred.value),
        _ => None,
    }
}

pub fn validate_language_wellformedness(
    source: &str,
    path: &str,
) -> Result<(), LanguageWellformednessFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| LanguageWellformednessFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
        byte_offset: 0,
        line: 1,
        column: 1,
    })?;
    validate_language_suite(&suite, source)
}

pub(crate) fn validate_language_suite(
    suite: &ast::Suite,
    source: &str,
) -> Result<(), LanguageWellformednessFailure> {
    let mut collector = LanguageRestrictionCollector::new(suite, source);
    for statement in suite {
        collector.visit_stmt(statement.clone());
    }
    let Some(candidate) = collector
        .candidates
        .into_iter()
        .min_by_key(|candidate| (candidate.byte_offset, candidate.priority))
    else {
        return Ok(());
    };
    let offset = usize::try_from(candidate.byte_offset)
        .unwrap_or(source.len())
        .min(source.len());
    let prefix = &source[..offset];
    Err(LanguageWellformednessFailure {
        code: candidate.code,
        message: candidate.message.to_owned(),
        byte_offset: candidate.byte_offset,
        line: u32::try_from(prefix.bytes().filter(|byte| *byte == b'\n').count() + 1)
            .unwrap_or(u32::MAX),
        column: u32::try_from(
            prefix
                .rsplit_once('\n')
                .map_or(prefix.len(), |(_, suffix)| suffix.len())
                + 1,
        )
        .unwrap_or(u32::MAX),
    })
}
