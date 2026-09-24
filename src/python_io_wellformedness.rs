//! Source-bound well-formedness for Nagini IO declarations and ghost-output assignments.

mod existentials;

use std::collections::{BTreeMap, BTreeSet};

use rustpython_ast::{Ranged, Visitor};
use rustpython_parser::{Mode, Parse, Tok, ast, lexer::lex};

pub const MULTIPLE_TARGETS: &str = "invalid.program:invalid.get_ghost_output.multiple_targets";
pub const TARGET_NOT_VARIABLE: &str =
    "invalid.program:invalid.get_ghost_output.target_not_variable";
pub const RESULT_IDENTIFIER_NOT_STRING: &str =
    "invalid.program:invalid.get_ghost_output.result_identifier_not_str";
pub const ARGUMENT_NOT_IO_OPERATION: &str =
    "invalid.program:invalid.get_ghost_output.argument_not_io_operation";
pub const INVALID_RESULT_IDENTIFIER: &str =
    "invalid.program:invalid.get_ghost_output.invalid_result_identifier";
pub const TYPE_MISMATCH: &str = "invalid.program:invalid.get_ghost_output.type_mismatch";
pub const CALL_SHAPE_UNSUPPORTED: &str =
    "frontend.python.io.get-ghost-output.call-shape-unsupported";
pub const TARGET_TYPE_UNKNOWN: &str = "frontend.python.io.get-ghost-output.target-type-unknown";
pub const MISPLACED_PROPERTY: &str = "invalid.program:invalid.io_operation.misplaced_property";
pub const DUPLICATE_PROPERTY: &str = "invalid.program:invalid.io_operation.duplicate_property";
pub const PROPERTY_DEPENDS_ON_NON_INPUT: &str =
    "invalid.program:invalid.io_operation.depends_on_not_imput";
pub const MISPLACED_IO_EXISTS: &str = "invalid.program:invalid.ioexists.misplaced";
pub const PROPERTY_CALL_SHAPE_UNSUPPORTED: &str =
    "frontend.python.io.operation-property.call-shape-unsupported";
pub const EXISTENTIAL_USE_UNDEFINED: &str = "invalid.program:io_existential_var.use_of_undefined";
pub const EXISTENTIAL_DEFINITION_TYPE_MISMATCH: &str =
    "invalid.program:invalid.io_existential_var.defining_expression_type_mismatch";
pub const OPERATION_UNDEFINED_EXISTENTIAL: &str =
    "invalid.program:invalid.io_operation.body.use_of_undefined_existential";
pub const OPERATION_RESULT_NOT_VARIABLE: &str =
    "invalid.program:invalid.io_operation.body.not_variable_in_result_position";
pub const OPERATION_RESULT_NOT_EXISTENTIAL: &str =
    "invalid.program:invalid.io_operation.body.variable_not_existential";

// This is the exact public IOExists family exported by the pinned nagini_contracts support
// package, not a verifier materialization limit. A future provider API must advance the bound
// frontend identity together with this catalog.
const MAX_IO_EXISTS_ARITY: u8 = 15;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IoWellformednessFailure {
    pub code: &'static str,
    pub message: String,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Debug)]
struct OperationOutput {
    name: String,
    annotation: Option<String>,
}

#[derive(Clone, Debug)]
struct Operation {
    inputs: BTreeSet<String>,
    outputs: Vec<OperationOutput>,
}

#[derive(Clone, Default)]
struct Bindings {
    canonical: BTreeMap<String, String>,
    operations: BTreeMap<String, Operation>,
    external_operations: BTreeSet<String>,
    deferred_imports: BTreeSet<String>,
    star_io_contracts_imported: bool,
    star_io_builtins_imported: bool,
    locally_shadowed: BTreeSet<String>,
    shadowed_module_names: BTreeSet<String>,
}

/// Validate every source-owned `GetGhostOutput` assignment against the final module binding graph.
pub fn validate_io_wellformedness(source: &str, path: &str) -> Result<(), IoWellformednessFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| IoWellformednessFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
        byte_offset: 0,
        line: 1,
        column: 1,
    })?;
    let ambiguous = module_rebound_names(&suite);
    let mut bindings = initial_bindings(&ambiguous);
    bind_module_imports(&suite, &ambiguous, &mut bindings);
    collect_final_operations(&suite, &bindings.canonical, &mut bindings.operations);
    let type_comments = collect_type_comments(source)?;

    reject_nested_io_exists(&suite, &bindings, source)?;

    for statement in &suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                validate_function_body(function, &bindings, &type_comments, source)?;
            }
            ast::Stmt::ClassDef(class) => {
                validate_class_methods(class, &bindings, &type_comments, source)?;
            }
            _ => reject_first_property_call_in_statement(statement, &bindings, source)?,
        }
    }
    Ok(())
}

fn validate_function_body(
    function: &ast::StmtFunctionDef,
    bindings: &Bindings,
    type_comments: &BTreeMap<u32, String>,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let mut function_bindings = bindings.clone();
    for local in function_local_names(function) {
        function_bindings.canonical.remove(&local);
        function_bindings.operations.remove(&local);
        function_bindings.external_operations.remove(&local);
        function_bindings.deferred_imports.remove(&local);
        function_bindings.locally_shadowed.insert(local);
    }
    if let Some(operation) = function_bindings.operations.get(function.name.as_str()) {
        validate_io_operation_properties(function, operation, &function_bindings, source)?;
    } else {
        reject_first_property_call_in_statements(&function.body, &function_bindings, source)?;
    }
    existentials::validate_function(function, &function_bindings, source)?;
    validate_statements(&function.body, &function_bindings, type_comments, source)
}

fn validate_class_methods(
    class: &ast::StmtClassDef,
    bindings: &Bindings,
    type_comments: &BTreeMap<u32, String>,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    for statement in &class.body {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                validate_function_body(function, bindings, type_comments, source)?;
            }
            ast::Stmt::ClassDef(nested) => {
                validate_class_methods(nested, bindings, type_comments, source)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn initial_bindings(ambiguous: &BTreeSet<String>) -> Bindings {
    let mut bindings = Bindings {
        shadowed_module_names: ambiguous.clone(),
        ..Bindings::default()
    };
    for builtin in ["bool", "int", "str"] {
        if !ambiguous.contains(builtin) {
            bindings
                .canonical
                .insert(builtin.to_owned(), builtin.to_owned());
        }
    }
    bindings
}

fn bind_module_imports(suite: &[ast::Stmt], ambiguous: &BTreeSet<String>, bindings: &mut Bindings) {
    for statement in suite {
        let ast::Stmt::ImportFrom(import) = statement else {
            continue;
        };
        if !import.level.is_none_or(|level| level == 0_u32) {
            continue;
        }
        let module = import.module.as_ref().map(|module| module.as_str());
        if module == Some("nagini_contracts.contracts") {
            for alias in &import.names {
                if alias.name.as_str() == "*" {
                    for primitive in ["Ensures", "Implies", "Requires", "Result"] {
                        if !ambiguous.contains(primitive) {
                            bindings
                                .canonical
                                .insert(primitive.to_owned(), primitive.to_owned());
                        }
                    }
                    continue;
                }
                if !matches!(
                    alias.name.as_str(),
                    "Ensures" | "Implies" | "Requires" | "Result"
                ) {
                    continue;
                }
                let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
                if !ambiguous.contains(&local) {
                    bindings.canonical.insert(local, alias.name.to_string());
                }
            }
            continue;
        }
        if module == Some("nagini_contracts.io_builtins") {
            for alias in &import.names {
                if alias.name.as_str() == "*" {
                    bindings.star_io_builtins_imported = true;
                    continue;
                }
                let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
                if !ambiguous.contains(&local) {
                    bindings.external_operations.insert(local);
                }
            }
            continue;
        }
        if module != Some("nagini_contracts.io_contracts") {
            for alias in &import.names {
                if alias.name.as_str() == "*" {
                    continue;
                }
                let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
                if !ambiguous.contains(&local) {
                    bindings.deferred_imports.insert(local);
                }
            }
            continue;
        }
        for alias in &import.names {
            if alias.name.as_str() == "*" {
                bindings.star_io_contracts_imported = true;
                for primitive in [
                    "GetGhostOutput",
                    "IOOperation",
                    "Place",
                    "Terminates",
                    "TerminationMeasure",
                    "token",
                ] {
                    if !ambiguous.contains(primitive) {
                        bindings
                            .canonical
                            .insert(primitive.to_owned(), primitive.to_owned());
                    }
                }
                for arity in 1..=MAX_IO_EXISTS_ARITY {
                    let name = format!("IOExists{arity}");
                    if !ambiguous.contains(&name) {
                        bindings.canonical.insert(name.clone(), name);
                    }
                }
                continue;
            }
            if !matches!(
                alias.name.as_str(),
                "GetGhostOutput"
                    | "IOOperation"
                    | "Place"
                    | "Terminates"
                    | "TerminationMeasure"
                    | "token"
            ) && !is_io_exists_export(alias.name.as_str())
            {
                continue;
            }
            let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
            if !ambiguous.contains(&local) {
                bindings.canonical.insert(local, alias.name.to_string());
            }
        }
    }
}

fn is_io_exists_export(name: &str) -> bool {
    if name == "IOExists" {
        return true;
    }
    let Some(arity) = name.strip_prefix("IOExists") else {
        return false;
    };
    !arity.is_empty()
        && !arity.starts_with('0')
        && arity.bytes().all(|byte| byte.is_ascii_digit())
        && arity
            .parse::<u8>()
            .is_ok_and(|arity| (1..=MAX_IO_EXISTS_ARITY).contains(&arity))
}

fn reject_nested_io_exists(
    suite: &[ast::Stmt],
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let mut collector = NestedIoExistsCollector {
        bindings,
        local_scopes: Vec::new(),
        first_nested: None,
    };
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                collector.visit_stmt_function_def(function.clone());
            }
            ast::Stmt::AsyncFunctionDef(function) => {
                collector.visit_stmt_async_function_def(function.clone());
            }
            ast::Stmt::ClassDef(class) => collector.visit_class_methods(class),
            _ => {}
        }
    }
    if let Some(call) = collector.first_nested {
        return fail(
            &call,
            source,
            MISPLACED_IO_EXISTS,
            "IOExists declarations cannot be nested inside another IOExists declaration",
        );
    }
    Ok(())
}

struct NestedIoExistsCollector<'a> {
    bindings: &'a Bindings,
    local_scopes: Vec<BTreeSet<String>>,
    first_nested: Option<ast::ExprCall>,
}

impl NestedIoExistsCollector<'_> {
    fn visit_class_methods(&mut self, class: &ast::StmtClassDef) {
        for statement in &class.body {
            match statement {
                ast::Stmt::FunctionDef(function) => {
                    self.visit_stmt_function_def(function.clone());
                }
                ast::Stmt::AsyncFunctionDef(function) => {
                    self.visit_stmt_async_function_def(function.clone());
                }
                ast::Stmt::ClassDef(nested) => self.visit_class_methods(nested),
                _ => {}
            }
        }
    }

    fn name_is_shadowed(&self, name: &str) -> bool {
        self.bindings.shadowed_module_names.contains(name)
            || self
                .local_scopes
                .iter()
                .rev()
                .any(|scope| scope.contains(name))
    }

    fn is_constructor(&self, expression: &ast::Expr) -> bool {
        let ast::Expr::Name(name) = expression else {
            return false;
        };
        if self.name_is_shadowed(name.id.as_str()) {
            return false;
        }
        self.bindings
            .canonical
            .get(name.id.as_str())
            .is_some_and(|canonical| is_io_exists_export(canonical))
            || (self.bindings.star_io_contracts_imported && is_io_exists_export(name.id.as_str()))
    }

    fn is_invocation(&self, call: &ast::ExprCall) -> bool {
        let ast::Expr::Call(constructor) = call.func.as_ref() else {
            return false;
        };
        self.is_constructor(&constructor.func)
            && constructor.keywords.is_empty()
            && !constructor.args.is_empty()
            && call.keywords.is_empty()
            && matches!(call.args.as_slice(), [ast::Expr::Lambda(_)])
    }

    fn visit_allowed_statements(
        &mut self,
        statements: &[ast::Stmt],
        allow_io_operation_return: bool,
    ) {
        for statement in statements {
            if let ast::Stmt::Expr(expression) = statement
                && let ast::Expr::Call(call) = expression.value.as_ref()
                && self.is_invocation(call)
            {
                self.visit_allowed_invocation(call);
            } else if allow_io_operation_return
                && let ast::Stmt::Return(return_statement) = statement
                && let Some(ast::Expr::Call(call)) = return_statement.value.as_deref()
                && self.is_invocation(call)
            {
                self.visit_allowed_invocation(call);
            } else {
                self.visit_stmt(statement.clone());
            }
        }
    }

    fn visit_allowed_invocation(&mut self, call: &ast::ExprCall) {
        for argument in &call.args {
            self.visit_expr(argument.clone());
        }
        for keyword in &call.keywords {
            self.visit_expr(keyword.value.clone());
        }
    }
}

impl Visitor for NestedIoExistsCollector<'_> {
    fn visit_stmt_function_def(&mut self, node: ast::StmtFunctionDef) {
        let local_names = function_local_names_from_parts(&node.args, &node.body);
        let allow_io_operation_return =
            has_canonical_decorator(&node, &self.bindings.canonical, "IOOperation");
        self.local_scopes.push(local_names);
        self.visit_allowed_statements(&node.body, allow_io_operation_return);
        self.local_scopes.pop();
    }

    fn visit_stmt_async_function_def(&mut self, node: ast::StmtAsyncFunctionDef) {
        let local_names = function_local_names_from_parts(&node.args, &node.body);
        self.local_scopes.push(local_names);
        self.visit_allowed_statements(&node.body, false);
        self.local_scopes.pop();
    }

    fn visit_stmt_class_def(&mut self, node: ast::StmtClassDef) {
        self.visit_class_methods(&node);
    }

    fn visit_stmt_for(&mut self, node: ast::StmtFor) {
        self.visit_expr(*node.target);
        self.visit_expr(*node.iter);
        self.visit_allowed_statements(&node.body, false);
        for statement in node.orelse {
            self.visit_stmt(statement);
        }
    }

    fn visit_stmt_async_for(&mut self, node: ast::StmtAsyncFor) {
        self.visit_expr(*node.target);
        self.visit_expr(*node.iter);
        self.visit_allowed_statements(&node.body, false);
        for statement in node.orelse {
            self.visit_stmt(statement);
        }
    }

    fn visit_stmt_while(&mut self, node: ast::StmtWhile) {
        self.visit_expr(*node.test);
        self.visit_allowed_statements(&node.body, false);
        for statement in node.orelse {
            self.visit_stmt(statement);
        }
    }

    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if !self.is_invocation(&node) {
            self.generic_visit_expr_call(node);
            return;
        }
        self.first_nested.get_or_insert(node);
    }
}

fn collect_final_operations(
    suite: &[ast::Stmt],
    canonical: &BTreeMap<String, String>,
    operations: &mut BTreeMap<String, Operation>,
) {
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                operations.remove(function.name.as_str());
                if has_canonical_decorator(function, canonical, "IOOperation") {
                    operations.insert(
                        function.name.to_string(),
                        Operation {
                            inputs: operation_inputs(function),
                            outputs: operation_outputs(function, canonical),
                        },
                    );
                }
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    remove_operation_targets(target, operations);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                remove_operation_targets(&assignment.target, operations);
            }
            ast::Stmt::ClassDef(class) => {
                operations.remove(class.name.as_str());
            }
            _ => {}
        }
    }
}

fn operation_outputs(
    function: &ast::StmtFunctionDef,
    canonical: &BTreeMap<String, String>,
) -> Vec<OperationOutput> {
    function
        .args
        .posonlyargs
        .iter()
        .chain(&function.args.args)
        .filter(|argument| argument.default.is_some())
        .map(|argument| OperationOutput {
            name: argument.def.arg.to_string(),
            annotation: argument
                .def
                .annotation
                .as_deref()
                .and_then(|annotation| annotation_key(annotation, canonical)),
        })
        .collect()
}

fn operation_inputs(function: &ast::StmtFunctionDef) -> BTreeSet<String> {
    function
        .args
        .posonlyargs
        .iter()
        .chain(&function.args.args)
        .filter(|argument| argument.default.is_none())
        // The declaration checker has already established that the first required
        // argument is the unique Place preset. Nagini properties may depend on
        // value inputs, but not on that linear state token.
        .skip(1)
        .map(|argument| argument.def.arg.to_string())
        .collect()
}

fn validate_io_operation_properties(
    function: &ast::StmtFunctionDef,
    operation: &Operation,
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let mut seen = BTreeSet::new();
    for statement in &function.body {
        let direct = match statement {
            ast::Stmt::Expr(expression) => property_call(&expression.value, bindings),
            _ => None,
        };
        let Some((call, property)) = direct else {
            reject_first_property_call_in_statement(statement, bindings, source)?;
            continue;
        };

        if !seen.insert(property) {
            return fail(
                call,
                source,
                DUPLICATE_PROPERTY,
                format!("IO operation declares {property} more than once"),
            );
        }
        let [argument] = call.args.as_slice() else {
            return fail(
                call,
                source,
                PROPERTY_CALL_SHAPE_UNSUPPORTED,
                format!("{property} requires exactly one positional argument"),
            );
        };
        if !call.keywords.is_empty() {
            return fail(
                call,
                source,
                PROPERTY_CALL_SHAPE_UNSUPPORTED,
                format!("{property} does not accept keyword arguments"),
            );
        }
        reject_first_property_call_in_expression(argument, bindings, source)?;

        let mut names = PropertyArgumentNameCollector::default();
        names.visit_expr(argument.clone());
        if let Some(name) = names
            .names
            .into_iter()
            .find(|name| !operation.inputs.contains(name.id.as_str()))
        {
            return fail(
                &name,
                source,
                PROPERTY_DEPENDS_ON_NON_INPUT,
                format!(
                    "{property} depends on non-input name {:?}",
                    name.id.as_str()
                ),
            );
        }
    }
    Ok(())
}

fn property_call<'a>(
    expression: &'a ast::Expr,
    bindings: &Bindings,
) -> Option<(&'a ast::ExprCall, &'static str)> {
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return None;
    };
    match bindings.canonical.get(name.id.as_str()).map(String::as_str) {
        Some("Terminates") => Some((call, "Terminates")),
        Some("TerminationMeasure") => Some((call, "TerminationMeasure")),
        _ => None,
    }
}

struct PropertyCallCollector<'a> {
    bindings: &'a Bindings,
    first: Option<ast::ExprCall>,
}

impl Visitor for PropertyCallCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        let canonical = match node.func.as_ref() {
            ast::Expr::Name(name) => self
                .bindings
                .canonical
                .get(name.id.as_str())
                .map(String::as_str),
            _ => None,
        };
        if matches!(canonical, Some("Terminates" | "TerminationMeasure")) {
            self.first.get_or_insert(node);
            return;
        }
        self.generic_visit_expr_call(node);
    }
}

fn reject_first_property_call_in_statements(
    statements: &[ast::Stmt],
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    for statement in statements {
        reject_first_property_call_in_statement(statement, bindings, source)?;
    }
    Ok(())
}

fn reject_first_property_call_in_statement(
    statement: &ast::Stmt,
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let mut collector = PropertyCallCollector {
        bindings,
        first: None,
    };
    collector.visit_stmt(statement.clone());
    if let Some(call) = collector.first {
        return fail(
            &call,
            source,
            MISPLACED_PROPERTY,
            "IO operation properties must be direct statements in an IO operation body",
        );
    }
    Ok(())
}

fn reject_first_property_call_in_expression(
    expression: &ast::Expr,
    bindings: &Bindings,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let mut collector = PropertyCallCollector {
        bindings,
        first: None,
    };
    collector.visit_expr(expression.clone());
    if let Some(call) = collector.first {
        return fail(
            &call,
            source,
            MISPLACED_PROPERTY,
            "IO operation properties cannot be nested inside another property",
        );
    }
    Ok(())
}

#[derive(Default)]
struct PropertyArgumentNameCollector {
    names: Vec<ast::ExprName>,
}

impl Visitor for PropertyArgumentNameCollector {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if matches!(node.ctx, ast::ExprContext::Load) {
            self.names.push(node);
        }
    }

    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        // Nagini's IO analyzer visits call arguments while checking a property,
        // not the callable expression itself. Preserve that binding behavior.
        for argument in node.args {
            self.visit_expr(argument);
        }
        for keyword in node.keywords {
            self.visit_expr(keyword.value);
        }
    }
}

fn validate_statements(
    statements: &[ast::Stmt],
    bindings: &Bindings,
    type_comments: &BTreeMap<u32, String>,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    for statement in statements {
        match statement {
            ast::Stmt::Assign(assignment) => {
                if let Some(call) = get_ghost_output_call(&assignment.value, bindings) {
                    validate_get_ghost_output_assignment(
                        assignment,
                        call,
                        bindings,
                        type_comments,
                        source,
                    )?;
                }
            }
            ast::Stmt::If(branch) => {
                validate_statements(&branch.body, bindings, type_comments, source)?;
                validate_statements(&branch.orelse, bindings, type_comments, source)?;
            }
            ast::Stmt::While(loop_statement) => {
                validate_statements(&loop_statement.body, bindings, type_comments, source)?;
                validate_statements(&loop_statement.orelse, bindings, type_comments, source)?;
            }
            ast::Stmt::For(loop_statement) => {
                validate_statements(&loop_statement.body, bindings, type_comments, source)?;
                validate_statements(&loop_statement.orelse, bindings, type_comments, source)?;
            }
            ast::Stmt::Try(try_statement) => {
                validate_statements(&try_statement.body, bindings, type_comments, source)?;
                validate_statements(&try_statement.orelse, bindings, type_comments, source)?;
                validate_statements(&try_statement.finalbody, bindings, type_comments, source)?;
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    validate_statements(&handler.body, bindings, type_comments, source)?;
                }
            }
            ast::Stmt::With(with_statement) => {
                validate_statements(&with_statement.body, bindings, type_comments, source)?;
            }
            ast::Stmt::Match(match_statement) => {
                for case in &match_statement.cases {
                    validate_statements(&case.body, bindings, type_comments, source)?;
                }
            }
            ast::Stmt::FunctionDef(_) | ast::Stmt::ClassDef(_) => {}
            _ => {}
        }
    }
    Ok(())
}

fn validate_get_ghost_output_assignment(
    assignment: &ast::StmtAssign,
    call: &ast::ExprCall,
    bindings: &Bindings,
    type_comments: &BTreeMap<u32, String>,
    source: &str,
) -> Result<(), IoWellformednessFailure> {
    let [target] = assignment.targets.as_slice() else {
        return fail(
            assignment,
            source,
            MULTIPLE_TARGETS,
            "GetGhostOutput requires exactly one assignment target",
        );
    };
    if !matches!(target, ast::Expr::Name(_)) {
        return fail(
            assignment,
            source,
            TARGET_NOT_VARIABLE,
            "GetGhostOutput requires a simple local-variable target",
        );
    }
    let [operation_expression, result_identifier] = call.args.as_slice() else {
        return fail(
            assignment,
            source,
            CALL_SHAPE_UNSUPPORTED,
            "GetGhostOutput requires an operation call and a result identifier",
        );
    };
    if !call.keywords.is_empty() {
        return fail(
            assignment,
            source,
            CALL_SHAPE_UNSUPPORTED,
            "GetGhostOutput does not accept keyword arguments",
        );
    }
    let ast::Expr::Constant(identifier) = result_identifier else {
        return fail(
            assignment,
            source,
            RESULT_IDENTIFIER_NOT_STRING,
            "GetGhostOutput result identifiers must be string literals",
        );
    };
    let ast::Constant::Str(result_name) = &identifier.value else {
        return fail(
            assignment,
            source,
            RESULT_IDENTIFIER_NOT_STRING,
            "GetGhostOutput result identifiers must be string literals",
        );
    };
    let ast::Expr::Call(operation_call) = operation_expression else {
        return fail(
            assignment,
            source,
            ARGUMENT_NOT_IO_OPERATION,
            "GetGhostOutput requires a direct IO operation call",
        );
    };
    let ast::Expr::Name(operation_name) = operation_call.func.as_ref() else {
        return fail(
            assignment,
            source,
            ARGUMENT_NOT_IO_OPERATION,
            "GetGhostOutput requires a direct source-declared IO operation call",
        );
    };
    let Some(operation) = bindings.operations.get(operation_name.id.as_str()) else {
        return fail(
            assignment,
            source,
            ARGUMENT_NOT_IO_OPERATION,
            "GetGhostOutput argument is not a source-declared IO operation",
        );
    };
    let Some(output) = operation
        .outputs
        .iter()
        .find(|output| output.name == result_name.as_str())
    else {
        return fail(
            assignment,
            source,
            INVALID_RESULT_IDENTIFIER,
            format!("IO operation has no output named {result_name:?}"),
        );
    };
    let line = location(source, assignment.range().start().into()).0;
    let target_annotation = assignment
        .type_comment
        .as_deref()
        .or_else(|| type_comments.get(&line).map(String::as_str))
        .and_then(|annotation| annotation_expression_key(annotation, &bindings.canonical));
    let Some(target_annotation) = target_annotation else {
        return fail(
            assignment,
            source,
            TARGET_TYPE_UNKNOWN,
            "GetGhostOutput target requires a source annotation or assignment type comment",
        );
    };
    if output.annotation.as_deref() != Some(target_annotation.as_str()) {
        return fail(
            assignment,
            source,
            TYPE_MISMATCH,
            format!(
                "GetGhostOutput target type {target_annotation:?} differs from output type {:?}",
                output.annotation
            ),
        );
    }
    Ok(())
}

fn get_ghost_output_call<'a>(
    expression: &'a ast::Expr,
    bindings: &Bindings,
) -> Option<&'a ast::ExprCall> {
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    matches!(call.func.as_ref(), ast::Expr::Name(name)
        if bindings.canonical.get(name.id.as_str()).map(String::as_str)
            == Some("GetGhostOutput"))
    .then_some(call)
}

fn has_canonical_decorator(
    function: &ast::StmtFunctionDef,
    canonical: &BTreeMap<String, String>,
    expected: &str,
) -> bool {
    function.decorator_list.iter().any(|decorator| {
        matches!(decorator, ast::Expr::Name(name)
            if canonical.get(name.id.as_str()).map(String::as_str) == Some(expected))
    })
}

fn annotation_expression_key(
    annotation: &str,
    canonical: &BTreeMap<String, String>,
) -> Option<String> {
    let expression = ast::Expr::parse(annotation.trim(), "<io-target-type-comment>").ok()?;
    annotation_key(&expression, canonical)
}

fn annotation_key(annotation: &ast::Expr, canonical: &BTreeMap<String, String>) -> Option<String> {
    let ast::Expr::Name(name) = annotation else {
        return None;
    };
    Some(
        canonical
            .get(name.id.as_str())
            .cloned()
            .unwrap_or_else(|| name.id.to_string()),
    )
}

fn collect_type_comments(source: &str) -> Result<BTreeMap<u32, String>, IoWellformednessFailure> {
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
        let byte_offset = u32::from(range.start());
        let line = location(source, byte_offset).0;
        if comments.insert(line, annotation.to_owned()).is_some() {
            return Err(IoWellformednessFailure {
                code: "frontend.python.io.type-comment-duplicate",
                message: format!("multiple assignment type comments occur on line {line}"),
                byte_offset,
                line,
                column: location(source, byte_offset).1,
            });
        }
    }
    Ok(comments)
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

fn function_local_names(function: &ast::StmtFunctionDef) -> BTreeSet<String> {
    function_local_names_from_parts(&function.args, &function.body)
}

fn function_local_names_from_parts(
    arguments: &ast::Arguments,
    body: &[ast::Stmt],
) -> BTreeSet<String> {
    let mut names = arguments
        .posonlyargs
        .iter()
        .chain(&arguments.args)
        .chain(&arguments.kwonlyargs)
        .map(|argument| argument.def.arg.to_string())
        .collect::<BTreeSet<_>>();
    if let Some(argument) = arguments.vararg.as_deref() {
        names.insert(argument.arg.to_string());
    }
    if let Some(argument) = arguments.kwarg.as_deref() {
        names.insert(argument.arg.to_string());
    }
    collect_statement_bindings(body, &mut names);
    names
}

fn collect_statement_bindings(statements: &[ast::Stmt], names: &mut BTreeSet<String>) {
    for statement in statements {
        match statement {
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    collect_target_names(target, names);
                }
            }
            ast::Stmt::AnnAssign(assignment) => collect_target_names(&assignment.target, names),
            ast::Stmt::For(loop_statement) => {
                collect_target_names(&loop_statement.target, names);
                collect_statement_bindings(&loop_statement.body, names);
                collect_statement_bindings(&loop_statement.orelse, names);
            }
            ast::Stmt::If(branch) => {
                collect_statement_bindings(&branch.body, names);
                collect_statement_bindings(&branch.orelse, names);
            }
            ast::Stmt::While(loop_statement) => {
                collect_statement_bindings(&loop_statement.body, names);
                collect_statement_bindings(&loop_statement.orelse, names);
            }
            ast::Stmt::Try(try_statement) => {
                collect_statement_bindings(&try_statement.body, names);
                collect_statement_bindings(&try_statement.orelse, names);
                collect_statement_bindings(&try_statement.finalbody, names);
                for handler in &try_statement.handlers {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    if let Some(name) = &handler.name {
                        names.insert(name.to_string());
                    }
                    collect_statement_bindings(&handler.body, names);
                }
            }
            ast::Stmt::With(with_statement) => {
                for item in &with_statement.items {
                    if let Some(target) = &item.optional_vars {
                        collect_target_names(target, names);
                    }
                }
                collect_statement_bindings(&with_statement.body, names);
            }
            ast::Stmt::FunctionDef(function) => {
                names.insert(function.name.to_string());
            }
            ast::Stmt::ClassDef(class) => {
                names.insert(class.name.to_string());
            }
            _ => {}
        }
    }
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
        ast::Expr::List(list) => {
            for element in &list.elts {
                collect_target_names(element, names);
            }
        }
        _ => {}
    }
}

fn remove_operation_targets(target: &ast::Expr, operations: &mut BTreeMap<String, Operation>) {
    let mut names = BTreeSet::new();
    collect_target_names(target, &mut names);
    for name in names {
        operations.remove(&name);
    }
}

fn fail<T>(
    ranged: &impl Ranged,
    source: &str,
    code: &'static str,
    message: impl Into<String>,
) -> Result<T, IoWellformednessFailure> {
    let byte_offset = u32::from(ranged.range().start());
    let (line, column) = location(source, byte_offset);
    Err(IoWellformednessFailure {
        code,
        message: message.into(),
        byte_offset,
        line,
        column,
    })
}

fn location(source: &str, byte_offset: u32) -> (u32, u32) {
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
    (line, column)
}
