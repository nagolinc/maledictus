//! Admission of canonical type-only imports without inventing runtime bindings.

use rustpython_ast::Visitor;
use rustpython_parser::ast::{self, Ranged};

use crate::python_contracts::ContractFailure;

fn located_failure(
    code: &'static str,
    message: impl AsRef<str>,
    source: &str,
    path: &str,
    offset: u32,
) -> ContractFailure {
    let prefix = &source.as_bytes()[..usize::try_from(offset)
        .unwrap_or(source.len())
        .min(source.len())];
    let line = 1 + prefix.iter().filter(|byte| **byte == b'\n').count();
    let column = prefix
        .iter()
        .rposition(|byte| *byte == b'\n')
        .map_or(prefix.len() + 1, |position| prefix.len() - position);
    ContractFailure {
        code,
        message: format!("{path}:{line}:{column}: {}", message.as_ref()),
    }
}

fn canonical_marker_import(import: &ast::StmtImportFrom) -> bool {
    import.level.is_none_or(|level| level == 0_u32)
        && import
            .module
            .as_ref()
            .is_some_and(|name| name.as_str() == "typing")
        && import
            .names
            .iter()
            .any(|alias| alias.name.as_str() == "TYPE_CHECKING" && alias.asname.is_none())
}

#[derive(Default)]
struct MarkerRebinding {
    offset: Option<u32>,
}

impl MarkerRebinding {
    fn bind(&mut self, name: &str, offset: u32) {
        if name == "TYPE_CHECKING" && self.offset.is_none() {
            self.offset = Some(offset);
        }
    }
}

impl Visitor for MarkerRebinding {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        if matches!(node.ctx, ast::ExprContext::Store | ast::ExprContext::Del) {
            self.bind(node.id.as_str(), node.range.start().into());
        }
    }

    fn visit_stmt_function_def(&mut self, node: ast::StmtFunctionDef) {
        self.bind(node.name.as_str(), node.range.start().into());
        self.generic_visit_stmt_function_def(node);
    }

    fn visit_stmt_class_def(&mut self, node: ast::StmtClassDef) {
        self.bind(node.name.as_str(), node.range.start().into());
        self.generic_visit_stmt_class_def(node);
    }

    fn visit_stmt_async_function_def(&mut self, node: ast::StmtAsyncFunctionDef) {
        self.bind(node.name.as_str(), node.range.start().into());
        self.generic_visit_stmt_async_function_def(node);
    }

    fn visit_stmt_try(&mut self, node: ast::StmtTry) {
        for handler in &node.handlers {
            let ast::ExceptHandler::ExceptHandler(handler) = handler;
            if let Some(name) = &handler.name {
                self.bind(name.as_str(), handler.range.start().into());
            }
        }
        self.generic_visit_stmt_try(node);
    }

    fn visit_stmt_import_from(&mut self, node: ast::StmtImportFrom) {
        for alias in &node.names {
            if alias.name.as_str() == "*" {
                self.bind("TYPE_CHECKING", alias.range.start().into());
                continue;
            }
            if canonical_marker_import(&node)
                && alias.name.as_str() == "TYPE_CHECKING"
                && alias.asname.is_none()
            {
                continue;
            }
            self.bind(
                alias.asname.as_ref().unwrap_or(&alias.name).as_str(),
                alias.range.start().into(),
            );
        }
    }

    fn visit_stmt_import(&mut self, node: ast::StmtImport) {
        for alias in node.names {
            self.bind(
                alias.asname.as_ref().map_or_else(
                    || alias.name.as_str().split('.').next().unwrap_or_default(),
                    |name| name.as_str(),
                ),
                alias.range.start().into(),
            );
        }
    }
}

/// Canonical typing.TYPE_CHECKING is false at runtime. Its import-only body is not
/// executed, but annotations remain intact and must resolve through the normal
/// source-bound type machinery. In particular, this does not define imported
/// names at runtime or turn an unresolved annotation into object/Any.
pub(super) fn normalize_type_checking(
    suite: Vec<ast::Stmt>,
    source: &str,
    path: &str,
) -> Result<Vec<ast::Stmt>, ContractFailure> {
    let has_gate = suite.iter().any(|statement| {
        matches!(statement,
        ast::Stmt::If(branch) if matches!(branch.test.as_ref(), ast::Expr::Name(name)
            if name.id.as_str() == "TYPE_CHECKING"))
    });
    if !has_gate {
        return Ok(suite);
    }
    let mut rebinding = MarkerRebinding::default();
    for statement in suite.iter().cloned() {
        rebinding.visit_stmt(statement);
    }
    if let Some(offset) = rebinding.offset {
        return Err(located_failure(
            "frontend.python.heap.type-checking-binding-reassigned",
            "TYPE_CHECKING must retain its canonical typing binding; rebinding is not a proof-only gate",
            source,
            path,
            offset,
        ));
    }
    let mut canonical = false;
    let mut result = Vec::new();
    for statement in suite {
        if let ast::Stmt::ImportFrom(import) = &statement {
            canonical |= canonical_marker_import(import);
        }
        if let ast::Stmt::If(branch) = &statement
            && matches!(branch.test.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "TYPE_CHECKING")
        {
            if !canonical {
                return Err(located_failure(
                    "frontend.python.heap.type-checking-binding-unresolved",
                    "type-only gate requires a preceding canonical `from typing import TYPE_CHECKING`",
                    source,
                    path,
                    branch.range.start().into(),
                ));
            }
            if let Some(unsupported) = branch.body.iter().find(|item| {
                !matches!(
                    item,
                    ast::Stmt::Import(_) | ast::Stmt::ImportFrom(_) | ast::Stmt::Pass(_)
                )
            }) {
                return Err(located_failure(
                    "frontend.python.heap.type-checking-body-unsupported",
                    "canonical type-only gate admits imports only; arbitrary guarded statements are not erased",
                    source,
                    path,
                    unsupported.range().start().into(),
                ));
            }
            // The else branch is real runtime code, not annotation metadata.
            result.extend(branch.orelse.iter().cloned());
        } else {
            result.push(statement);
        }
    }
    Ok(result)
}

/// Recognize the recursive annotation shape only to give an accurate refusal.
/// No alias assignment or mutable-container semantics are removed or assumed.
pub(super) fn reject_recursive_aliases(
    suite: &[ast::Stmt],
    source: &str,
    path: &str,
) -> Result<(), ContractFailure> {
    fn type_shape(expression: &ast::Expr, alias: &str) -> Option<bool> {
        match expression {
            ast::Expr::Name(name) => Some(name.id.as_str() == alias),
            ast::Expr::Constant(value) => match &value.value {
                ast::Constant::None => Some(false),
                ast::Constant::Str(name) => Some(name == alias),
                _ => None,
            },
            ast::Expr::BinOp(binary) if binary.op == ast::Operator::BitOr => {
                Some(type_shape(&binary.left, alias)? | type_shape(&binary.right, alias)?)
            }
            ast::Expr::Subscript(subscript)
                if matches!(subscript.value.as_ref(), ast::Expr::Name(name)
                    if matches!(name.id.as_str(), "list" | "dict" | "tuple" | "set" | "List" | "Dict" | "Tuple" | "Set" | "Union" | "Optional")) =>
            {
                match subscript.slice.as_ref() {
                    ast::Expr::Tuple(tuple) => {
                        tuple.elts.iter().try_fold(false, |recursive, item| {
                            Some(recursive | type_shape(item, alias)?)
                        })
                    }
                    item => type_shape(item, alias),
                }
            }
            _ => None,
        }
    }
    for statement in suite {
        let ast::Stmt::Assign(assignment) = statement else {
            continue;
        };
        let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
            continue;
        };
        if matches!(
            assignment.value.as_ref(),
            ast::Expr::BinOp(_) | ast::Expr::Subscript(_)
        ) && type_shape(&assignment.value, target.id.as_str()) == Some(true)
        {
            return Err(located_failure(
                "frontend.python.heap.recursive-type-alias-unsupported",
                format!(
                    "recursive source type alias {:?} requires recursive value and mutable-container semantics; it cannot be treated as ordinary bitwise-or, erased, or replaced by an opaque type",
                    target.id
                ),
                source,
                path,
                assignment.range.start().into(),
            ));
        }
    }
    Ok(())
}
