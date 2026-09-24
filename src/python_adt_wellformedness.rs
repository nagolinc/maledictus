//! Closed-module, source-bound well-formedness checks for Nagini algebraic data types.
//!
//! This module intentionally validates only Nagini's declaration shape.  It does not lower or
//! prove ADT semantics; a well-formed ADT must continue into the semantic frontend and is refused
//! there until that lowering exists.

use std::collections::BTreeMap;

use rustpython_ast::Ranged;
use rustpython_parser::{Parse, ast};

pub const MALFORMED_ADT: &str = "invalid.program:malformed.adt";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdtWellformednessFailure {
    pub message: String,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binding {
    AdtMarker,
    NamedTupleFactory,
    AdtModule,
    TypingModule,
    NaginiContractsPackage,
    Root(usize),
    Constructor(usize),
    Other,
}

#[derive(Clone, Debug)]
struct RootDeclaration {
    byte_offset: u32,
    line: u32,
    column: u32,
    constructors: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AdtBase {
    Marker,
    Root(usize),
    Constructor(usize),
}

/// Validate every ADT declaration in a complete Python module.
pub fn validate_adt_wellformedness(
    source: &str,
    path: &str,
) -> Result<(), AdtWellformednessFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| AdtWellformednessFailure {
        message: error.to_string(),
        byte_offset: 0,
        line: 1,
        column: 1,
    })?;
    let mut bindings = BTreeMap::<String, Binding>::new();
    let mut roots = Vec::<RootDeclaration>::new();

    for statement in &suite {
        match statement {
            ast::Stmt::Import(import) => bind_import(import, &mut bindings),
            ast::Stmt::ImportFrom(import) => bind_import_from(import, &mut bindings),
            ast::Stmt::ClassDef(class) => {
                let first_base = class
                    .bases
                    .first()
                    .and_then(|base| resolve_adt_base(base, &bindings));
                let class_binding = if let Some(first_base) = first_base {
                    validate_adt_class(class, first_base, &bindings, &mut roots, source)?
                } else {
                    Binding::Other
                };
                // The new class name becomes visible only after its bases have been evaluated.
                bindings.insert(class.name.to_string(), class_binding);
            }
            ast::Stmt::FunctionDef(function) => {
                bindings.insert(function.name.to_string(), Binding::Other);
            }
            ast::Stmt::AsyncFunctionDef(function) => {
                bindings.insert(function.name.to_string(), Binding::Other);
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    bind_target_as_other(target, &mut bindings);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                bind_target_as_other(&assignment.target, &mut bindings);
            }
            ast::Stmt::AugAssign(assignment) => {
                bind_target_as_other(&assignment.target, &mut bindings);
            }
            ast::Stmt::Delete(deletion) => {
                for target in &deletion.targets {
                    remove_target_binding(target, &mut bindings);
                }
            }
            ast::Stmt::For(loop_statement) => {
                bind_target_as_other(&loop_statement.target, &mut bindings);
            }
            ast::Stmt::AsyncFor(loop_statement) => {
                bind_target_as_other(&loop_statement.target, &mut bindings);
            }
            ast::Stmt::With(with_statement) => {
                for item in &with_statement.items {
                    if let Some(target) = item.optional_vars.as_deref() {
                        bind_target_as_other(target, &mut bindings);
                    }
                }
            }
            ast::Stmt::AsyncWith(with_statement) => {
                for item in &with_statement.items {
                    if let Some(target) = item.optional_vars.as_deref() {
                        bind_target_as_other(target, &mut bindings);
                    }
                }
            }
            _ => {}
        }
    }

    if let Some(root) = roots.iter().find(|root| root.constructors == 0) {
        return Err(AdtWellformednessFailure {
            message: "malformed algebraic datatype: ADT defining classes must declare at least one constructor"
                .to_owned(),
            byte_offset: root.byte_offset,
            line: root.line,
            column: root.column,
        });
    }
    Ok(())
}

fn validate_adt_class(
    class: &ast::StmtClassDef,
    first_base: AdtBase,
    bindings: &BTreeMap<String, Binding>,
    roots: &mut Vec<RootDeclaration>,
    source: &str,
) -> Result<Binding, AdtWellformednessFailure> {
    if class.bases.len() > 2 {
        return malformed(
            class,
            source,
            "malformed algebraic data type: superclasses can only be a class optionally followed by one NamedTuple",
        );
    }
    if !adt_body_is_empty(&class.body) {
        return malformed(
            class,
            source,
            "malformed algebraic data type: classes cannot have a body; fields belong in the NamedTuple declaration",
        );
    }

    if class.bases.len() == 2 {
        let named_tuple = &class.bases[1];
        let Some(call) = canonical_named_tuple_call(named_tuple, bindings) else {
            return malformed(
                named_tuple,
                source,
                "malformed algebraic data type: only typing.NamedTuple can define constructors",
            );
        };
        if named_tuple_declared_name(call) != Some(class.name.as_str()) {
            return malformed(
                named_tuple,
                source,
                "malformed algebraic data type: the NamedTuple name must match its constructor class",
            );
        }
        let root = match first_base {
            AdtBase::Marker => {
                return malformed(
                    class,
                    source,
                    "malformed algebraic datatype: a constructor cannot inherit directly from ADT",
                );
            }
            AdtBase::Root(root) | AdtBase::Constructor(root) => root,
        };
        roots[root].constructors += 1;
        return Ok(Binding::Constructor(root));
    }

    match first_base {
        AdtBase::Marker => {
            let root = roots.len();
            let (byte_offset, line, column) = source_position(class, source);
            roots.push(RootDeclaration {
                byte_offset,
                line,
                column,
                constructors: 0,
            });
            Ok(Binding::Root(root))
        }
        AdtBase::Root(_) | AdtBase::Constructor(_) => malformed(
            class,
            source,
            "malformed algebraic datatype: ADT defining classes must inherit directly from ADT",
        ),
    }
}

fn adt_body_is_empty(body: &[ast::Stmt]) -> bool {
    matches!(body, [ast::Stmt::Pass(_)])
        || matches!(body, [first, ast::Stmt::Pass(_)] if is_docstring(first))
}

fn is_docstring(statement: &ast::Stmt) -> bool {
    matches!(statement, ast::Stmt::Expr(expression)
        if matches!(expression.value.as_ref(), ast::Expr::Constant(constant)
            if matches!(constant.value, ast::Constant::Str(_))))
}

fn canonical_named_tuple_call<'a>(
    expression: &'a ast::Expr,
    bindings: &BTreeMap<String, Binding>,
) -> Option<&'a ast::ExprCall> {
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    let canonical = match call.func.as_ref() {
        ast::Expr::Name(name) => {
            bindings.get(name.id.as_str()) == Some(&Binding::NamedTupleFactory)
        }
        ast::Expr::Attribute(attribute) if attribute.attr.as_str() == "NamedTuple" => {
            matches!(attribute.value.as_ref(), ast::Expr::Name(name)
                if bindings.get(name.id.as_str()) == Some(&Binding::TypingModule))
        }
        _ => false,
    };
    canonical.then_some(call)
}

fn named_tuple_declared_name(call: &ast::ExprCall) -> Option<&str> {
    match call.args.first() {
        Some(ast::Expr::Constant(constant)) => match &constant.value {
            ast::Constant::Str(name) => Some(name.as_str()),
            _ => None,
        },
        _ => None,
    }
}

fn resolve_adt_base(
    expression: &ast::Expr,
    bindings: &BTreeMap<String, Binding>,
) -> Option<AdtBase> {
    let binding = match expression {
        ast::Expr::Name(name) => bindings.get(name.id.as_str()).copied(),
        ast::Expr::Attribute(attribute) if attribute.attr.as_str() == "ADT" => {
            match attribute.value.as_ref() {
                ast::Expr::Name(name)
                    if bindings.get(name.id.as_str()) == Some(&Binding::AdtModule) =>
                {
                    Some(Binding::AdtMarker)
                }
                ast::Expr::Attribute(module)
                    if module.attr.as_str() == "adt"
                        && matches!(module.value.as_ref(), ast::Expr::Name(name)
                            if bindings.get(name.id.as_str()) == Some(&Binding::NaginiContractsPackage)) =>
                {
                    Some(Binding::AdtMarker)
                }
                _ => None,
            }
        }
        _ => None,
    }?;
    match binding {
        Binding::AdtMarker => Some(AdtBase::Marker),
        Binding::Root(root) => Some(AdtBase::Root(root)),
        Binding::Constructor(root) => Some(AdtBase::Constructor(root)),
        _ => None,
    }
}

fn bind_import(import: &ast::StmtImport, bindings: &mut BTreeMap<String, Binding>) {
    for alias in &import.names {
        let imported = alias.name.as_str();
        let (local, binding) = if let Some(asname) = alias.asname.as_ref() {
            (
                asname.to_string(),
                match imported {
                    "nagini_contracts.adt" => Binding::AdtModule,
                    "typing" => Binding::TypingModule,
                    "nagini_contracts" => Binding::NaginiContractsPackage,
                    _ => Binding::Other,
                },
            )
        } else {
            let local = imported.split('.').next().unwrap_or(imported).to_owned();
            let binding =
                if imported == "nagini_contracts" || imported.starts_with("nagini_contracts.") {
                    Binding::NaginiContractsPackage
                } else if imported == "typing" {
                    Binding::TypingModule
                } else {
                    Binding::Other
                };
            (local, binding)
        };
        bindings.insert(local, binding);
    }
}

fn bind_import_from(import: &ast::StmtImportFrom, bindings: &mut BTreeMap<String, Binding>) {
    if !import.level.is_none_or(|level| level == 0_u32) {
        for alias in &import.names {
            if alias.name.as_str() != "*" {
                let local = alias.asname.as_ref().unwrap_or(&alias.name);
                bindings.insert(local.to_string(), Binding::Other);
            }
        }
        return;
    }
    let module = import.module.as_ref().map(|module| module.as_str());
    for alias in &import.names {
        let imported = alias.name.as_str();
        if imported == "*" {
            match module {
                Some("nagini_contracts.adt") => {
                    bindings.insert("ADT".to_owned(), Binding::AdtMarker);
                }
                Some("typing") => {
                    bindings.insert("NamedTuple".to_owned(), Binding::NamedTupleFactory);
                }
                _ => {}
            }
            continue;
        }
        let local = alias.asname.as_ref().unwrap_or(&alias.name).to_string();
        let binding = match (module, imported) {
            (Some("nagini_contracts.adt"), "ADT") => Binding::AdtMarker,
            (Some("nagini_contracts"), "adt") => Binding::AdtModule,
            (Some("typing"), "NamedTuple") => Binding::NamedTupleFactory,
            _ => Binding::Other,
        };
        bindings.insert(local, binding);
    }
}

fn bind_target_as_other(target: &ast::Expr, bindings: &mut BTreeMap<String, Binding>) {
    match target {
        ast::Expr::Name(name) => {
            bindings.insert(name.id.to_string(), Binding::Other);
        }
        ast::Expr::Tuple(tuple) => {
            for item in &tuple.elts {
                bind_target_as_other(item, bindings);
            }
        }
        ast::Expr::List(list) => {
            for item in &list.elts {
                bind_target_as_other(item, bindings);
            }
        }
        ast::Expr::Starred(starred) => bind_target_as_other(&starred.value, bindings),
        _ => {}
    }
}

fn remove_target_binding(target: &ast::Expr, bindings: &mut BTreeMap<String, Binding>) {
    match target {
        ast::Expr::Name(name) => {
            bindings.remove(name.id.as_str());
        }
        ast::Expr::Tuple(tuple) => {
            for item in &tuple.elts {
                remove_target_binding(item, bindings);
            }
        }
        ast::Expr::List(list) => {
            for item in &list.elts {
                remove_target_binding(item, bindings);
            }
        }
        ast::Expr::Starred(starred) => remove_target_binding(&starred.value, bindings),
        _ => {}
    }
}

fn malformed<T>(
    ranged: &impl Ranged,
    source: &str,
    message: impl Into<String>,
) -> Result<T, AdtWellformednessFailure> {
    let (byte_offset, line, column) = source_position(ranged, source);
    Err(AdtWellformednessFailure {
        message: message.into(),
        byte_offset,
        line,
        column,
    })
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
