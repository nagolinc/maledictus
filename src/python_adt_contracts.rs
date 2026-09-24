//! Closed semantic lowering for canonical Nagini algebraic data types.
//!
//! ADT constructors are immutable structural products.  This lowering keeps their constructor
//! tag, declared root, and every field value, so field reads, runtime-type tests, and structural
//! equality are derived from the source declaration rather than from an opaque nominal label.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_parser::{Parse, ast};

use crate::python_contracts::ContractFailure;
use crate::python_heap_contracts::HeapContractVerification;
use crate::solver::discharge;
use crate::vc::{Obligation, ObligationExpectation, ObligationResult, Term};

#[path = "python_adt_contracts/expressions.rs"]
mod expressions;

use expressions::{bool_term, lower_expression, symbolic_value};

#[derive(Clone, Debug)]
pub(super) struct Constructor {
    pub(super) root: String,
    pub(super) fields: Vec<(String, FieldType)>,
}

#[derive(Clone, Debug)]
pub(super) enum FieldType {
    Int,
    Bool,
    Adt(String),
    Object(String),
}

#[derive(Default)]
pub(super) struct Catalog {
    pub(super) roots: BTreeSet<String>,
    pub(super) constructors: BTreeMap<String, Constructor>,
    pub(super) ordinary_classes: BTreeMap<String, OrdinaryClass>,
}

#[derive(Clone, Debug)]
pub(super) struct OrdinaryClass {
    pub(super) fields: Vec<String>,
    constructor_offset: u32,
}

pub(super) fn verify_adt_module(
    source: &str,
    path: &str,
    requested_symbols: &[String],
) -> Result<Option<HeapContractVerification>, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    if !has_canonical_adt_import(&suite) || !has_canonical_named_tuple_import(&suite) {
        return Ok(None);
    }
    let Some(catalog) = collect_catalog(&suite) else {
        return Ok(None);
    };
    if catalog.constructors.is_empty() {
        return Ok(None);
    }
    let declared = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ClassDef(class) => Some(class.name.to_string()),
            ast::Stmt::FunctionDef(function) => Some(function.name.to_string()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    if requested_symbols
        .iter()
        .any(|requested| !declared.contains(requested))
    {
        return Ok(None);
    }

    let mut obligations = Vec::new();
    let mut methods = Vec::new();
    for statement in &suite {
        match statement {
            ast::Stmt::ImportFrom(import) if supported_import(import) => {}
            ast::Stmt::ClassDef(class)
                if catalog.roots.contains(class.name.as_str())
                    || catalog.constructors.contains_key(class.name.as_str()) => {}
            ast::Stmt::ClassDef(class)
                if catalog.ordinary_classes.contains_key(class.name.as_str()) =>
            {
                let ordinary = &catalog.ordinary_classes[class.name.as_str()];
                methods.push(format!("{}.__init__", class.name));
                obligations.push(make_obligation(
                    format!("{}.__init__:function-totality:constructor", class.name),
                    Vec::new(),
                    Term::Bool { value: true },
                    source,
                    path,
                    ordinary.constructor_offset,
                ));
            }
            ast::Stmt::FunctionDef(function) => {
                if !requested_symbols.is_empty()
                    && !requested_symbols
                        .iter()
                        .any(|name| name.as_str() == function.name.as_str())
                {
                    continue;
                }
                let Some(function_obligations) = verify_function(function, &catalog, source, path)
                else {
                    return Ok(None);
                };
                methods.push(function.name.to_string());
                obligations.extend(function_obligations);
                obligations.push(make_obligation(
                    format!("{}:function-totality", function.name),
                    Vec::new(),
                    Term::Bool { value: true },
                    source,
                    path,
                    function.range.start().into(),
                ));
            }
            _ => return Ok(None),
        }
    }
    if obligations.is_empty() {
        return Ok(None);
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
    Ok(Some(HeapContractVerification {
        schema: "maledictus-python-heap-contracts/v65".to_owned(),
        path: path.to_owned(),
        methods,
        obligations,
        passed,
    }))
}

fn has_canonical_adt_import(suite: &[ast::Stmt]) -> bool {
    suite.iter().any(|statement| matches!(statement,
        ast::Stmt::ImportFrom(import)
            if import.level.is_none_or(|level| level == 0_u32)
                && import.module.as_ref().is_some_and(|module| module.as_str() == "nagini_contracts.adt")
                && import.names.iter().any(|alias| alias.name.as_str() == "ADT" && alias.asname.is_none())))
}

fn has_canonical_named_tuple_import(suite: &[ast::Stmt]) -> bool {
    suite.iter().any(|statement| matches!(statement,
        ast::Stmt::ImportFrom(import)
            if import.level.is_none_or(|level| level == 0_u32)
                && import.module.as_ref().is_some_and(|module| module.as_str() == "typing")
                && import.names.iter().any(|alias| alias.name.as_str() == "NamedTuple" && alias.asname.is_none())))
}

fn supported_import(import: &ast::StmtImportFrom) -> bool {
    import.level.is_none_or(|level| level == 0_u32)
        && import.module.as_ref().is_some_and(|module| {
            matches!(
                module.as_str(),
                "typing" | "nagini_contracts.adt" | "nagini_contracts.contracts"
            )
        })
}

fn collect_catalog(suite: &[ast::Stmt]) -> Option<Catalog> {
    let mut catalog = Catalog::default();
    for statement in suite {
        let ast::Stmt::ClassDef(class) = statement else {
            continue;
        };
        if matches!(class.bases.as_slice(), [ast::Expr::Name(base)] if base.id.as_str() == "ADT") {
            catalog.roots.insert(class.name.to_string());
        }
    }
    for statement in suite {
        let ast::Stmt::ClassDef(class) = statement else {
            continue;
        };
        if let Some(constructor) = parse_constructor(class, &catalog.roots) {
            catalog
                .constructors
                .insert(class.name.to_string(), constructor);
        } else if class.bases.is_empty() {
            let ordinary = parse_ordinary_class(class)?;
            catalog
                .ordinary_classes
                .insert(class.name.to_string(), ordinary);
        }
    }
    Some(catalog)
}

fn parse_ordinary_class(class: &ast::StmtClassDef) -> Option<OrdinaryClass> {
    let [ast::Stmt::FunctionDef(constructor)] = class.body.as_slice() else {
        return None;
    };
    if constructor.name.as_str() != "__init__" || !constructor.decorator_list.is_empty() {
        return None;
    }
    let parameters = constructor
        .args
        .args
        .iter()
        .skip(1)
        .map(|argument| argument.def.arg.to_string())
        .collect::<BTreeSet<_>>();
    let mut assigned = BTreeSet::new();
    let mut permitted = BTreeSet::new();
    for statement in &constructor.body {
        match statement {
            ast::Stmt::Assign(assignment) => {
                let [ast::Expr::Attribute(target)] = assignment.targets.as_slice() else {
                    return None;
                };
                let ast::Expr::Name(receiver) = target.value.as_ref() else {
                    return None;
                };
                let ast::Expr::Name(value) = assignment.value.as_ref() else {
                    return None;
                };
                if receiver.id.as_str() != "self"
                    || value.id.as_str() != target.attr.as_str()
                    || !parameters.contains(value.id.as_str())
                    || !assigned.insert(target.attr.to_string())
                {
                    return None;
                }
            }
            ast::Stmt::Expr(expression) => {
                let ast::Expr::Call(ensures) = expression.value.as_ref() else {
                    return None;
                };
                let ast::Expr::Name(ensures_name) = ensures.func.as_ref() else {
                    return None;
                };
                let [ast::Expr::Call(acc)] = ensures.args.as_slice() else {
                    return None;
                };
                let ast::Expr::Name(acc_name) = acc.func.as_ref() else {
                    return None;
                };
                let [ast::Expr::Attribute(field)] = acc.args.as_slice() else {
                    return None;
                };
                if ensures_name.id.as_str() != "Ensures"
                    || acc_name.id.as_str() != "Acc"
                    || !matches!(field.value.as_ref(), ast::Expr::Name(receiver)
                        if receiver.id.as_str() == "self")
                    || !permitted.insert(field.attr.to_string())
                {
                    return None;
                }
            }
            _ => return None,
        }
    }
    if assigned.is_empty() || assigned != permitted || assigned != parameters {
        return None;
    }
    Some(OrdinaryClass {
        fields: constructor
            .args
            .args
            .iter()
            .skip(1)
            .map(|argument| argument.def.arg.to_string())
            .collect(),
        constructor_offset: constructor.range.start().into(),
    })
}

fn parse_constructor(class: &ast::StmtClassDef, roots: &BTreeSet<String>) -> Option<Constructor> {
    let [ast::Expr::Name(root), ast::Expr::Call(product)] = class.bases.as_slice() else {
        return None;
    };
    if !roots.contains(root.id.as_str())
        || !matches!(product.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "NamedTuple")
        || product.args.len() != 2
    {
        return None;
    }
    let ast::Expr::Constant(name) = &product.args[0] else {
        return None;
    };
    if name.value != ast::Constant::Str(class.name.to_string()) {
        return None;
    }
    let ast::Expr::List(field_list) = &product.args[1] else {
        return None;
    };
    let mut fields = Vec::new();
    for field in &field_list.elts {
        let ast::Expr::Tuple(pair) = field else {
            return None;
        };
        let [ast::Expr::Constant(name), ast::Expr::Name(annotation)] = pair.elts.as_slice() else {
            return None;
        };
        let ast::Constant::Str(name) = &name.value else {
            return None;
        };
        let field_type = match annotation.id.as_str() {
            "int" => FieldType::Int,
            "bool" => FieldType::Bool,
            other if roots.contains(other) => FieldType::Adt(other.to_owned()),
            other => FieldType::Object(other.to_owned()),
        };
        fields.push((name.clone(), field_type));
    }
    Some(Constructor {
        root: root.id.to_string(),
        fields,
    })
}

fn verify_function(
    function: &ast::StmtFunctionDef,
    catalog: &Catalog,
    source: &str,
    path: &str,
) -> Option<Vec<Obligation>> {
    let mut environment = BTreeMap::new();
    for argument in &function.args.args {
        let annotation = argument.def.annotation.as_deref()?;
        let ast::Expr::Name(annotation) = annotation else {
            return None;
        };
        let value = symbolic_value(
            annotation.id.as_str(),
            &format!("{}::{}", function.name, argument.def.arg),
            catalog,
        )?;
        environment.insert(argument.def.arg.to_string(), value);
    }
    let mut assumptions = Vec::new();
    let mut obligations = Vec::new();
    for statement in &function.body {
        match statement {
            ast::Stmt::Assign(assignment) => {
                let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
                    return None;
                };
                let value = lower_expression(&assignment.value, &environment, catalog)?;
                environment.insert(target.id.to_string(), value);
            }
            ast::Stmt::Assert(assertion) => {
                let conclusion =
                    bool_term(lower_expression(&assertion.test, &environment, catalog)?)?;
                obligations.push(make_obligation(
                    format!(
                        "{}:assert:{}",
                        function.name,
                        u32::from(assertion.range.start())
                    ),
                    assumptions.clone(),
                    conclusion,
                    source,
                    path,
                    assertion.range.start().into(),
                ));
            }
            ast::Stmt::Expr(expression) => {
                let ast::Expr::Call(call) = expression.value.as_ref() else {
                    return None;
                };
                let ast::Expr::Name(callee) = call.func.as_ref() else {
                    return None;
                };
                let [argument] = call.args.as_slice() else {
                    return None;
                };
                match callee.id.as_str() {
                    "Requires" => assumptions.push(bool_term(lower_expression(
                        argument,
                        &environment,
                        catalog,
                    )?)?),
                    "Ensures" => obligations.push(make_obligation(
                        format!(
                            "{}:postcondition:{}",
                            function.name,
                            u32::from(expression.range.start())
                        ),
                        assumptions.clone(),
                        bool_term(lower_expression(argument, &environment, catalog)?)?,
                        source,
                        path,
                        expression.range.start().into(),
                    )),
                    "Assert" => obligations.push(make_obligation(
                        format!(
                            "{}:assert:{}",
                            function.name,
                            u32::from(expression.range.start())
                        ),
                        assumptions.clone(),
                        bool_term(lower_expression(argument, &environment, catalog)?)?,
                        source,
                        path,
                        expression.range.start().into(),
                    )),
                    _ => return None,
                }
            }
            ast::Stmt::Return(returned) => {
                if let Some(value) = returned.value.as_deref() {
                    lower_expression(value, &environment, catalog)?;
                }
            }
            _ => return None,
        }
    }
    Some(obligations)
}

fn make_obligation(
    id: String,
    assumptions: Vec<Term>,
    conclusion: Term,
    source: &str,
    path: &str,
    offset: u32,
) -> Obligation {
    let prefix = &source[..usize::try_from(offset)
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

#[cfg(test)]
mod tests {
    use super::verify_adt_module;

    const PREFIX: &str = "from nagini_contracts.adt import ADT\nfrom nagini_contracts.contracts import *\nfrom typing import NamedTuple\nclass Root(ADT):\n    pass\nclass Item(Root, NamedTuple('Item', [('value', int)])):\n    pass\n";

    #[test]
    fn declarations_without_a_verified_function_do_not_issue_vacuously() {
        assert!(
            verify_adt_module(PREFIX, "declarations.py", &[])
                .unwrap()
                .is_none()
        );
        assert!(
            verify_adt_module(PREFIX, "selection.py", &["Item".to_owned()])
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn ordinary_object_permissions_are_never_assumed_from_acc_syntax() {
        let unsafe_constructor = format!(
            "{PREFIX}class Box:\n    def __init__(self, value: int) -> None:\n        Ensures(Acc(self.value))\n\ndef run() -> None:\n    return\n"
        );
        assert!(
            verify_adt_module(&unsafe_constructor, "unsafe_constructor.py", &[])
                .unwrap()
                .is_none()
        );

        let ordinary_acc = format!(
            "{PREFIX}def run(item: Item) -> bool:\n    Requires(Acc(item.value))\n    return True\n"
        );
        assert!(
            verify_adt_module(&ordinary_acc, "ordinary_acc.py", &[])
                .unwrap()
                .is_none()
        );
    }
}
