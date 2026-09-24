//! Closed source predicate-family abstractness validation.

use std::collections::BTreeMap;

use rustpython_ast::Ranged;
use rustpython_parser::ast;

pub const PARTIALLY_ABSTRACT_PREDICATE_FAMILY: &str =
    "invalid.program:partially.abstract.predicate.family";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PredicateFamilyFailure {
    pub code: &'static str,
    pub message: String,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Debug)]
enum Binding {
    Predicate,
    ContractOnly,
    ContractModule,
    SourceClass(usize),
    Other,
}

#[derive(Clone, Copy)]
enum ContractDecorator {
    Predicate,
    ContractOnly,
}

#[derive(Clone, Debug, Default)]
struct SourceClass {
    closed: bool,
    predicate_roots: BTreeMap<String, bool>,
}

pub fn validate_predicate_families(
    suite: &[ast::Stmt],
    source: &str,
) -> Result<(), PredicateFamilyFailure> {
    let mut bindings = BTreeMap::new();
    let mut classes = Vec::new();
    for statement in suite {
        match statement {
            ast::Stmt::ImportFrom(import) => {
                bind_import_from(import, &mut bindings);
            }
            ast::Stmt::Import(import) => {
                bind_import(import, &mut bindings);
            }
            ast::Stmt::ClassDef(class) => {
                if !class.decorator_list.is_empty() {
                    // Class decorators execute arbitrary code and may replace the class value or
                    // rebind names used by later inheritance/decorator resolution.
                    bindings.clear();
                    bindings.insert(class.name.to_string(), Binding::Other);
                    continue;
                }
                let mut declaration = inherited_class(class, &bindings, &classes);
                if declaration.closed {
                    analyze_class_body(class, &bindings, &mut declaration, source)?;
                }
                let index = classes.len();
                classes.push(declaration);
                bindings.insert(class.name.to_string(), Binding::SourceClass(index));
            }
            ast::Stmt::FunctionDef(function) => {
                if !function.decorator_list.is_empty() {
                    // Unknown module-level decorators execute before this binding is installed.
                    // Forget earlier identities because their effects are not source-closed.
                    bindings.clear();
                }
                bindings.insert(function.name.to_string(), Binding::Other);
            }
            ast::Stmt::AsyncFunctionDef(function) => {
                if !function.decorator_list.is_empty() {
                    bindings.clear();
                }
                bindings.insert(function.name.to_string(), Binding::Other);
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    bind_target_other(target, &mut bindings);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                bind_target_other(&assignment.target, &mut bindings);
            }
            ast::Stmt::AugAssign(assignment) => {
                bind_target_other(&assignment.target, &mut bindings);
            }
            ast::Stmt::Delete(deletion) => {
                for target in &deletion.targets {
                    bind_target_other(target, &mut bindings);
                }
            }
            ast::Stmt::Expr(_) | ast::Stmt::Pass(_) => {}
            _ => {
                // Conditional or dynamically executed module statements can rebind any name used
                // by a later decorator or base. Forget the catalog rather than guessing.
                bindings.clear();
            }
        }
    }
    Ok(())
}

fn inherited_class(
    class: &ast::StmtClassDef,
    bindings: &BTreeMap<String, Binding>,
    classes: &[SourceClass],
) -> SourceClass {
    if !class.keywords.is_empty() {
        return SourceClass::default();
    }
    match class.bases.as_slice() {
        [] => SourceClass {
            closed: true,
            predicate_roots: BTreeMap::new(),
        },
        [ast::Expr::Name(base)] => match bindings.get(base.id.as_str()) {
            Some(Binding::SourceClass(index)) if classes[*index].closed => classes[*index].clone(),
            _ => SourceClass::default(),
        },
        _ => SourceClass::default(),
    }
}

fn analyze_class_body(
    class: &ast::StmtClassDef,
    globals: &BTreeMap<String, Binding>,
    declaration: &mut SourceClass,
    source: &str,
) -> Result<(), PredicateFamilyFailure> {
    let mut locals = BTreeMap::new();
    for statement in &class.body {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                let predicate = resolved_decorator(
                    &function.decorator_list,
                    &locals,
                    globals,
                    ContractDecorator::Predicate,
                );
                if predicate.is_some() {
                    let abstract_member = resolved_decorator(
                        &function.decorator_list,
                        &locals,
                        globals,
                        ContractDecorator::ContractOnly,
                    )
                    .is_some();
                    if let Some(root_abstract) = declaration
                        .predicate_roots
                        .get(function.name.as_str())
                        .copied()
                    {
                        if root_abstract != abstract_member {
                            return Err(failure(
                                format!(
                                    "predicate override {:?}.{} changes the root family's ContractOnly abstractness",
                                    class.name, function.name
                                ),
                                function.range().start().into(),
                                source,
                            ));
                        }
                    } else {
                        declaration
                            .predicate_roots
                            .insert(function.name.to_string(), abstract_member);
                    }
                } else {
                    declaration.predicate_roots.remove(function.name.as_str());
                }
                locals.insert(function.name.to_string(), Binding::Other);
            }
            ast::Stmt::AsyncFunctionDef(function) => {
                declaration.predicate_roots.remove(function.name.as_str());
                locals.insert(function.name.to_string(), Binding::Other);
            }
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    remove_family_target(target, declaration);
                    bind_target_other(target, &mut locals);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                remove_family_target(&assignment.target, declaration);
                bind_target_other(&assignment.target, &mut locals);
            }
            ast::Stmt::AugAssign(assignment) => {
                remove_family_target(&assignment.target, declaration);
                bind_target_other(&assignment.target, &mut locals);
            }
            ast::Stmt::ImportFrom(import) => bind_import_from(import, &mut locals),
            ast::Stmt::Import(import) => bind_import(import, &mut locals),
            ast::Stmt::Expr(_) | ast::Stmt::Pass(_) => {}
            _ => {
                declaration.closed = false;
                declaration.predicate_roots.clear();
                return Ok(());
            }
        }
    }
    Ok(())
}

fn resolved_decorator<'a>(
    decorators: &'a [ast::Expr],
    locals: &BTreeMap<String, Binding>,
    globals: &BTreeMap<String, Binding>,
    expected: ContractDecorator,
) -> Option<&'a ast::Expr> {
    decorators.iter().find(|decorator| match decorator {
        ast::Expr::Name(name) => locals
            .get(name.id.as_str())
            .or_else(|| globals.get(name.id.as_str()))
            .is_some_and(|binding| direct_decorator_matches(binding, expected)),
        ast::Expr::Attribute(attribute) => {
            let ast::Expr::Name(module) = attribute.value.as_ref() else {
                return false;
            };
            let module_is_canonical = locals
                .get(module.id.as_str())
                .or_else(|| globals.get(module.id.as_str()))
                .is_some_and(|binding| matches!(binding, Binding::ContractModule));
            module_is_canonical
                && match expected {
                    ContractDecorator::Predicate => attribute.attr.as_str() == "Predicate",
                    ContractDecorator::ContractOnly => attribute.attr.as_str() == "ContractOnly",
                }
        }
        _ => false,
    })
}

fn direct_decorator_matches(binding: &Binding, expected: ContractDecorator) -> bool {
    matches!(
        (binding, expected),
        (Binding::Predicate, ContractDecorator::Predicate)
            | (Binding::ContractOnly, ContractDecorator::ContractOnly)
    )
}

fn bind_import(import: &ast::StmtImport, bindings: &mut BTreeMap<String, Binding>) {
    for alias in &import.names {
        let local = alias.asname.as_ref().map_or_else(
            || alias.name.as_str().split('.').next().unwrap_or_default(),
            |name| name.as_str(),
        );
        let binding =
            if alias.name.as_str() == "nagini_contracts.contracts" && alias.asname.is_some() {
                Binding::ContractModule
            } else {
                Binding::Other
            };
        bindings.insert(local.to_owned(), binding);
    }
}

fn bind_import_from(import: &ast::StmtImportFrom, bindings: &mut BTreeMap<String, Binding>) {
    let contract_module = import.level.is_none_or(|level| level == 0_u32)
        && import
            .module
            .as_ref()
            .is_some_and(|module| module.as_str() == "nagini_contracts.contracts");
    for alias in &import.names {
        if alias.name.as_str() == "*" {
            // A star import may overwrite any prior local binding. Without the imported
            // module's complete, source-bound export catalog, retaining even an apparently
            // unrelated source class would invent its identity after this statement.
            bindings.clear();
            if contract_module {
                bindings.insert("Predicate".to_owned(), Binding::Predicate);
                bindings.insert("ContractOnly".to_owned(), Binding::ContractOnly);
            }
            continue;
        }
        let local = alias
            .asname
            .as_ref()
            .map_or(alias.name.as_str(), |name| name.as_str());
        let binding = if contract_module {
            match alias.name.as_str() {
                "Predicate" => Binding::Predicate,
                "ContractOnly" => Binding::ContractOnly,
                _ => Binding::Other,
            }
        } else {
            Binding::Other
        };
        bindings.insert(local.to_owned(), binding);
    }
}

fn bind_target_other(target: &ast::Expr, bindings: &mut BTreeMap<String, Binding>) {
    match target {
        ast::Expr::Name(name) => {
            bindings.insert(name.id.to_string(), Binding::Other);
        }
        ast::Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                bind_target_other(element, bindings);
            }
        }
        ast::Expr::List(list) => {
            for element in &list.elts {
                bind_target_other(element, bindings);
            }
        }
        _ => {}
    }
}

fn remove_family_target(target: &ast::Expr, declaration: &mut SourceClass) {
    match target {
        ast::Expr::Name(name) => {
            declaration.predicate_roots.remove(name.id.as_str());
        }
        ast::Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                remove_family_target(element, declaration);
            }
        }
        ast::Expr::List(list) => {
            for element in &list.elts {
                remove_family_target(element, declaration);
            }
        }
        _ => {}
    }
}

fn failure(message: String, byte_offset: u32, source: &str) -> PredicateFamilyFailure {
    let (line, column) = location(source, byte_offset);
    PredicateFamilyFailure {
        code: PARTIALLY_ABSTRACT_PREDICATE_FAMILY,
        message,
        byte_offset,
        line,
        column,
    }
}

fn location(source: &str, byte_offset: u32) -> (u32, u32) {
    let offset = usize::try_from(byte_offset)
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

#[cfg(test)]
mod tests {
    use rustpython_parser::Parse;

    use super::*;

    fn validate(source: &str) -> Result<(), PredicateFamilyFailure> {
        let suite = ast::Suite::parse(source, "predicate_family.py").unwrap();
        validate_predicate_families(&suite, source)
    }

    #[test]
    fn both_mixed_abstractness_directions_report_the_override_declaration() {
        let abstract_to_concrete = "from nagini_contracts.contracts import Predicate, ContractOnly\nclass Base:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\nclass Child(Base):\n    @Predicate\n    def ready(self) -> bool:\n        return True\n";
        let failure = validate(abstract_to_concrete).unwrap_err();
        assert_eq!(failure.code, PARTIALLY_ABSTRACT_PREDICATE_FAMILY);
        assert_eq!((failure.line, failure.column), (9, 5));

        let concrete_to_abstract = "from nagini_contracts.contracts import Predicate, ContractOnly\nclass Base:\n    @Predicate\n    def ready(self) -> bool:\n        return True\nclass Child(Base):\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\n";
        let failure = validate(concrete_to_abstract).unwrap_err();
        assert_eq!((failure.line, failure.column), (9, 5));
    }

    #[test]
    fn homogeneous_families_and_real_alias_bindings_are_valid() {
        for source in [
            "from nagini_contracts.contracts import Predicate as P, ContractOnly as C\nclass Base:\n    @P\n    @C\n    def ready(self) -> bool:\n        return True\nclass Child(Base):\n    @P\n    @C\n    def ready(self) -> bool:\n        return True\n",
            "from nagini_contracts.contracts import Predicate\nclass Base:\n    @Predicate\n    def ready(self) -> bool:\n        return True\nclass Child(Base):\n    @Predicate\n    def ready(self) -> bool:\n        return True\n",
            "import nagini_contracts.contracts as contracts\nclass Base:\n    @contracts.Predicate\n    @contracts.ContractOnly\n    def ready(self) -> bool:\n        return True\nclass Child(Base):\n    @contracts.Predicate\n    @contracts.ContractOnly\n    def ready(self) -> bool:\n        return True\n",
        ] {
            validate(source).unwrap();
        }
    }

    #[test]
    fn shadowed_decorators_and_unresolved_or_multiple_bases_are_not_guessed() {
        for source in [
            "from nagini_contracts.contracts import Predicate, ContractOnly\nclass Base:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\nPredicate = lambda value: value\nclass Child(Base):\n    @Predicate\n    def ready(self) -> bool:\n        return True\n",
            "from nagini_contracts.contracts import Predicate, ContractOnly\nclass Base:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\nclass Child(Base):\n    Predicate = lambda value: value\n    @Predicate\n    def ready(self) -> bool:\n        return True\n",
            "from nagini_contracts.contracts import Predicate, ContractOnly\nclass Base:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\nBase = object\nclass Child(Base):\n    @Predicate\n    def ready(self) -> bool:\n        return True\n",
            "from nagini_contracts.contracts import Predicate, ContractOnly\nclass Left:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\nclass Right:\n    pass\nclass Child(Left, Right):\n    @Predicate\n    def ready(self) -> bool:\n        return True\n",
            "from nagini_contracts.contracts import Predicate, ContractOnly\nclass Result:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\nfrom nagini_contracts.contracts import *\nclass Child(Result):\n    @Predicate\n    def ready(self) -> bool:\n        return True\n",
            "from nagini_contracts.contracts import Predicate, ContractOnly\nclass Base:\n    @Predicate\n    @ContractOnly\n    def ready(self) -> bool:\n        return True\n@unknown_decorator\ndef mutate_bindings() -> None:\n    pass\nclass Child(Base):\n    @Predicate\n    def ready(self) -> bool:\n        return True\n",
        ] {
            validate(source).unwrap();
        }
    }
}
