//! Closed production lowering for canonical Python `enum.IntEnum` programs.
//!
//! An IntEnum value deliberately retains both its finite class descriptor and its integer
//! projection.  Numeric operations use the projection; `is` uses enum singleton identity.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_parser::{Parse, ast};

use crate::python_contracts::ContractFailure;
use crate::python_heap_contracts::HeapContractVerification;
use crate::solver::discharge;
use crate::vc::{
    IntEnumDescriptor, Obligation, ObligationExpectation, ObligationResult, Sort, Term,
};

pub(super) fn verify_int_enum_module(
    source: &str,
    path: &str,
    requested_symbols: &[String],
) -> Result<Option<HeapContractVerification>, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    if !suite.iter().any(is_canonical_int_enum_import) {
        return Ok(None);
    }
    validate_imports(&suite)?;
    validate_source_order_and_bindings(&suite)?;
    let descriptors = collect_descriptors(&suite)?;
    if descriptors.is_empty() {
        return fail(
            "frontend.python.int-enum.declaration-missing",
            "canonical IntEnum import requires at least one bounded source enum declaration",
        );
    }
    validate_dataclasses(&suite, &descriptors)?;

    let declared_symbols = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::ClassDef(class) => Some(class.name.to_string()),
            ast::Stmt::FunctionDef(function) => Some(function.name.to_string()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    for requested in requested_symbols {
        if !declared_symbols.contains(requested) {
            return fail(
                "frontend.python.int-enum.requested-symbol-unresolved",
                format!(
                    "requested IntEnum module symbol {requested:?} is not a verified class or function"
                ),
            );
        }
    }

    let mut obligations = Vec::new();
    let mut methods = Vec::new();
    for statement in &suite {
        match statement {
            ast::Stmt::ImportFrom(_) => {}
            ast::Stmt::ClassDef(_) => {}
            ast::Stmt::FunctionDef(function) => {
                methods.push(function.name.to_string());
                verify_function(function, &descriptors, source, path, &mut obligations)?;
            }
            _ => {
                return fail(
                    "frontend.python.int-enum.module-statement-unsupported",
                    format!(
                        "top-level statement {statement:?} is outside the closed IntEnum module"
                    ),
                );
            }
        }
    }
    let results = obligations
        .iter()
        .map(|obligation| {
            discharge(obligation).map_err(|message| ContractFailure {
                code: "solver.translation-failed",
                message,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let passed = results.iter().all(ObligationResult::satisfied);
    Ok(Some(HeapContractVerification {
        schema: "maledictus-python-heap-contracts/v65".to_owned(),
        path: path.to_owned(),
        methods,
        obligations: results,
        passed,
    }))
}

fn validate_imports(suite: &[ast::Stmt]) -> Result<(), ContractFailure> {
    let mut int_enum_imports = 0_usize;
    for statement in suite {
        if matches!(statement, ast::Stmt::Import(_)) {
            return fail(
                "frontend.python.int-enum.import-unsupported",
                "IntEnum modules require exact from-imports; ordinary import statements are unsupported",
            );
        }
        let ast::Stmt::ImportFrom(import) = statement else {
            continue;
        };
        let Some(module) = import.module.as_ref() else {
            return fail(
                "frontend.python.int-enum.relative-import-unsupported",
                "IntEnum modules require absolute imports",
            );
        };
        match module.as_str() {
            "enum" => {
                int_enum_imports += 1;
                if import.level.is_some_and(|level| level != 0_u32)
                    || !matches!(import.names.as_slice(), [alias]
                        if alias.name.as_str() == "IntEnum" && alias.asname.is_none())
                {
                    return fail(
                        "frontend.python.int-enum.import-unsupported",
                        "only canonical `from enum import IntEnum` is supported",
                    );
                }
            }
            "nagini_contracts.contracts" => {
                if !matches!(import.names.as_slice(), [alias]
                    if alias.name.as_str() == "*" && alias.asname.is_none())
                {
                    return fail(
                        "frontend.python.int-enum.contract-import-unsupported",
                        "the closed IntEnum verifier requires the canonical contracts star import",
                    );
                }
            }
            "dataclasses" => {
                if !matches!(import.names.as_slice(), [alias]
                    if alias.name.as_str() == "dataclass" && alias.asname.is_none())
                {
                    return fail(
                        "frontend.python.int-enum.dataclass-import-unsupported",
                        "only canonical `from dataclasses import dataclass` is supported",
                    );
                }
            }
            _ => {
                return fail(
                    "frontend.python.int-enum.import-unsupported",
                    format!("import from {module:?} is outside the closed IntEnum module"),
                );
            }
        }
    }
    if int_enum_imports != 1 {
        return fail(
            "frontend.python.int-enum.import-ambiguous",
            "exactly one canonical IntEnum import is required",
        );
    }
    Ok(())
}

fn is_canonical_int_enum_import(statement: &ast::Stmt) -> bool {
    matches!(statement, ast::Stmt::ImportFrom(import)
        if import.level.is_none_or(|level| level == 0_u32)
            && import.module.as_ref().is_some_and(|module| module.as_str() == "enum")
            && matches!(import.names.as_slice(), [alias]
                if alias.name.as_str() == "IntEnum" && alias.asname.is_none()))
}

fn validate_source_order_and_bindings(suite: &[ast::Stmt]) -> Result<(), ContractFailure> {
    let protected = BTreeSet::from(["IntEnum", "int", "Requires", "dataclass"]);
    let mut bindings = BTreeSet::new();
    let mut enum_classes = BTreeSet::new();
    let mut int_enum_available = false;
    let mut contracts_available = false;
    let mut dataclass_available = false;
    for statement in suite {
        match statement {
            ast::Stmt::ImportFrom(import) => match import.module.as_ref().map(|name| name.as_str())
            {
                Some("enum") => {
                    if !bindings.insert("IntEnum".to_owned()) {
                        return fail(
                            "frontend.python.int-enum.binding-redefined",
                            "IntEnum is bound more than once",
                        );
                    }
                    int_enum_available = true;
                }
                Some("nagini_contracts.contracts") => {
                    if !bindings.insert("Requires".to_owned()) {
                        return fail(
                            "frontend.python.int-enum.binding-redefined",
                            "Requires is bound more than once",
                        );
                    }
                    contracts_available = true;
                }
                Some("dataclasses") => {
                    if !bindings.insert("dataclass".to_owned()) {
                        return fail(
                            "frontend.python.int-enum.binding-redefined",
                            "dataclass is bound more than once",
                        );
                    }
                    dataclass_available = true;
                }
                _ => {}
            },
            ast::Stmt::ClassDef(class) => {
                let name = class.name.as_str();
                if protected.contains(name) || !bindings.insert(name.to_owned()) {
                    return fail(
                        "frontend.python.int-enum.binding-redefined",
                        format!("class name {name:?} rebinds a protected or existing module name"),
                    );
                }
                let exact_int_enum = matches!(class.bases.as_slice(), [ast::Expr::Name(base)] if base.id.as_str() == "IntEnum");
                if exact_int_enum {
                    if !int_enum_available {
                        return fail(
                            "frontend.python.int-enum.definition-order",
                            format!(
                                "enum class {name:?} is defined before canonical IntEnum is available"
                            ),
                        );
                    }
                    enum_classes.insert(name.to_owned());
                    continue;
                }
                if !class.decorator_list.is_empty() {
                    if !dataclass_available {
                        return fail(
                            "frontend.python.int-enum.definition-order",
                            format!(
                                "dataclass {name:?} is defined before canonical dataclass is available"
                            ),
                        );
                    }
                    for body in &class.body {
                        let ast::Stmt::AnnAssign(field) = body else {
                            continue;
                        };
                        let ast::Expr::Name(annotation) = field.annotation.as_ref() else {
                            continue;
                        };
                        if !enum_classes.contains(annotation.id.as_str()) {
                            return fail(
                                "frontend.python.int-enum.definition-order",
                                format!(
                                    "dataclass {name:?} uses IntEnum annotation {:?} before that enum is defined",
                                    annotation.id
                                ),
                            );
                        }
                    }
                }
            }
            ast::Stmt::FunctionDef(function) => {
                let name = function.name.as_str();
                if protected.contains(name) || !bindings.insert(name.to_owned()) {
                    return fail(
                        "frontend.python.int-enum.binding-redefined",
                        format!(
                            "function name {name:?} rebinds a protected or existing module name"
                        ),
                    );
                }
                for argument in function.args.posonlyargs.iter().chain(&function.args.args) {
                    if let Some(ast::Expr::Name(annotation)) = argument.def.annotation.as_deref()
                        && !enum_classes.contains(annotation.id.as_str())
                    {
                        return fail(
                            "frontend.python.int-enum.definition-order",
                            format!(
                                "function {name:?} uses annotation {:?} before that IntEnum is defined",
                                annotation.id
                            ),
                        );
                    }
                }
                if function.body.iter().any(|statement| matches!(statement, ast::Stmt::Expr(expression) if is_requires(&expression.value)))
                    && !contracts_available
                {
                    return fail("frontend.python.int-enum.requires-unbound", format!("function {name:?} uses Requires before the canonical contracts import"));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn collect_descriptors(
    suite: &[ast::Stmt],
) -> Result<BTreeMap<String, IntEnumDescriptor>, ContractFailure> {
    let mut descriptors = BTreeMap::new();
    for statement in suite {
        let ast::Stmt::ClassDef(class) = statement else {
            continue;
        };
        let exact_int_enum = matches!(class.bases.as_slice(), [ast::Expr::Name(base)] if base.id.as_str() == "IntEnum");
        if !exact_int_enum {
            if class.bases.iter().any(|base| {
                matches!(base, ast::Expr::Name(name)
                if name.id.as_str() == "IntEnum" || descriptors.contains_key(name.id.as_str()))
            }) {
                return fail(
                    "frontend.python.int-enum.inheritance-unsupported",
                    format!(
                        "enum class {:?} must directly and solely extend IntEnum; memberful enums cannot be extended",
                        class.name
                    ),
                );
            }
            continue;
        }
        if !class.decorator_list.is_empty()
            || !class.keywords.is_empty()
            || !class.type_params.is_empty()
        {
            return fail(
                "frontend.python.int-enum.class-options-unsupported",
                format!(
                    "enum class {:?} uses unsupported decorators, keywords, or type parameters",
                    class.name
                ),
            );
        }
        let mut members = Vec::new();
        let mut names = BTreeSet::new();
        let mut values = BTreeSet::new();
        for body in &class.body {
            let ast::Stmt::Assign(assignment) = body else {
                return fail(
                    "frontend.python.int-enum.body-unsupported",
                    format!(
                        "enum class {:?} may contain only direct integer member assignments",
                        class.name
                    ),
                );
            };
            let [ast::Expr::Name(name)] = assignment.targets.as_slice() else {
                return fail(
                    "frontend.python.int-enum.member-target-unsupported",
                    "IntEnum members require direct names",
                );
            };
            if !safe_int_enum_member_name(name.id.as_str()) {
                return fail(
                    "frontend.python.int-enum.member-name-unsupported",
                    format!(
                        "enum member name {:?} is outside the safe ordinary identifier subset",
                        name.id
                    ),
                );
            }
            let value = integer_literal(&assignment.value)?;
            if !names.insert(name.id.to_string()) || !values.insert(value) {
                return fail(
                    "frontend.python.int-enum.alias-unsupported",
                    format!(
                        "enum class {:?} requires unique member names and values",
                        class.name
                    ),
                );
            }
            members.push((name.id.to_string(), value));
        }
        if members.is_empty() {
            return fail(
                "frontend.python.int-enum.empty-unsupported",
                format!("enum class {:?} requires at least one member", class.name),
            );
        }
        let descriptor = IntEnumDescriptor {
            class: class.name.to_string(),
            members,
        };
        descriptors.insert(class.name.to_string(), descriptor);
    }
    Ok(descriptors)
}

fn safe_int_enum_member_name(name: &str) -> bool {
    let mut characters = name.chars();
    characters
        .next()
        .is_some_and(|first| first.is_ascii_lowercase())
        && characters.all(|character| {
            character.is_ascii_lowercase() || character.is_ascii_digit() || character == '_'
        })
        && !name.ends_with('_')
        && !name.contains("__")
        && !matches!(name, "mro" | "name" | "value")
}

fn integer_literal(expression: &ast::Expr) -> Result<i64, ContractFailure> {
    match expression {
        ast::Expr::Constant(constant) if matches!(constant.value, ast::Constant::Int(_)) => {
            let ast::Constant::Int(value) = &constant.value else {
                unreachable!()
            };
            value.to_string().parse().map_err(|_| ContractFailure {
                code: "frontend.python.integer.out-of-range",
                message: format!("integer literal {value} exceeds i64"),
            })
        }
        ast::Expr::UnaryOp(unary) if unary.op == ast::UnaryOp::USub => {
            integer_literal(&unary.operand)?
                .checked_neg()
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.integer.out-of-range",
                    message: "negative integer literal exceeds i64".to_owned(),
                })
        }
        _ => fail(
            "frontend.python.int-enum.member-value-unsupported",
            "IntEnum members require exact integer literals",
        ),
    }
}

fn validate_dataclasses(
    suite: &[ast::Stmt],
    descriptors: &BTreeMap<String, IntEnumDescriptor>,
) -> Result<(), ContractFailure> {
    for statement in suite {
        let ast::Stmt::ClassDef(class) = statement else {
            continue;
        };
        if descriptors.contains_key(class.name.as_str()) {
            continue;
        }
        let is_dataclass = !class.decorator_list.is_empty();
        if !is_dataclass {
            return fail(
                "frontend.python.int-enum.non-enum-class-unsupported",
                format!(
                    "class {:?} must be an exact dataclass or IntEnum",
                    class.name
                ),
            );
        }
        let frozen = match class.decorator_list.as_slice() {
            [ast::Expr::Name(name)] if name.id.as_str() == "dataclass" => false,
            [ast::Expr::Call(call)]
                if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "dataclass")
                    && call.args.is_empty()
                    && matches!(call.keywords.as_slice(), [keyword]
                    if keyword.arg.as_ref().is_some_and(|name| name.as_str() == "frozen")
                    && matches!(keyword.value, ast::Expr::Constant(ref constant) if constant.value == ast::Constant::Bool(true))) =>
            {
                true
            }
            _ => {
                return fail(
                    "frontend.python.int-enum.dataclass-options-unsupported",
                    format!(
                        "dataclass {:?} supports only canonical @dataclass or @dataclass(frozen=True)",
                        class.name
                    ),
                );
            }
        };
        let _ = frozen;
        if !class.bases.is_empty() || !class.keywords.is_empty() || !class.type_params.is_empty() {
            return fail(
                "frontend.python.int-enum.dataclass-inheritance-unsupported",
                "IntEnum-valued dataclasses do not support inheritance or class options",
            );
        }
        for body in &class.body {
            let ast::Stmt::AnnAssign(field) = body else {
                return fail(
                    "frontend.python.int-enum.dataclass-body-unsupported",
                    "IntEnum-valued dataclasses may contain only annotated fields",
                );
            };
            let ast::Expr::Name(annotation) = field.annotation.as_ref() else {
                return fail(
                    "frontend.python.int-enum.dataclass-field-type-unsupported",
                    "dataclass field requires a direct IntEnum annotation",
                );
            };
            let Some(descriptor) = descriptors.get(annotation.id.as_str()) else {
                return fail(
                    "frontend.python.int-enum.dataclass-field-type-unsupported",
                    format!(
                        "dataclass field annotation {:?} is not a local IntEnum",
                        annotation.id
                    ),
                );
            };
            let Some(default) = field.value.as_deref() else {
                return fail(
                    "frontend.python.int-enum.dataclass-default-required",
                    "bounded IntEnum dataclass fields require an explicit member default",
                );
            };
            let _ = enum_member(default, descriptors)?
                .filter(|term| enum_descriptor(term) == Some(descriptor))
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.int-enum.dataclass-default-mismatch",
                    message: format!(
                        "dataclass field default must be a member of {:?}",
                        descriptor.class
                    ),
                })?;
        }
    }
    Ok(())
}

fn verify_function(
    function: &ast::StmtFunctionDef,
    descriptors: &BTreeMap<String, IntEnumDescriptor>,
    source: &str,
    path: &str,
    obligations: &mut Vec<Obligation>,
) -> Result<(), ContractFailure> {
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || function.args.vararg.is_some()
        || function.args.kwarg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Constant(value)) if value.value == ast::Constant::None)
    {
        return fail(
            "frontend.python.int-enum.function-signature-unsupported",
            format!(
                "function {:?} is outside the closed IntEnum signature fragment",
                function.name
            ),
        );
    }
    let mut environment = BTreeMap::new();
    let mut assumptions = Vec::new();
    for argument in function.args.posonlyargs.iter().chain(&function.args.args) {
        if argument.default.is_some() {
            return fail(
                "frontend.python.int-enum.parameter-default-unsupported",
                "IntEnum parameters do not support defaults",
            );
        }
        let Some(ast::Expr::Name(annotation)) = argument.def.annotation.as_deref() else {
            return fail(
                "frontend.python.int-enum.parameter-type-unsupported",
                "parameters require a direct local IntEnum annotation",
            );
        };
        let Some(descriptor) = descriptors.get(annotation.id.as_str()) else {
            return fail(
                "frontend.python.int-enum.parameter-type-unsupported",
                format!(
                    "parameter annotation {:?} is not a local IntEnum",
                    annotation.id
                ),
            );
        };
        if descriptors.contains_key(argument.def.arg.as_str())
            || matches!(
                argument.def.arg.as_str(),
                "IntEnum" | "int" | "Requires" | "dataclass"
            )
        {
            return fail(
                "frontend.python.int-enum.protected-name-rebound",
                format!(
                    "parameter {:?} rebinds a protected IntEnum semantic name",
                    argument.def.arg
                ),
            );
        }
        let value = Term::IntEnumValue {
            descriptor: descriptor.clone(),
            value: Box::new(Term::Variable {
                name: format!("{}::{}", function.name, argument.def.arg),
                sort: Sort::Int,
            }),
        };
        assumptions.push(Term::IntEnumDomain {
            value: Box::new(value.clone()),
        });
        environment.insert(argument.def.arg.to_string(), value);
    }
    let mut executable_seen = false;
    for statement in &function.body {
        match statement {
            ast::Stmt::Assign(assignment) => {
                let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
                    return fail("frontend.python.int-enum.assignment-target-unsupported", "IntEnum locals require direct name assignment");
                };
                if descriptors.contains_key(target.id.as_str())
                    || matches!(target.id.as_str(), "IntEnum" | "int" | "Requires" | "dataclass")
                {
                    return fail(
                        "frontend.python.int-enum.protected-name-rebound",
                        format!("assignment rebinds protected IntEnum semantic name {:?}", target.id),
                    );
                }
                let value = lower_expression(
                    &assignment.value,
                    &environment,
                    &mut LoweringContext {
                        descriptors,
                        assumptions: &assumptions,
                        obligations,
                        source,
                        path,
                    },
                )?;
                environment.insert(target.id.to_string(), value);
            }
            ast::Stmt::Assert(assertion) => {
                let conclusion = lower_expression(
                    &assertion.test,
                    &environment,
                    &mut LoweringContext {
                        descriptors,
                        assumptions: &assumptions,
                        obligations,
                        source,
                        path,
                    },
                )?;
                require_bool(&conclusion)?;
                obligations.push(make_obligation(format!("{}:assert:{}", function.name, u32::from(assertion.range.start())), assumptions.clone(), conclusion, path, source, assertion.range.start().into()));
            }
            ast::Stmt::Expr(expression) if is_requires(&expression.value) => {
                if executable_seen {
                    return fail(
                        "frontend.python.int-enum.requires-prefix",
                        "Requires clauses must form one contiguous prefix before executable statements",
                    );
                }
                let ast::Expr::Call(call) = expression.value.as_ref() else { unreachable!() };
                let premise = lower_expression(
                    &call.args[0],
                    &environment,
                    &mut LoweringContext {
                        descriptors,
                        assumptions: &assumptions,
                        obligations,
                        source,
                        path,
                    },
                )?;
                require_bool(&premise)?;
                assumptions.push(premise);
            }
            ast::Stmt::Return(returned) if returned.value.as_deref().is_none_or(|value| matches!(value, ast::Expr::Constant(constant) if constant.value == ast::Constant::None)) => {}
            _ => return fail("frontend.python.int-enum.statement-unsupported", format!("function {:?} contains a statement outside the closed IntEnum fragment", function.name)),
        }
        if !matches!(statement, ast::Stmt::Expr(expression) if is_requires(&expression.value)) {
            executable_seen = true;
        }
    }
    Ok(())
}

fn is_requires(expression: &ast::Expr) -> bool {
    matches!(expression, ast::Expr::Call(call)
        if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Requires")
            && call.args.len() == 1 && call.keywords.is_empty())
}

struct LoweringContext<'a> {
    descriptors: &'a BTreeMap<String, IntEnumDescriptor>,
    assumptions: &'a [Term],
    obligations: &'a mut Vec<Obligation>,
    source: &'a str,
    path: &'a str,
}

fn lower_expression(
    expression: &ast::Expr,
    environment: &BTreeMap<String, Term>,
    context: &mut LoweringContext<'_>,
) -> Result<Term, ContractFailure> {
    if let Some(member) = enum_member(expression, context.descriptors)? {
        return Ok(member);
    }
    match expression {
        ast::Expr::Name(name) => {
            environment
                .get(name.id.as_str())
                .cloned()
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.int-enum.name-unresolved",
                    message: format!("IntEnum expression name {:?} is unavailable", name.id),
                })
        }
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Int(value) => Ok(Term::Int {
                value: value.to_string().parse().map_err(|_| ContractFailure {
                    code: "frontend.python.integer.out-of-range",
                    message: format!("integer literal {value} exceeds i64"),
                })?,
            }),
            ast::Constant::Bool(value) => Ok(Term::Bool { value: *value }),
            _ => fail(
                "frontend.python.int-enum.literal-unsupported",
                "only integer and boolean literals are supported in IntEnum expressions",
            ),
        },
        ast::Expr::Call(call) if call.keywords.is_empty() && call.args.len() == 1 => {
            let ast::Expr::Name(function) = call.func.as_ref() else {
                return fail(
                    "frontend.python.int-enum.call-unsupported",
                    "IntEnum calls require a direct canonical name",
                );
            };
            if function.id.as_str() == "int" {
                let value = lower_expression(&call.args[0], environment, context)?;
                if enum_descriptor(&value).is_none() {
                    return fail(
                        "frontend.python.int-enum.projection-type-mismatch",
                        "int(...) requires an IntEnum value in the closed IntEnum fragment",
                    );
                }
                return Ok(Term::IntEnumProjection {
                    value: Box::new(value),
                });
            }
            let Some(descriptor) = context.descriptors.get(function.id.as_str()) else {
                return fail(
                    "frontend.python.int-enum.call-unsupported",
                    format!("call target {:?} is not a local IntEnum", function.id),
                );
            };
            let argument = lower_expression(&call.args[0], environment, context)?;
            let argument = numeric_projection(argument)?;
            let value = Term::IntEnumValue {
                descriptor: descriptor.clone(),
                value: Box::new(argument),
            };
            let domain = Term::IntEnumDomain {
                value: Box::new(value.clone()),
            };
            let check = make_obligation(
                format!(
                    "int-enum-constructor:{}:{}",
                    descriptor.class,
                    u32::from(call.range.start())
                ),
                context.assumptions.to_vec(),
                domain.clone(),
                context.path,
                context.source,
                call.range.start().into(),
            );
            let result = discharge(&check).map_err(|message| ContractFailure {
                code: "solver.translation-failed",
                message,
            })?;
            context.obligations.push(check);
            if !result.satisfied() {
                return fail(
                    "frontend.python.int-enum.constructor-domain-unproved",
                    format!(
                        "construction of {:?} may raise ValueError outside its finite member domain",
                        descriptor.class
                    ),
                );
            }
            Ok(value)
        }
        ast::Expr::Compare(comparison)
            if comparison.ops.len() == 1 && comparison.comparators.len() == 1 =>
        {
            let left = lower_expression(&comparison.left, environment, context)?;
            let right = lower_expression(&comparison.comparators[0], environment, context)?;
            lower_comparison(comparison.ops[0], left, right)
        }
        ast::Expr::BoolOp(operation)
            if operation.op == ast::BoolOp::Or && !operation.values.is_empty() =>
        {
            let mut values = Vec::new();
            for value in &operation.values {
                let value = lower_expression(value, environment, context)?;
                require_bool(&value)?;
                values.push(value);
            }
            Ok(Term::Or { values })
        }
        _ => fail(
            "frontend.python.int-enum.expression-unsupported",
            format!("expression {expression:?} is outside the closed IntEnum fragment"),
        ),
    }
}

fn enum_member(
    expression: &ast::Expr,
    descriptors: &BTreeMap<String, IntEnumDescriptor>,
) -> Result<Option<Term>, ContractFailure> {
    let ast::Expr::Attribute(attribute) = expression else {
        return Ok(None);
    };
    let ast::Expr::Name(owner) = attribute.value.as_ref() else {
        return Ok(None);
    };
    let Some(descriptor) = descriptors.get(owner.id.as_str()) else {
        return Ok(None);
    };
    let Some((_, value)) = descriptor
        .members
        .iter()
        .find(|(name, _)| name == attribute.attr.as_str())
    else {
        return fail(
            "frontend.python.int-enum.member-unknown",
            format!("enum {:?} has no member {:?}", owner.id, attribute.attr),
        );
    };
    Ok(Some(Term::IntEnumValue {
        descriptor: descriptor.clone(),
        value: Box::new(Term::Int { value: *value }),
    }))
}

fn enum_descriptor(term: &Term) -> Option<&IntEnumDescriptor> {
    match term {
        Term::IntEnumValue { descriptor, .. } => Some(descriptor),
        _ => None,
    }
}

fn numeric_projection(term: Term) -> Result<Term, ContractFailure> {
    match term {
        Term::IntEnumValue { .. } => Ok(Term::IntEnumProjection {
            value: Box::new(term),
        }),
        Term::Int { .. } | Term::IntEnumProjection { .. } => Ok(term),
        Term::Bool { value } => Ok(Term::Int {
            value: i64::from(value),
        }),
        _ => fail(
            "frontend.python.int-enum.numeric-type-mismatch",
            "IntEnum numeric operation requires an IntEnum, int, or bool",
        ),
    }
}

fn lower_comparison(
    operation: ast::CmpOp,
    left: Term,
    right: Term,
) -> Result<Term, ContractFailure> {
    if matches!(operation, ast::CmpOp::Is | ast::CmpOp::IsNot) {
        if enum_descriptor(&left).is_none() || enum_descriptor(&right).is_none() {
            return fail(
                "frontend.python.int-enum.identity-type-mismatch",
                "IntEnum identity requires two descriptor-carrying enum values",
            );
        }
        let identity = Term::IntEnumIdentity {
            left: Box::new(left),
            right: Box::new(right),
        };
        return Ok(if operation == ast::CmpOp::Is {
            identity
        } else {
            Term::Not {
                value: Box::new(identity),
            }
        });
    }
    let left = numeric_projection(left)?;
    let right = numeric_projection(right)?;
    let comparison = match operation {
        ast::CmpOp::Eq | ast::CmpOp::NotEq => Term::Equal {
            left: Box::new(left),
            right: Box::new(right),
        },
        ast::CmpOp::Lt => Term::Less {
            left: Box::new(left),
            right: Box::new(right),
        },
        ast::CmpOp::LtE => Term::LessEqual {
            left: Box::new(left),
            right: Box::new(right),
        },
        ast::CmpOp::Gt => Term::Greater {
            left: Box::new(left),
            right: Box::new(right),
        },
        ast::CmpOp::GtE => Term::GreaterEqual {
            left: Box::new(left),
            right: Box::new(right),
        },
        _ => {
            return fail(
                "frontend.python.int-enum.comparison-unsupported",
                "IntEnum comparison operator is unsupported",
            );
        }
    };
    Ok(if operation == ast::CmpOp::NotEq {
        Term::Not {
            value: Box::new(comparison),
        }
    } else {
        comparison
    })
}

fn require_bool(term: &Term) -> Result<(), ContractFailure> {
    match term.sort() {
        Ok(Sort::Bool) => Ok(()),
        Ok(actual) => fail(
            "frontend.python.int-enum.boolean-required",
            format!("expected bool expression, got {actual:?}"),
        ),
        Err(message) => fail("frontend.python.int-enum.term-invalid", message),
    }
}

fn make_obligation(
    id: String,
    assumptions: Vec<Term>,
    conclusion: Term,
    path: &str,
    source: &str,
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

fn fail<T>(code: &'static str, message: impl Into<String>) -> Result<T, ContractFailure> {
    Err(ContractFailure {
        code,
        message: message.into(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const PREFIX: &str = "from nagini_contracts.contracts import *\nfrom enum import IntEnum\n\nclass Flag(IntEnum):\n    off = 0\n    on = 1\n";

    fn verify(suffix: &str, symbols: &[&str]) -> Result<HeapContractVerification, ContractFailure> {
        verify_int_enum_module(
            &format!("{PREFIX}{suffix}"),
            "enum.py",
            &symbols
                .iter()
                .map(|symbol| (*symbol).to_owned())
                .collect::<Vec<_>>(),
        )?
        .ok_or_else(|| ContractFailure {
            code: "test.int-enum.not-selected",
            message: "IntEnum verifier was not selected".to_owned(),
        })
    }

    #[test]
    fn keeps_numeric_equality_distinct_from_member_identity() {
        let result = verify(
            "\nclass Other(IntEnum):\n    off = 0\n    on = 2\n\ndef run() -> None:\n    assert Flag.off == Other.off\n    assert Flag.off is Flag(0)\n    assert Flag.off is Other.off\n",
            &["run"],
        )
        .unwrap();
        assert_eq!(result.obligations.len(), 4);
        assert!(result.obligations[0].satisfied());
        assert!(result.obligations[1].satisfied());
        assert!(result.obligations[2].satisfied());
        assert!(!result.obligations[3].satisfied());
    }

    #[test]
    fn accepts_verified_selected_symbols_and_rejects_unknown_ones() {
        let result = verify(
            "\ndef run(value: Flag) -> None:\n    assert value == 0 or value == 1\n",
            &["Flag", "run"],
        )
        .unwrap();
        assert!(result.passed);
        let error = verify("", &["missing"]).unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.int-enum.requested-symbol-unresolved"
        );
    }

    #[test]
    fn refuses_top_level_effects_and_noncanonical_imports() {
        let effect = verify_int_enum_module(
            "from enum import IntEnum\ndangerous_call()\nclass Flag(IntEnum):\n    off = 0\n",
            "effect.py",
            &[],
        )
        .unwrap_err();
        assert_eq!(
            effect.code,
            "frontend.python.int-enum.module-statement-unsupported"
        );

        for source in [
            "import enum\nfrom enum import IntEnum\nclass Flag(IntEnum):\n    off = 0\n",
            "from enum import IntEnum\nfrom enum import IntEnum as IE\nclass Flag(IntEnum):\n    off = 0\n",
            "from enum import IntEnum\nfrom enum import *\nclass Flag(IntEnum):\n    off = 0\n",
            "from enum import IntEnum\nfrom dataclasses import dataclass as dc\nclass Flag(IntEnum):\n    off = 0\n",
            "from enum import IntEnum\nfrom nagini_contracts.contracts import Requires\nclass Flag(IntEnum):\n    off = 0\n",
        ] {
            assert!(
                verify_int_enum_module(source, "import.py", &[]).is_err(),
                "{source}"
            );
        }
    }

    #[test]
    fn refuses_protected_rebinding_and_unmodeled_mixed_classes() {
        for suffix in [
            "\ndef run(Flag: Flag) -> None:\n    pass\n",
            "\ndef run() -> None:\n    int = Flag.off\n",
            "\ndef Flag() -> None:\n    pass\n",
            "\ndef int() -> None:\n    pass\n",
            "\nclass IntEnum:\n    pass\n",
            "\nclass Ordinary:\n    pass\n",
            "\nclass Child(Flag):\n    extra = 2\n",
        ] {
            assert!(verify(suffix, &[]).is_err(), "{suffix}");
        }
    }

    #[test]
    fn refuses_aliases_hooks_dynamic_members_and_out_of_domain_construction() {
        for source in [
            "from enum import IntEnum\nclass Flag(IntEnum):\n    off = 0\n    also_off = 0\n",
            "from enum import IntEnum\nclass Flag(IntEnum):\n    off = make_value()\n",
            "from enum import IntEnum\nclass Flag(IntEnum):\n    off = 0\n    def __str__(self) -> str:\n        return 'off'\n",
            "from enum import IntEnum\nclass Flag(IntEnum):\n    off = 0\n\ndef run() -> None:\n    value = Flag(2)\n",
        ] {
            assert!(
                verify_int_enum_module(source, "invalid.py", &[]).is_err(),
                "{source}"
            );
        }
    }

    #[test]
    fn refuses_out_of_order_bindings_and_nonprefix_or_unbound_requires() {
        for source in [
            "class Flag(IntEnum):\n    off = 0\nfrom enum import IntEnum\n",
            "from dataclasses import dataclass\nfrom enum import IntEnum\n@dataclass\nclass Holder:\n    value: Flag = Flag.off\nclass Flag(IntEnum):\n    off = 0\n",
            "from enum import IntEnum\ndef run(value: Flag) -> None:\n    pass\nclass Flag(IntEnum):\n    off = 0\n",
            "from enum import IntEnum\nclass Flag(IntEnum):\n    off = 0\ndef run(value: Flag) -> None:\n    Requires(value == Flag.off)\n",
            "from enum import IntEnum\nfrom nagini_contracts.contracts import *\nclass Flag(IntEnum):\n    off = 0\ndef run(value: Flag) -> None:\n    assert value == Flag.off\n    Requires(value == Flag.off)\n",
            "from enum import IntEnum\nclass Flag(IntEnum):\n    off = 0\nclass Flag(IntEnum):\n    on = 1\n",
        ] {
            assert!(
                verify_int_enum_module(source, "order.py", &[]).is_err(),
                "{source}"
            );
        }
    }

    #[test]
    fn refuses_enum_member_names_outside_safe_ordinary_subset() {
        for name in ["_hidden", "mro", "name", "value", "CAPITAL", "trailing_"] {
            let source =
                format!("from enum import IntEnum\nclass Flag(IntEnum):\n    {name} = 0\n");
            let error = verify_int_enum_module(&source, "member.py", &[]).unwrap_err();
            assert_eq!(
                error.code,
                "frontend.python.int-enum.member-name-unsupported"
            );
        }
    }
}
