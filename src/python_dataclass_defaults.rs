//! Closed heap execution for ordinary dataclass defaults and fresh list factories.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_parser::{Parse, ast};

use crate::python_contracts::ContractFailure;
use crate::python_heap_contracts::HeapContractVerification;
use crate::solver::discharge;
use crate::vc::{
    IntEnumDescriptor, Obligation, ObligationExpectation, ObligationResult, Sort, Term,
};

#[derive(Clone, Debug)]
enum FieldKind {
    Int,
    Bool,
    String,
    IntList,
    IntEnum(IntEnumDescriptor),
}

#[derive(Clone, Debug)]
enum DefaultValue {
    Required,
    Value(Value),
    FreshIntList,
}

#[derive(Clone, Debug)]
struct FieldSpec {
    name: String,
    kind: FieldKind,
    default: DefaultValue,
}

#[derive(Clone, Debug)]
struct DataclassSpec {
    frozen: bool,
    fields: Vec<FieldSpec>,
}

#[derive(Clone, Debug)]
enum Value {
    Int(Term),
    Bool(Term),
    String(Term),
    IntEnum {
        descriptor: IntEnumDescriptor,
        carrier: Term,
    },
    IntList(String),
    Object {
        allocation: String,
        class: String,
    },
}

#[derive(Default)]
struct RuntimeHeap {
    next_allocation: usize,
    objects: BTreeMap<String, BTreeMap<String, Value>>,
    int_lists: BTreeMap<String, Vec<Term>>,
}

impl RuntimeHeap {
    fn allocate(&mut self, prefix: &str) -> String {
        let id = format!("{prefix}:{}", self.next_allocation);
        self.next_allocation += 1;
        id
    }

    fn allocate_list(&mut self, prefix: &str, values: Vec<Term>) -> Value {
        let id = self.allocate(prefix);
        self.int_lists.insert(id.clone(), values);
        Value::IntList(id)
    }
}

struct ModuleModel {
    enums: BTreeMap<String, IntEnumDescriptor>,
    dataclasses: BTreeMap<String, DataclassSpec>,
    functions: Vec<ast::StmtFunctionDef>,
}

pub(super) fn verify_dataclass_defaults_module(
    source: &str,
    path: &str,
    requested_symbols: &[String],
) -> Result<Option<HeapContractVerification>, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    if !suite.iter().any(is_canonical_dataclass_import)
        || !suite.iter().any(is_canonical_int_enum_import)
    {
        return Ok(None);
    }
    let model = build_model(&suite)?;
    let declared = model
        .dataclasses
        .keys()
        .chain(model.enums.keys())
        .cloned()
        .chain(model.functions.iter().map(|item| item.name.to_string()))
        .collect::<BTreeSet<_>>();
    for symbol in requested_symbols {
        if !declared.contains(symbol) {
            return fail(
                "frontend.python.dataclass-defaults.requested-symbol-unresolved",
                format!("requested symbol {symbol:?} is not a verified declaration"),
            );
        }
    }
    let mut methods = Vec::new();
    let mut obligations = Vec::new();
    for function in &model.functions {
        methods.push(function.name.to_string());
        verify_function(function, &model, source, path, &mut obligations)?;
    }
    let results = obligations
        .iter()
        .map(|item| {
            discharge(item).map_err(|message| ContractFailure {
                code: "solver.translation-failed",
                message,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Some(HeapContractVerification {
        schema: "maledictus-python-heap-contracts/v67".to_owned(),
        path: path.to_owned(),
        methods,
        passed: results.iter().all(ObligationResult::satisfied),
        obligations: results,
    }))
}

fn is_canonical_dataclass_import(statement: &ast::Stmt) -> bool {
    matches!(statement, ast::Stmt::ImportFrom(import)
        if import.level.is_none_or(|level| level == 0_u32)
            && import.module.as_ref().is_some_and(|module| module.as_str() == "dataclasses")
            && import.names.iter().any(|alias|
                alias.name.as_str() == "dataclass" && alias.asname.is_none()))
}

fn is_canonical_int_enum_import(statement: &ast::Stmt) -> bool {
    matches!(statement, ast::Stmt::ImportFrom(import)
        if import.level.is_none_or(|level| level == 0_u32)
            && import.module.as_ref().is_some_and(|module| module.as_str() == "enum")
            && matches!(import.names.as_slice(), [alias]
                if alias.name.as_str() == "IntEnum" && alias.asname.is_none()))
}

fn build_model(suite: &[ast::Stmt]) -> Result<ModuleModel, ContractFailure> {
    let mut enum_imported = false;
    let mut list_imported = false;
    let mut contracts_imported = false;
    let mut dataclass_imported = false;
    let mut field_imported = false;
    let mut bindings = BTreeSet::new();
    let protected = BTreeSet::from([
        "IntEnum",
        "List",
        "dataclass",
        "field",
        "list",
        "len",
        "int",
        "bool",
        "str",
    ]);
    let mut enums = BTreeMap::new();
    let mut dataclasses = BTreeMap::new();
    let mut functions = Vec::new();
    for statement in suite {
        match statement {
            ast::Stmt::Import(_) => {
                return fail(
                    "frontend.python.dataclass-defaults.import-unsupported",
                    "ordinary imports are outside the closed dataclass fragment",
                );
            }
            ast::Stmt::ImportFrom(import) => {
                if !import.level.is_none_or(|level| level == 0_u32) {
                    return fail(
                        "frontend.python.dataclass-defaults.import-unsupported",
                        "relative imports are unsupported",
                    );
                }
                let Some(module) = import.module.as_ref() else {
                    return fail(
                        "frontend.python.dataclass-defaults.import-unsupported",
                        "absolute import module is required",
                    );
                };
                match module.as_str() {
                    "enum"
                        if matches!(import.names.as_slice(), [alias]
                        if alias.name.as_str() == "IntEnum" && alias.asname.is_none()) =>
                    {
                        bind_once(&mut bindings, "IntEnum")?;
                        enum_imported = true;
                    }
                    "typing"
                        if matches!(import.names.as_slice(), [alias]
                        if alias.name.as_str() == "List" && alias.asname.is_none()) =>
                    {
                        bind_once(&mut bindings, "List")?;
                        list_imported = true;
                    }
                    "nagini_contracts.contracts"
                        if matches!(import.names.as_slice(), [alias]
                        if alias.name.as_str() == "*" && alias.asname.is_none()) =>
                    {
                        contracts_imported = true;
                    }
                    "dataclasses" => {
                        if import.names.is_empty() {
                            return fail(
                                "frontend.python.dataclass-defaults.import-unsupported",
                                "dataclasses import must name dataclass",
                            );
                        }
                        for alias in &import.names {
                            if alias.asname.is_some()
                                || !matches!(alias.name.as_str(), "dataclass" | "field")
                            {
                                return fail(
                                    "frontend.python.dataclass-defaults.import-unsupported",
                                    "only canonical dataclass and field imports are supported",
                                );
                            }
                            bind_once(&mut bindings, alias.name.as_str())?;
                            dataclass_imported |= alias.name.as_str() == "dataclass";
                            field_imported |= alias.name.as_str() == "field";
                        }
                        if !dataclass_imported {
                            return fail(
                                "frontend.python.dataclass-defaults.import-unsupported",
                                "dataclass must be imported",
                            );
                        }
                    }
                    _ => {
                        return fail(
                            "frontend.python.dataclass-defaults.import-unsupported",
                            format!("import from {module:?} is unsupported"),
                        );
                    }
                }
            }
            ast::Stmt::ClassDef(class) => {
                let name = class.name.as_str();
                if protected.contains(name) || !bindings.insert(name.to_owned()) {
                    return fail(
                        "frontend.python.dataclass-defaults.binding-redefined",
                        format!("class name {name:?} is protected or duplicated"),
                    );
                }
                if matches!(class.bases.as_slice(), [ast::Expr::Name(base)]
                    if base.id.as_str() == "IntEnum")
                {
                    if !enum_imported {
                        return fail(
                            "frontend.python.dataclass-defaults.definition-order",
                            "IntEnum class precedes its import",
                        );
                    }
                    enums.insert(name.to_owned(), parse_enum(class)?);
                } else {
                    if !dataclass_imported {
                        return fail(
                            "frontend.python.dataclass-defaults.definition-order",
                            "dataclass precedes its import",
                        );
                    }
                    dataclasses.insert(
                        name.to_owned(),
                        parse_dataclass(class, &enums, list_imported, field_imported)?,
                    );
                }
            }
            ast::Stmt::FunctionDef(function) => {
                if !contracts_imported {
                    return fail(
                        "frontend.python.dataclass-defaults.contract-import-required",
                        "verification functions require a preceding contracts import",
                    );
                }
                if protected.contains(function.name.as_str())
                    || !bindings.insert(function.name.to_string())
                {
                    return fail(
                        "frontend.python.dataclass-defaults.binding-redefined",
                        format!(
                            "function name {:?} is protected or duplicated",
                            function.name
                        ),
                    );
                }
                functions.push(function.clone());
            }
            _ => {
                return fail(
                    "frontend.python.dataclass-defaults.module-statement-unsupported",
                    format!("unsupported module statement {statement:?}"),
                );
            }
        }
    }
    if dataclasses.is_empty() {
        return fail(
            "frontend.python.dataclass-defaults.declaration-missing",
            "no supported dataclass was declared",
        );
    }
    Ok(ModuleModel {
        enums,
        dataclasses,
        functions,
    })
}

fn bind_once(bindings: &mut BTreeSet<String>, name: &str) -> Result<(), ContractFailure> {
    if !bindings.insert(name.to_owned()) {
        return fail(
            "frontend.python.dataclass-defaults.binding-redefined",
            format!("module name {name:?} is bound twice"),
        );
    }
    Ok(())
}

fn parse_enum(class: &ast::StmtClassDef) -> Result<IntEnumDescriptor, ContractFailure> {
    if !class.decorator_list.is_empty()
        || !class.keywords.is_empty()
        || !class.type_params.is_empty()
        || class.bases.len() != 1
    {
        return fail(
            "frontend.python.dataclass-defaults.enum-shape-unsupported",
            "IntEnum decorators, mixed bases, and class options are unsupported",
        );
    }
    let mut members = Vec::new();
    let mut names = BTreeSet::new();
    let mut values = BTreeSet::new();
    for statement in &class.body {
        let ast::Stmt::Assign(assignment) = statement else {
            return fail(
                "frontend.python.dataclass-defaults.enum-body-unsupported",
                "IntEnum body may contain only member assignments",
            );
        };
        let [ast::Expr::Name(name)] = assignment.targets.as_slice() else {
            return fail(
                "frontend.python.dataclass-defaults.enum-member-unsupported",
                "IntEnum member requires a direct name",
            );
        };
        if !safe_member(name.id.as_str()) {
            return fail(
                "frontend.python.dataclass-defaults.enum-member-unsupported",
                "IntEnum member name is outside the safe ordinary subset",
            );
        }
        let value = exact_int(&assignment.value)?;
        if !names.insert(name.id.to_string()) || !values.insert(value) {
            return fail(
                "frontend.python.dataclass-defaults.enum-alias-unsupported",
                "IntEnum names and values must be unique",
            );
        }
        members.push((name.id.to_string(), value));
    }
    if members.is_empty() {
        return fail(
            "frontend.python.dataclass-defaults.enum-empty",
            "IntEnum requires members",
        );
    }
    Ok(IntEnumDescriptor {
        class: class.name.to_string(),
        members,
    })
}

fn safe_member(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|first| first.is_ascii_lowercase())
        && chars.all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == '_')
        && !name.ends_with('_')
        && !name.contains("__")
        && !matches!(name, "mro" | "name" | "value")
}

fn parse_dataclass(
    class: &ast::StmtClassDef,
    enums: &BTreeMap<String, IntEnumDescriptor>,
    list_imported: bool,
    field_imported: bool,
) -> Result<DataclassSpec, ContractFailure> {
    if !class.bases.is_empty() || !class.keywords.is_empty() || !class.type_params.is_empty() {
        return fail(
            "frontend.python.dataclass-defaults.inheritance-unsupported",
            "dataclass inheritance, metaclasses, and type parameters are unsupported",
        );
    }
    let frozen = match class.decorator_list.as_slice() {
        [ast::Expr::Name(name)] if name.id.as_str() == "dataclass" => false,
        [ast::Expr::Call(call)]
            if matches!(call.func.as_ref(), ast::Expr::Name(name)
                if name.id.as_str() == "dataclass")
                && call.args.is_empty()
                && matches!(call.keywords.as_slice(), [keyword]
                    if keyword.arg.as_ref().is_some_and(|name| name.as_str() == "frozen")
                        && matches!(&keyword.value, ast::Expr::Constant(value)
                            if value.value == ast::Constant::Bool(true))) =>
        {
            true
        }
        _ => {
            return fail(
                "frontend.python.dataclass-defaults.decorator-unsupported",
                "only @dataclass and @dataclass(frozen=True) are supported",
            );
        }
    };
    let mut fields = Vec::new();
    let mut field_names = BTreeSet::new();
    let mut seen_default = false;
    for statement in &class.body {
        let ast::Stmt::AnnAssign(field) = statement else {
            return fail(
                "frontend.python.dataclass-defaults.class-body-unsupported",
                "dataclass body may contain only annotated fields",
            );
        };
        let ast::Expr::Name(name) = field.target.as_ref() else {
            return fail(
                "frontend.python.dataclass-defaults.field-target-unsupported",
                "field requires a direct name",
            );
        };
        if !field_names.insert(name.id.to_string()) {
            return fail(
                "frontend.python.dataclass-defaults.field-redefined",
                format!("dataclass field {:?} is declared more than once", name.id),
            );
        }
        let kind = field_kind(&field.annotation, enums, list_imported)?;
        let default = field_default(field.value.as_deref(), &kind, enums, field_imported)?;
        if seen_default && matches!(default, DefaultValue::Required) {
            return fail(
                "frontend.python.dataclass-defaults.field-order-unsupported",
                "required field follows a defaulted field",
            );
        }
        seen_default |= !matches!(default, DefaultValue::Required);
        fields.push(FieldSpec {
            name: name.id.to_string(),
            kind,
            default,
        });
    }
    if fields.is_empty() {
        return fail(
            "frontend.python.dataclass-defaults.empty-unsupported",
            "dataclass requires fields",
        );
    }
    Ok(DataclassSpec { frozen, fields })
}

fn field_kind(
    annotation: &ast::Expr,
    enums: &BTreeMap<String, IntEnumDescriptor>,
    list_imported: bool,
) -> Result<FieldKind, ContractFailure> {
    match annotation {
        ast::Expr::Name(name) if name.id.as_str() == "int" => Ok(FieldKind::Int),
        ast::Expr::Name(name) if name.id.as_str() == "bool" => Ok(FieldKind::Bool),
        ast::Expr::Name(name) if name.id.as_str() == "str" => Ok(FieldKind::String),
        ast::Expr::Name(name) if enums.contains_key(name.id.as_str()) => {
            Ok(FieldKind::IntEnum(enums[name.id.as_str()].clone()))
        }
        ast::Expr::Subscript(item)
            if list_imported
                && matches!(item.value.as_ref(), ast::Expr::Name(name)
                    if name.id.as_str() == "List")
                && matches!(item.slice.as_ref(), ast::Expr::Name(name)
                    if name.id.as_str() == "int") =>
        {
            Ok(FieldKind::IntList)
        }
        _ => fail(
            "frontend.python.dataclass-defaults.field-type-unsupported",
            "field type must be int, bool, str, List[int], or a preceding IntEnum",
        ),
    }
}

fn field_default(
    expression: Option<&ast::Expr>,
    kind: &FieldKind,
    enums: &BTreeMap<String, IntEnumDescriptor>,
    field_imported: bool,
) -> Result<DefaultValue, ContractFailure> {
    let Some(expression) = expression else {
        return Ok(DefaultValue::Required);
    };
    match (kind, expression) {
        (FieldKind::Int, ast::Expr::Constant(value))
            if matches!(value.value, ast::Constant::Int(_)) =>
        {
            Ok(DefaultValue::Value(Value::Int(Term::Int {
                value: exact_int(expression)?,
            })))
        }
        (FieldKind::Bool, ast::Expr::Constant(value))
            if matches!(value.value, ast::Constant::Bool(_)) =>
        {
            let ast::Constant::Bool(value) = value.value else {
                unreachable!()
            };
            Ok(DefaultValue::Value(Value::Bool(Term::Bool { value })))
        }
        (FieldKind::String, ast::Expr::Constant(value))
            if matches!(value.value, ast::Constant::Str(_)) =>
        {
            let ast::Constant::Str(value) = &value.value else {
                unreachable!()
            };
            Ok(DefaultValue::Value(Value::String(Term::String {
                value: value.clone(),
            })))
        }
        (FieldKind::IntEnum(expected), ast::Expr::Attribute(attribute)) => {
            let value = enum_member(attribute, enums)?;
            if matches!(&value, Value::IntEnum { descriptor, .. } if descriptor == expected) {
                Ok(DefaultValue::Value(value))
            } else {
                fail(
                    "frontend.python.dataclass-defaults.enum-default-mismatch",
                    "enum default belongs to another descriptor",
                )
            }
        }
        (FieldKind::IntList, ast::Expr::Call(call))
            if field_imported
                && matches!(call.func.as_ref(), ast::Expr::Name(name)
                    if name.id.as_str() == "field")
                && call.args.is_empty()
                && matches!(call.keywords.as_slice(), [keyword]
                    if keyword.arg.as_ref().is_some_and(|name|
                        name.as_str() == "default_factory")
                        && matches!(&keyword.value, ast::Expr::Name(name)
                            if name.id.as_str() == "list")) =>
        {
            Ok(DefaultValue::FreshIntList)
        }
        (FieldKind::IntList, ast::Expr::List(_)) => fail(
            "frontend.python.dataclass-defaults.mutable-literal-default",
            "mutable list literal default is forbidden",
        ),
        _ => fail(
            "frontend.python.dataclass-defaults.default-unsupported",
            "default is type-mismatched, effectful, or uses an unsupported factory",
        ),
    }
}

fn exact_int(expression: &ast::Expr) -> Result<i64, ContractFailure> {
    let ast::Expr::Constant(value) = expression else {
        return fail(
            "frontend.python.dataclass-defaults.integer-literal-required",
            "integer literal required",
        );
    };
    let ast::Constant::Int(value) = &value.value else {
        return fail(
            "frontend.python.dataclass-defaults.integer-literal-required",
            "integer literal required",
        );
    };
    value.to_string().parse().map_err(|_| ContractFailure {
        code: "frontend.python.integer.out-of-range",
        message: format!("integer literal {value} exceeds i64"),
    })
}

fn enum_member(
    attribute: &ast::ExprAttribute,
    enums: &BTreeMap<String, IntEnumDescriptor>,
) -> Result<Value, ContractFailure> {
    let ast::Expr::Name(owner) = attribute.value.as_ref() else {
        return fail(
            "frontend.python.dataclass-defaults.enum-member-unsupported",
            "enum member owner must be a direct name",
        );
    };
    let Some(descriptor) = enums.get(owner.id.as_str()) else {
        return fail(
            "frontend.python.dataclass-defaults.enum-member-unknown",
            format!("enum {:?} is unavailable", owner.id),
        );
    };
    let Some((_, value)) = descriptor
        .members
        .iter()
        .find(|(name, _)| name == attribute.attr.as_str())
    else {
        return fail(
            "frontend.python.dataclass-defaults.enum-member-unknown",
            format!("enum {:?} has no member {:?}", owner.id, attribute.attr),
        );
    };
    Ok(Value::IntEnum {
        descriptor: descriptor.clone(),
        carrier: Term::Int { value: *value },
    })
}

fn verify_function(
    function: &ast::StmtFunctionDef,
    model: &ModuleModel,
    source: &str,
    path: &str,
    obligations: &mut Vec<Obligation>,
) -> Result<(), ContractFailure> {
    if !function.decorator_list.is_empty()
        || !function.type_params.is_empty()
        || function.args.vararg.is_some()
        || function.args.kwarg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || !matches!(function.returns.as_deref(), Some(ast::Expr::Constant(value))
            if value.value == ast::Constant::None)
    {
        return fail(
            "frontend.python.dataclass-defaults.function-signature-unsupported",
            format!("function {:?} has an unsupported signature", function.name),
        );
    }
    let mut environment = BTreeMap::new();
    let protected_locals = BTreeSet::from([
        "IntEnum",
        "List",
        "dataclass",
        "field",
        "list",
        "len",
        "int",
        "bool",
        "str",
    ]);
    for argument in function.args.posonlyargs.iter().chain(&function.args.args) {
        if argument.default.is_some()
            || !matches!(argument.def.annotation.as_deref(), Some(ast::Expr::Name(name))
                if name.id.as_str() == "int")
            || protected_locals.contains(argument.def.arg.as_str())
            || model.dataclasses.contains_key(argument.def.arg.as_str())
            || model.enums.contains_key(argument.def.arg.as_str())
        {
            return fail(
                "frontend.python.dataclass-defaults.parameter-type-unsupported",
                "verification functions accept only required int parameters",
            );
        }
        environment.insert(
            argument.def.arg.to_string(),
            Value::Int(Term::Variable {
                name: format!("{}::{}", function.name, argument.def.arg),
                sort: Sort::Int,
            }),
        );
    }
    let mut heap = RuntimeHeap::default();
    for statement in &function.body {
        match statement {
            ast::Stmt::Assign(assignment) => {
                let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
                    if let [ast::Expr::Attribute(attribute)] = assignment.targets.as_slice() {
                        return reject_field_assignment(
                            attribute,
                            &environment,
                            &model.dataclasses,
                        );
                    }
                    return fail(
                        "frontend.python.dataclass-defaults.assignment-target-unsupported",
                        "assignment requires a direct local name",
                    );
                };
                if environment.contains_key(target.id.as_str())
                    || protected_locals.contains(target.id.as_str())
                    || model.dataclasses.contains_key(target.id.as_str())
                    || model.enums.contains_key(target.id.as_str())
                {
                    return fail(
                        "frontend.python.dataclass-defaults.rebinding-unsupported",
                        format!("local name {:?} is rebound or protected", target.id),
                    );
                }
                let value = evaluate(
                    &assignment.value,
                    &environment,
                    &mut heap,
                    model,
                    function.name.as_str(),
                )?;
                environment.insert(target.id.to_string(), value);
            }
            ast::Stmt::Expr(expression) => execute_expression_statement(
                &expression.value,
                &environment,
                &mut heap,
                model,
                function.name.as_str(),
            )?,
            ast::Stmt::Assert(assertion) => {
                let conclusion = evaluate_bool(
                    &assertion.test,
                    &environment,
                    &mut heap,
                    model,
                    function.name.as_str(),
                )?;
                obligations.push(make_obligation(
                    format!(
                        "{}:assert:{}",
                        function.name,
                        u32::from(assertion.range.start())
                    ),
                    conclusion,
                    path,
                    source,
                    assertion.range.start().into(),
                ));
            }
            ast::Stmt::Return(returned)
                if returned.value.as_deref().is_none_or(|value| {
                    matches!(value, ast::Expr::Constant(constant)
                        if constant.value == ast::Constant::None)
                }) => {}
            _ => {
                return fail(
                    "frontend.python.dataclass-defaults.statement-unsupported",
                    format!(
                        "function {:?} contains an unsupported statement",
                        function.name
                    ),
                );
            }
        }
    }
    Ok(())
}

fn reject_field_assignment<T>(
    attribute: &ast::ExprAttribute,
    environment: &BTreeMap<String, Value>,
    classes: &BTreeMap<String, DataclassSpec>,
) -> Result<T, ContractFailure> {
    if let ast::Expr::Name(receiver) = attribute.value.as_ref()
        && let Some(Value::Object { class, .. }) = environment.get(receiver.id.as_str())
        && classes.get(class).is_some_and(|spec| spec.frozen)
    {
        return fail(
            "frontend.python.heap.dataclass-frozen-write",
            format!(
                "frozen dataclass field {class:?}.{} cannot be assigned",
                attribute.attr
            ),
        );
    }
    fail(
        "frontend.python.dataclass-defaults.field-assignment-unsupported",
        "dataclass field assignment is outside the bounded defaults fragment",
    )
}

fn execute_expression_statement(
    expression: &ast::Expr,
    environment: &BTreeMap<String, Value>,
    heap: &mut RuntimeHeap,
    model: &ModuleModel,
    function: &str,
) -> Result<(), ContractFailure> {
    let ast::Expr::Call(call) = expression else {
        return fail(
            "frontend.python.dataclass-defaults.expression-statement-unsupported",
            "only list append is supported as an expression statement",
        );
    };
    let ast::Expr::Attribute(method) = call.func.as_ref() else {
        return fail(
            "frontend.python.dataclass-defaults.expression-statement-unsupported",
            "only receiver list.append is supported",
        );
    };
    if method.attr.as_str() != "append" || call.args.len() != 1 || !call.keywords.is_empty() {
        return fail(
            "frontend.python.dataclass-defaults.list-append-unsupported",
            "list append requires exactly one positional argument",
        );
    }
    let receiver = evaluate(&method.value, environment, heap, model, function)?;
    let Value::IntList(allocation) = receiver else {
        return fail(
            "frontend.python.dataclass-defaults.list-append-receiver",
            "append receiver must be a modeled List[int] allocation",
        );
    };
    let value = evaluate(&call.args[0], environment, heap, model, function)?;
    let Value::Int(value) = value else {
        return fail(
            "frontend.python.dataclass-defaults.list-append-type",
            "List[int].append requires int",
        );
    };
    heap.int_lists
        .get_mut(&allocation)
        .ok_or_else(|| ContractFailure {
            code: "frontend.python.dataclass-defaults.list-allocation-unknown",
            message: format!("list allocation {allocation:?} is unavailable"),
        })?
        .push(value);
    Ok(())
}

fn evaluate(
    expression: &ast::Expr,
    environment: &BTreeMap<String, Value>,
    heap: &mut RuntimeHeap,
    model: &ModuleModel,
    function: &str,
) -> Result<Value, ContractFailure> {
    match expression {
        ast::Expr::Name(name) => {
            environment
                .get(name.id.as_str())
                .cloned()
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.dataclass-defaults.name-unresolved",
                    message: format!("name {:?} is unavailable", name.id),
                })
        }
        ast::Expr::Constant(value) => match &value.value {
            ast::Constant::Int(value) => Ok(Value::Int(Term::Int {
                value: value.to_string().parse().map_err(|_| ContractFailure {
                    code: "frontend.python.integer.out-of-range",
                    message: format!("integer literal {value} exceeds i64"),
                })?,
            })),
            ast::Constant::Bool(value) => Ok(Value::Bool(Term::Bool { value: *value })),
            ast::Constant::Str(value) => Ok(Value::String(Term::String {
                value: value.clone(),
            })),
            _ => fail(
                "frontend.python.dataclass-defaults.literal-unsupported",
                "literal is outside the bounded dataclass fragment",
            ),
        },
        ast::Expr::List(list) => {
            let mut values = Vec::new();
            for element in &list.elts {
                let Value::Int(value) = evaluate(element, environment, heap, model, function)?
                else {
                    return fail(
                        "frontend.python.dataclass-defaults.list-element-type",
                        "list literal requires int elements",
                    );
                };
                values.push(value);
            }
            Ok(heap.allocate_list(&format!("{function}:list"), values))
        }
        ast::Expr::Attribute(attribute) => {
            if matches!(attribute.value.as_ref(), ast::Expr::Name(owner)
                if model.enums.contains_key(owner.id.as_str()))
            {
                return enum_member(attribute, &model.enums);
            }
            let receiver = evaluate(&attribute.value, environment, heap, model, function)?;
            let Value::Object { allocation, .. } = receiver else {
                return fail(
                    "frontend.python.dataclass-defaults.field-receiver",
                    "field read requires a modeled dataclass object",
                );
            };
            heap.objects
                .get(&allocation)
                .and_then(|fields| fields.get(attribute.attr.as_str()))
                .cloned()
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.dataclass-defaults.field-unknown",
                    message: format!("object {allocation:?} has no field {:?}", attribute.attr),
                })
        }
        ast::Expr::Call(call) => evaluate_call(call, environment, heap, model, function),
        ast::Expr::Subscript(item) => {
            let receiver = evaluate(&item.value, environment, heap, model, function)?;
            let Value::IntList(allocation) = receiver else {
                return fail(
                    "frontend.python.dataclass-defaults.index-receiver",
                    "index receiver must be List[int]",
                );
            };
            let index = usize::try_from(exact_int(&item.slice)?).map_err(|_| ContractFailure {
                code: "frontend.python.dataclass-defaults.index-out-of-range",
                message: "negative indices are outside this bounded fragment".to_owned(),
            })?;
            heap.int_lists
                .get(&allocation)
                .and_then(|values| values.get(index))
                .cloned()
                .map(Value::Int)
                .ok_or_else(|| ContractFailure {
                    code: "frontend.python.dataclass-defaults.index-out-of-range",
                    message: format!("list index {index} is outside allocation {allocation:?}"),
                })
        }
        _ => fail(
            "frontend.python.dataclass-defaults.expression-unsupported",
            format!("expression {expression:?} is unsupported"),
        ),
    }
}

fn evaluate_call(
    call: &ast::ExprCall,
    environment: &BTreeMap<String, Value>,
    heap: &mut RuntimeHeap,
    model: &ModuleModel,
    function: &str,
) -> Result<Value, ContractFailure> {
    let ast::Expr::Name(callee) = call.func.as_ref() else {
        return fail(
            "frontend.python.dataclass-defaults.call-unsupported",
            "call target must be a direct canonical name",
        );
    };
    if callee.id.as_str() == "len" {
        if call.args.len() != 1 || !call.keywords.is_empty() {
            return fail(
                "frontend.python.dataclass-defaults.len-arguments",
                "len requires one positional argument",
            );
        }
        let Value::IntList(allocation) =
            evaluate(&call.args[0], environment, heap, model, function)?
        else {
            return fail(
                "frontend.python.dataclass-defaults.len-type",
                "len requires List[int]",
            );
        };
        let length = heap
            .int_lists
            .get(&allocation)
            .ok_or_else(|| ContractFailure {
                code: "frontend.python.dataclass-defaults.list-allocation-unknown",
                message: format!("list allocation {allocation:?} is unavailable"),
            })?
            .len();
        return Ok(Value::Int(Term::Int {
            value: i64::try_from(length).map_err(|_| ContractFailure {
                code: "frontend.python.integer.out-of-range",
                message: "list length exceeds i64".to_owned(),
            })?,
        }));
    }
    let Some(class) = model.dataclasses.get(callee.id.as_str()) else {
        return fail(
            "frontend.python.dataclass-defaults.call-unsupported",
            format!("call target {:?} is not a dataclass constructor", callee.id),
        );
    };
    if call.args.len() > class.fields.len() {
        return fail(
            "frontend.python.dataclass-defaults.constructor-arguments",
            "too many positional constructor arguments",
        );
    }
    let mut supplied = BTreeMap::new();
    for (field, argument) in class.fields.iter().zip(&call.args) {
        supplied.insert(
            field.name.clone(),
            evaluate(argument, environment, heap, model, function)?,
        );
    }
    for keyword in &call.keywords {
        let Some(name) = keyword.arg.as_ref() else {
            return fail(
                "frontend.python.dataclass-defaults.constructor-arguments",
                "dynamic keyword mappings are unsupported",
            );
        };
        if !class.fields.iter().any(|field| field.name == name.as_str())
            || supplied.contains_key(name.as_str())
        {
            return fail(
                "frontend.python.dataclass-defaults.constructor-arguments",
                format!("duplicate or unknown constructor argument {name:?}"),
            );
        }
        supplied.insert(
            name.to_string(),
            evaluate(&keyword.value, environment, heap, model, function)?,
        );
    }
    let object_id = heap.allocate(&format!("{function}:{}", callee.id));
    let mut fields = BTreeMap::new();
    for field in &class.fields {
        let value = match supplied.remove(&field.name) {
            Some(value) => value,
            None => match &field.default {
                DefaultValue::Required => {
                    return fail(
                        "frontend.python.dataclass-defaults.constructor-argument-missing",
                        format!("required field {:?} was not supplied", field.name),
                    );
                }
                DefaultValue::Value(value) => value.clone(),
                DefaultValue::FreshIntList => heap.allocate_list(
                    &format!("{function}:{}:{}", callee.id, field.name),
                    Vec::new(),
                ),
            },
        };
        ensure_kind(&value, &field.kind)?;
        fields.insert(field.name.clone(), value);
    }
    heap.objects.insert(object_id.clone(), fields);
    Ok(Value::Object {
        allocation: object_id,
        class: callee.id.to_string(),
    })
}

fn ensure_kind(value: &Value, kind: &FieldKind) -> Result<(), ContractFailure> {
    let valid = match (value, kind) {
        (Value::Int(_), FieldKind::Int)
        | (Value::Bool(_), FieldKind::Bool)
        | (Value::String(_), FieldKind::String)
        | (Value::IntList(_), FieldKind::IntList) => true,
        (Value::IntEnum { descriptor, .. }, FieldKind::IntEnum(expected)) => descriptor == expected,
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        fail(
            "frontend.python.dataclass-defaults.constructor-argument-type",
            "constructor argument does not match the field type",
        )
    }
}

fn evaluate_bool(
    expression: &ast::Expr,
    environment: &BTreeMap<String, Value>,
    heap: &mut RuntimeHeap,
    model: &ModuleModel,
    function: &str,
) -> Result<Term, ContractFailure> {
    let ast::Expr::Compare(comparison) = expression else {
        return fail(
            "frontend.python.dataclass-defaults.boolean-expression",
            "assertion requires one equality or identity comparison",
        );
    };
    if comparison.ops.len() != 1 || comparison.comparators.len() != 1 {
        return fail(
            "frontend.python.dataclass-defaults.comparison-chain-unsupported",
            "comparison chains are unsupported",
        );
    }
    let left = evaluate(&comparison.left, environment, heap, model, function)?;
    let right = evaluate(
        &comparison.comparators[0],
        environment,
        heap,
        model,
        function,
    )?;
    match comparison.ops[0] {
        ast::CmpOp::Eq | ast::CmpOp::NotEq => {
            let equality = value_equality(&left, &right, heap)?;
            Ok(if comparison.ops[0] == ast::CmpOp::Eq {
                equality
            } else {
                Term::Not {
                    value: Box::new(equality),
                }
            })
        }
        ast::CmpOp::Is | ast::CmpOp::IsNot => {
            let identity = value_identity(&left, &right)?;
            Ok(if comparison.ops[0] == ast::CmpOp::Is {
                identity
            } else {
                Term::Not {
                    value: Box::new(identity),
                }
            })
        }
        _ => fail(
            "frontend.python.dataclass-defaults.comparison-unsupported",
            "only ==, !=, is, and is not are supported",
        ),
    }
}

fn value_equality(
    left: &Value,
    right: &Value,
    heap: &RuntimeHeap,
) -> Result<Term, ContractFailure> {
    match (left, right) {
        (Value::Int(left), Value::Int(right))
        | (Value::Bool(left), Value::Bool(right))
        | (Value::String(left), Value::String(right)) => Ok(Term::Equal {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }),
        (Value::IntEnum { carrier: left, .. }, Value::IntEnum { carrier: right, .. }) => {
            Ok(Term::Equal {
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            })
        }
        (Value::IntList(left), Value::IntList(right)) => {
            let left = heap.int_lists.get(left).ok_or_else(|| ContractFailure {
                code: "frontend.python.dataclass-defaults.list-allocation-unknown",
                message: "left list allocation is unavailable".to_owned(),
            })?;
            let right = heap.int_lists.get(right).ok_or_else(|| ContractFailure {
                code: "frontend.python.dataclass-defaults.list-allocation-unknown",
                message: "right list allocation is unavailable".to_owned(),
            })?;
            Ok(Term::Equal {
                left: Box::new(Term::List {
                    element_sort: Sort::Int,
                    values: left.clone(),
                }),
                right: Box::new(Term::List {
                    element_sort: Sort::Int,
                    values: right.clone(),
                }),
            })
        }
        _ => fail(
            "frontend.python.dataclass-defaults.equality-type-mismatch",
            "equality operands have unsupported or different types",
        ),
    }
}

fn value_identity(left: &Value, right: &Value) -> Result<Term, ContractFailure> {
    let same = match (left, right) {
        (Value::IntList(left), Value::IntList(right)) => left == right,
        (
            Value::Object {
                allocation: left, ..
            },
            Value::Object {
                allocation: right, ..
            },
        ) => left == right,
        (
            Value::IntEnum {
                descriptor: left_descriptor,
                carrier: left,
            },
            Value::IntEnum {
                descriptor: right_descriptor,
                carrier: right,
            },
        ) => {
            return Ok(Term::IntEnumIdentity {
                left: Box::new(Term::IntEnumValue {
                    descriptor: left_descriptor.clone(),
                    value: Box::new(left.clone()),
                }),
                right: Box::new(Term::IntEnumValue {
                    descriptor: right_descriptor.clone(),
                    value: Box::new(right.clone()),
                }),
            });
        }
        _ => {
            return fail(
                "frontend.python.dataclass-defaults.identity-type-mismatch",
                "identity requires two modeled lists, objects, or IntEnums",
            );
        }
    };
    Ok(Term::Bool { value: same })
}

fn make_obligation(
    id: String,
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
        assumptions: Vec::new(),
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
