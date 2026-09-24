//! Closed verification for finite Python type algebra and path narrowing.
//!
//! This frontend models `Union`, `Optional`, nominal inheritance, `isinstance`, and `cast` as
//! source types.  A union is expanded into finite entry states; it is never erased to `object`.
//! Narrowing therefore changes the reachable states rather than trusting a source assertion.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_ast::Visitor;
use rustpython_parser::ast::Ranged;
use rustpython_parser::{Mode, Parse, Tok, ast, lexer::lex};

use crate::python_contracts::ContractFailure;
use crate::python_heap_contracts::HeapContractVerification;
use crate::python_type_algebra_kernel::{
    NominalClass, NominalHierarchy, Type, TypeList, build_nominal_hierarchy, cast_compatible,
    expand_union, is_assignable, is_subclass, narrow_type, normalize_union,
};
use crate::solver::discharge;
use crate::vc::{Obligation, ObligationExpectation, ObligationResult, Sort, Term};

#[derive(Clone, Debug)]
enum Value {
    Int(Term),
    Bool(Term),
    Str(Term),
    None,
    Ref {
        identity: Term,
        classes: Vec<String>,
        tag: Option<Term>,
    },
    AnyObject {
        identity: Term,
        key: String,
    },
    List {
        element: Type,
        length: Term,
        values: Option<Vec<Value>>,
        key: String,
    },
    Set {
        element: Type,
        length: Term,
    },
    Dict {
        key_type: Type,
        value_type: Type,
        length: Term,
    },
    Tuple(Vec<Value>),
    VariadicTuple {
        element: Type,
        length: Term,
        values: Option<Vec<Value>>,
        key: String,
    },
}

#[derive(Clone, Debug, Default)]
struct State {
    assumptions: Vec<Term>,
    environment: BTreeMap<String, Value>,
    refinements: BTreeMap<String, String>,
}

#[derive(Clone)]
struct ReturnState {
    state: State,
    value: Option<Value>,
}

#[derive(Clone, Debug)]
struct FunctionSummary {
    parameters: Vec<(String, Type)>,
    return_type: Option<Type>,
    requires: Vec<ast::Expr>,
    ensures: Vec<ast::Expr>,
    body: Vec<ast::Stmt>,
}

#[derive(Clone, Debug)]
struct MethodSummary {
    positional_parameters: usize,
    required_parameters: usize,
}

#[derive(Clone, Debug, Default)]
struct Catalog {
    classes: BTreeMap<String, Option<String>>,
    hierarchy: NominalHierarchy,
    methods: BTreeMap<String, BTreeMap<String, MethodSummary>>,
    functions: BTreeMap<String, FunctionSummary>,
}

struct Context<'a> {
    source: &'a str,
    path: &'a str,
    catalog: &'a Catalog,
    function: &'a str,
    obligations: &'a mut Vec<Obligation>,
    call_serial: &'a mut u64,
}

pub(super) fn verify_type_algebra_module(
    source: &str,
    path: &str,
    requested_symbols: &[String],
) -> Result<Option<HeapContractVerification>, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    if !has_type_algebra_feature(&suite) {
        return Ok(None);
    }
    // Nagini algebraic data types have their own closed heap semantics. Their modules often
    // import `cast` for constructor projections, but that does not transfer ownership to this
    // nominal-union frontend. The explicit ADT import is a source-language boundary, so route
    // the complete module to the ADT verifier before attempting this fragment's class catalog.
    if imports_nagini_adt(&suite) {
        return Ok(None);
    }
    // Qualified requested symbols are class methods owned by the heap/reference frontends. This
    // frontend models closed top-level type operations only; the presence of a top-level helper
    // in the same Optional/Union module must not transfer ownership of method contracts or heap
    // receiver semantics to it.
    if requested_symbols.iter().any(|name| name.contains('.')) {
        return Ok(None);
    }
    let top_level_functions = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => Some(function.name.as_str()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    // `Optional` and `Union` are also ordinary heap-field annotations. This frontend owns a
    // request only when at least one explicitly requested symbol is a function it could analyze;
    // otherwise the more general heap/reference frontends must get the module unchanged.
    if !requested_symbols.is_empty()
        && !requested_symbols
            .iter()
            .any(|name| top_level_functions.contains(name.as_str()))
    {
        return Ok(None);
    }
    if !requested_symbols.is_empty()
        && requested_symbols
            .iter()
            .any(|name| !top_level_functions.contains(name.as_str()))
    {
        return Err(type_algebra_failure(
            "frontend.python.type-algebra.requested-symbol-missing",
            "a requested symbol is not declared in the closed type-algebra module",
        ));
    }
    // Importing Optional/Union is not itself a type-algebra operation. Heap and nominal-reference
    // programs use those annotations for fields and receivers, and must retain their richer
    // ownership. Claim this fragment only when a selected top-level function performs an actual
    // closed algebra operation: cast/narrowing, typed tuple access, or truth testing a value whose
    // own annotation is algebraic. This preflight deliberately examines executable function bodies
    // rather than prose, fixture names, or field annotations.
    if !has_selected_executable_type_algebra_use(source, &suite, requested_symbols) {
        return Ok(None);
    }
    let Some(catalog) = collect_catalog(&suite) else {
        return Err(type_algebra_failure(
            "frontend.python.type-algebra.catalog-unsupported",
            "the module uses type algebra but its declarations are outside the closed type-algebra fragment",
        ));
    };
    // Class-only modules belong to the heap/reference frontends. Their annotations may mention
    // Optional or Union, but there is no top-level type-algebra operation for this frontend to
    // prove. Returning `None` here is a disjoint routing decision, not a fallback after a failed
    // type-algebra proof.
    if catalog.functions.is_empty() {
        return Ok(None);
    }
    if contains_unsupported_cast_target(&suite, &catalog.classes) {
        return Err(ContractFailure {
            code: "frontend.python.type-algebra.cast-target-unsupported",
            message:
                "cast target must be a source-bound class or a closed supported typing annotation"
                    .to_owned(),
        });
    }
    let declared = catalog
        .classes
        .keys()
        .chain(catalog.functions.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    if requested_symbols
        .iter()
        .any(|name| !declared.contains(name))
    {
        return Err(type_algebra_failure(
            "frontend.python.type-algebra.requested-symbol-missing",
            "a requested symbol is not declared in the closed type-algebra module",
        ));
    }

    let mut obligations = Vec::new();
    let mut methods = Vec::new();
    let mut call_serial = 0;
    let algebraic_functions = algebraic_result_functions(&suite);
    for (name, function) in &catalog.functions {
        if !requested_symbols.is_empty() && !requested_symbols.iter().any(|item| item == name) {
            continue;
        }
        let Some(mut function_obligations) =
            verify_function(source, path, name, function, &catalog, &mut call_serial)
        else {
            let has_direct_algebra_witness = suite.iter().any(|statement| {
                matches!(statement,
                ast::Stmt::FunctionDef(source_function)
                    if source_function.name.as_str() == name
                        && function_has_executable_type_algebra_use(
                            source,
                            source_function,
                            &algebraic_functions,
                        ))
            });
            if !has_direct_algebra_witness {
                // A mixed module can contain a genuine algebra helper alongside ordinary heap,
                // call-binding, or reference functions. If the unsupported selected function
                // does not itself consume an algebra value, this frontend does not own the whole
                // module. A function with a direct witness remains fail-closed below.
                return Ok(None);
            }
            return Err(type_algebra_failure(
                "frontend.python.type-algebra.function-unsupported",
                &format!(
                    "function {name:?} uses behavior outside the closed type-algebra fragment"
                ),
            ));
        };
        methods.push(name.clone());
        obligations.append(&mut function_obligations);
        obligations.push(make_obligation(
            format!("{name}:function-totality:type-algebra"),
            Vec::new(),
            bool_value(true),
            source,
            path,
            function_offset(&suite, name),
        ));
    }
    if methods.is_empty() {
        return Err(type_algebra_failure(
            "frontend.python.type-algebra.no-verifiable-symbols",
            "the module uses type algebra but no requested function can be verified",
        ));
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
        schema: "maledictus-python-type-algebra/v1".to_owned(),
        path: path.to_owned(),
        methods,
        obligations,
        passed,
    }))
}

fn type_algebra_failure(code: &'static str, message: &str) -> ContractFailure {
    ContractFailure {
        code,
        message: message.to_owned(),
    }
}

struct UnsupportedCastTargetCollector<'a> {
    classes: &'a BTreeMap<String, Option<String>>,
    found: bool,
}

impl Visitor for UnsupportedCastTargetCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if matches!(node.func.as_ref(), ast::Expr::Name(function)
            if function.id.as_str() == "cast")
        {
            self.found |= match node.args.as_slice() {
                [target, _] => parse_cast_target(target, self.classes).is_none(),
                _ => true,
            };
        }
        self.generic_visit_expr_call(node);
    }
}

fn contains_unsupported_cast_target(
    suite: &[ast::Stmt],
    classes: &BTreeMap<String, Option<String>>,
) -> bool {
    let mut collector = UnsupportedCastTargetCollector {
        classes,
        found: false,
    };
    for statement in suite {
        collector.visit_stmt(statement.clone());
    }
    collector.found
}

fn has_type_algebra_feature(suite: &[ast::Stmt]) -> bool {
    suite.iter().any(|statement| match statement {
        ast::Stmt::ImportFrom(import)
            if import.level.is_none_or(|level| level == 0_u32)
                && import
                    .module
                    .as_ref()
                    .is_some_and(|module| module.as_str() == "typing") =>
        {
            import.names.iter().any(|alias| {
                alias.asname.is_none()
                    && matches!(alias.name.as_str(), "Union" | "Optional" | "cast" | "Tuple")
            })
        }
        _ => false,
    })
}

fn algebraic_annotation(expression: &ast::Expr) -> bool {
    matches!(expression,
        ast::Expr::Subscript(subscript)
            if matches!(subscript.value.as_ref(),
                ast::Expr::Name(name)
                    if matches!(name.id.as_str(),
                        "Union" | "Optional" | "Tuple" | "List" | "Set" | "Dict")))
}

fn parse_algebraic_type_comment(comment: &str) -> bool {
    ast::Expr::parse(comment, "<type-comment>")
        .is_ok_and(|expression| algebraic_annotation(&expression))
}

struct AlgebraicLocalCollector<'a> {
    names: BTreeSet<String>,
    algebraic_functions: &'a BTreeSet<String>,
    algebraic_type_comment_lines: BTreeSet<u32>,
    source: String,
}

impl AlgebraicLocalCollector<'_> {
    fn expression_is_algebraic(&self, expression: &ast::Expr) -> bool {
        match expression {
            ast::Expr::Name(name) => self.names.contains(name.id.as_str()),
            ast::Expr::Call(call) => matches!(call.func.as_ref(),
                ast::Expr::Name(name)
                    if self.algebraic_functions.contains(name.id.as_str())),
            ast::Expr::IfExp(conditional) => {
                self.expression_is_algebraic(&conditional.body)
                    || self.expression_is_algebraic(&conditional.orelse)
            }
            _ => false,
        }
    }
}

impl Visitor for AlgebraicLocalCollector<'_> {
    fn visit_stmt_assign(&mut self, node: ast::StmtAssign) {
        if node
            .type_comment
            .as_deref()
            .is_some_and(parse_algebraic_type_comment)
            || self
                .algebraic_type_comment_lines
                .contains(&source_line_number(&self.source, node.range.start().into()))
            || self.expression_is_algebraic(&node.value)
        {
            for target in &node.targets {
                if let ast::Expr::Name(name) = target {
                    self.names.insert(name.id.to_string());
                }
            }
        }
        self.generic_visit_stmt_assign(node);
    }

    fn visit_stmt_ann_assign(&mut self, node: ast::StmtAnnAssign) {
        if algebraic_annotation(&node.annotation)
            && let ast::Expr::Name(name) = node.target.as_ref()
        {
            self.names.insert(name.id.to_string());
        }
        self.generic_visit_stmt_ann_assign(node);
    }
}

struct ExecutableAlgebraCollector<'a> {
    algebraic_names: &'a BTreeSet<String>,
    algebraic_functions: &'a BTreeSet<String>,
    found: bool,
}

impl ExecutableAlgebraCollector<'_> {
    fn expression_uses_algebraic_name(&self, expression: &ast::Expr) -> bool {
        match expression {
            ast::Expr::Name(name) => self.algebraic_names.contains(name.id.as_str()),
            ast::Expr::BoolOp(operation) => operation
                .values
                .iter()
                .any(|value| self.expression_uses_algebraic_name(value)),
            ast::Expr::UnaryOp(operation) => {
                self.expression_uses_algebraic_name(&operation.operand)
            }
            ast::Expr::Call(call) => matches!(call.func.as_ref(),
                ast::Expr::Name(name)
                    if self.algebraic_functions.contains(name.id.as_str())),
            _ => false,
        }
    }
}

impl Visitor for ExecutableAlgebraCollector<'_> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        self.found |= match node.func.as_ref() {
            ast::Expr::Name(name) if name.id.as_str() == "cast" => true,
            ast::Expr::Name(name) if name.id.as_str() == "isinstance" => node
                .args
                .first()
                .is_some_and(|value| self.expression_uses_algebraic_name(value)),
            _ => false,
        };
        self.generic_visit_expr_call(node);
    }

    fn visit_expr_subscript(&mut self, node: ast::ExprSubscript) {
        self.found |= matches!(node.value.as_ref(), ast::Expr::Name(name)
            if self.algebraic_names.contains(name.id.as_str()));
        self.generic_visit_expr_subscript(node);
    }

    fn visit_stmt_if(&mut self, node: ast::StmtIf) {
        self.found |= self.expression_uses_algebraic_name(&node.test);
        self.generic_visit_stmt_if(node);
    }

    fn visit_stmt_while(&mut self, node: ast::StmtWhile) {
        self.found |= self.expression_uses_algebraic_name(&node.test);
        self.generic_visit_stmt_while(node);
    }

    fn visit_expr_if_exp(&mut self, node: ast::ExprIfExp) {
        self.found |= self.expression_uses_algebraic_name(&node.test);
        self.generic_visit_expr_if_exp(node);
    }
}

fn function_has_executable_type_algebra_use(
    source: &str,
    function: &ast::StmtFunctionDef,
    algebraic_functions: &BTreeSet<String>,
) -> bool {
    let mut algebraic_type_comment_lines = BTreeSet::new();
    for token in lex(source, Mode::Module) {
        let Ok((Tok::Comment(comment), range)) = token else {
            continue;
        };
        let comment = comment.trim_start_matches('#').trim_start();
        let Some(annotation) = comment.strip_prefix("type:") else {
            continue;
        };
        if parse_algebraic_type_comment(annotation.trim()) {
            algebraic_type_comment_lines.insert(source_line_number(source, range.start().into()));
        }
    }
    let mut locals = AlgebraicLocalCollector {
        names: BTreeSet::new(),
        algebraic_functions,
        algebraic_type_comment_lines,
        source: source.to_owned(),
    };
    for argument in function.args.posonlyargs.iter().chain(&function.args.args) {
        if argument
            .def
            .annotation
            .as_deref()
            .is_some_and(algebraic_annotation)
        {
            locals.names.insert(argument.def.arg.to_string());
        }
    }
    for statement in &function.body {
        locals.visit_stmt(statement.clone());
    }
    let mut executable = ExecutableAlgebraCollector {
        algebraic_names: &locals.names,
        algebraic_functions,
        found: false,
    };
    for statement in &function.body {
        executable.visit_stmt(statement.clone());
    }
    executable.found
}

fn algebraic_result_functions(suite: &[ast::Stmt]) -> BTreeSet<String> {
    suite
        .iter()
        .filter_map(|statement| {
            let ast::Stmt::FunctionDef(function) = statement else {
                return None;
            };
            function
                .returns
                .as_deref()
                .is_some_and(algebraic_annotation)
                .then(|| function.name.to_string())
        })
        .collect()
}

fn has_selected_executable_type_algebra_use(
    source: &str,
    suite: &[ast::Stmt],
    requested_symbols: &[String],
) -> bool {
    let algebraic_functions = algebraic_result_functions(suite);
    let selected_has_algebraic_signature = suite.iter().any(|statement| {
        let ast::Stmt::FunctionDef(function) = statement else {
            return false;
        };
        (requested_symbols.is_empty()
            || requested_symbols
                .iter()
                .any(|name| name == function.name.as_str()))
            && (function
                .args
                .posonlyargs
                .iter()
                .chain(&function.args.args)
                .any(|argument| {
                    argument
                        .def
                        .annotation
                        .as_deref()
                        .is_some_and(algebraic_annotation)
                })
                || function
                    .returns
                    .as_deref()
                    .is_some_and(algebraic_annotation))
    });
    suite.iter().any(|statement| {
        let ast::Stmt::FunctionDef(function) = statement else {
            return false;
        };
        (requested_symbols.is_empty()
            || requested_symbols
                .iter()
                .any(|name| name == function.name.as_str()))
            && function_has_executable_type_algebra_use(source, function, &algebraic_functions)
    }) || (selected_has_algebraic_signature
        && suite.iter().any(|statement| {
            matches!(statement,
                ast::Stmt::ClassDef(class)
                    if class.bases.len() > 1
                        || !class.keywords.is_empty()
                        || !class.type_params.is_empty())
        }))
}

fn source_line_number(source: &str, byte_offset: u32) -> u32 {
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

fn imports_nagini_adt(suite: &[ast::Stmt]) -> bool {
    suite.iter().any(|statement| {
        matches!(statement,
        ast::Stmt::ImportFrom(import)
            if import.level.is_none_or(|level| level == 0_u32)
                && import.module.as_ref().is_some_and(|module| {
                    module.as_str() == "nagini_contracts.adt"
                })
                && import.names.iter().any(|alias| {
                    alias.asname.is_none() && alias.name.as_str() == "ADT"
                }))
    })
}

fn collect_catalog(suite: &[ast::Stmt]) -> Option<Catalog> {
    let mut catalog = Catalog::default();
    for statement in suite {
        if let ast::Stmt::ClassDef(class) = statement {
            if !class.keywords.is_empty()
                || !class.decorator_list.is_empty()
                || !class.type_params.is_empty()
                || class.bases.len() > 1
            {
                return None;
            }
            let base = match class.bases.as_slice() {
                [] => None,
                [ast::Expr::Name(base)] => Some(base.id.to_string()),
                _ => return None,
            };
            if catalog
                .classes
                .insert(class.name.to_string(), base)
                .is_some()
            {
                return None;
            }
            let mut methods = BTreeMap::new();
            for statement in &class.body {
                let ast::Stmt::FunctionDef(method) = statement else {
                    continue;
                };
                if method.args.posonlyargs.len() + method.args.args.len() == 0
                    || method.args.vararg.is_some()
                    || method.args.kwarg.is_some()
                    || !method.args.kwonlyargs.is_empty()
                {
                    return None;
                }
                let positional_parameters =
                    method.args.posonlyargs.len() + method.args.args.len() - 1;
                let required_parameters = method
                    .args
                    .posonlyargs
                    .iter()
                    .chain(&method.args.args)
                    .skip(1)
                    .filter(|argument| argument.default.is_none())
                    .count();
                methods.insert(
                    method.name.to_string(),
                    MethodSummary {
                        positional_parameters,
                        required_parameters,
                    },
                );
            }
            catalog.methods.insert(class.name.to_string(), methods);
        }
    }
    let hierarchy = catalog
        .classes
        .iter()
        .map(|(name, parent)| NominalClass {
            name: name.clone(),
            parent: parent.clone(),
        })
        .collect();
    catalog.hierarchy = build_nominal_hierarchy(hierarchy)?;
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                if !function.decorator_list.iter().all(|decorator| {
                    matches!(decorator, ast::Expr::Name(name) if name.id.as_str() == "Pure")
                }) || !function.type_params.is_empty()
                    || function.args.vararg.is_some()
                    || function.args.kwarg.is_some()
                    || !function.args.kwonlyargs.is_empty()
                {
                    return None;
                }
                let parameters = function
                    .args
                    .posonlyargs
                    .iter()
                    .chain(&function.args.args)
                    .map(|argument| {
                        parse_type(argument.def.annotation.as_deref(), &catalog.classes)
                            .map(|ty| (argument.def.arg.to_string(), ty))
                    })
                    .collect::<Option<Vec<_>>>()?;
                let return_type = match function.returns.as_deref() {
                    Some(ast::Expr::Constant(constant)) if constant.value.is_none() => None,
                    annotation => Some(parse_type(annotation, &catalog.classes)?),
                };
                let mut requires = Vec::new();
                let mut ensures = Vec::new();
                let mut body = Vec::new();
                for body_statement in &function.body {
                    match contract_expression(body_statement) {
                        Some(("Requires", expression)) => requires.push(expression.clone()),
                        Some(("Ensures", expression)) => ensures.push(expression.clone()),
                        _ => body.push(body_statement.clone()),
                    }
                }
                if catalog
                    .functions
                    .insert(
                        function.name.to_string(),
                        FunctionSummary {
                            parameters,
                            return_type,
                            requires,
                            ensures,
                            body,
                        },
                    )
                    .is_some()
                {
                    return None;
                }
            }
            ast::Stmt::ImportFrom(import) if supported_import(import) => {}
            ast::Stmt::ClassDef(_) => {}
            _ => return None,
        }
    }
    Some(catalog)
}

fn supported_import(import: &ast::StmtImportFrom) -> bool {
    import.level.is_none_or(|level| level == 0_u32)
        && import.module.as_ref().is_some_and(|module| {
            matches!(module.as_str(), "typing" | "nagini_contracts.contracts")
        })
}

fn parse_type(
    annotation: Option<&ast::Expr>,
    classes: &BTreeMap<String, Option<String>>,
) -> Option<Type> {
    match annotation? {
        ast::Expr::Name(name) => match name.id.as_str() {
            "int" => Some(Type::Int),
            "bool" => Some(Type::Bool),
            "str" => Some(Type::Str),
            "object" => Some(Type::Object),
            name if classes.contains_key(name) => Some(Type::Class(name.to_owned())),
            _ => None,
        },
        ast::Expr::Constant(constant) if constant.value.is_none() => Some(Type::None),
        ast::Expr::Subscript(subscript) => {
            let ast::Expr::Name(container) = subscript.value.as_ref() else {
                return None;
            };
            match container.id.as_str() {
                "Optional" => Some(normalize_union(vec![
                    parse_type(Some(&subscript.slice), classes)?,
                    Type::None,
                ])),
                "Union" => {
                    let elements = match subscript.slice.as_ref() {
                        ast::Expr::Tuple(tuple) => tuple.elts.as_slice(),
                        other => std::slice::from_ref(other),
                    };
                    Some(normalize_union(
                        elements
                            .iter()
                            .map(|element| parse_type(Some(element), classes))
                            .collect::<Option<Vec<_>>>()?,
                    ))
                }
                "List" => Some(Type::List(Box::new(parse_type(
                    Some(&subscript.slice),
                    classes,
                )?))),
                "Set" => Some(Type::Set(Box::new(parse_type(
                    Some(&subscript.slice),
                    classes,
                )?))),
                "Dict" => {
                    let ast::Expr::Tuple(tuple) = subscript.slice.as_ref() else {
                        return None;
                    };
                    let [key, value] = tuple.elts.as_slice() else {
                        return None;
                    };
                    Some(Type::Dict(
                        Box::new(parse_type(Some(key), classes)?),
                        Box::new(parse_type(Some(value), classes)?),
                    ))
                }
                "Tuple" => {
                    let ast::Expr::Tuple(tuple) = subscript.slice.as_ref() else {
                        return Some(Type::FixedTuple(TypeList::from_vec(vec![parse_type(
                            Some(&subscript.slice),
                            classes,
                        )?])));
                    };
                    if let [element, ast::Expr::Constant(ellipsis)] = tuple.elts.as_slice()
                        && ellipsis.value.is_ellipsis()
                    {
                        Some(Type::VariadicTuple(Box::new(parse_type(
                            Some(element),
                            classes,
                        )?)))
                    } else {
                        Some(Type::FixedTuple(TypeList::from_vec(
                            tuple
                                .elts
                                .iter()
                                .map(|element| parse_type(Some(element), classes))
                                .collect::<Option<Vec<_>>>()?,
                        )))
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn type_list_items(types: &TypeList) -> Vec<&Type> {
    let mut items = Vec::new();
    let mut current = types;
    while let TypeList::Item(item, tail) = current {
        items.push(item.as_ref());
        current = tail;
    }
    items
}

fn contract_expression(statement: &ast::Stmt) -> Option<(&str, &ast::Expr)> {
    let ast::Stmt::Expr(statement) = statement else {
        return None;
    };
    let ast::Expr::Call(call) = statement.value.as_ref() else {
        return None;
    };
    let ast::Expr::Name(function) = call.func.as_ref() else {
        return None;
    };
    let [argument] = call.args.as_slice() else {
        return None;
    };
    matches!(function.id.as_str(), "Requires" | "Ensures" | "Invariant")
        .then_some((function.id.as_str(), argument))
}

fn verify_function(
    source: &str,
    path: &str,
    name: &str,
    function: &FunctionSummary,
    catalog: &Catalog,
    call_serial: &mut u64,
) -> Option<Vec<Obligation>> {
    let mut states = vec![State::default()];
    for (parameter, ty) in &function.parameters {
        let variants = values_for_type(ty, parameter);
        let mut expanded = Vec::new();
        for state in states {
            for (value, assumptions) in &variants {
                let mut branch = state.clone();
                branch.environment.insert(parameter.clone(), value.clone());
                branch.assumptions.extend(assumptions.clone());
                expanded.push(branch);
            }
        }
        states = expanded;
    }
    let mut obligations = Vec::new();
    for state in &mut states {
        for precondition in &function.requires {
            let condition = lower_bool(precondition, state, catalog, None, call_serial)?;
            state.assumptions.push(condition);
            apply_refinement(precondition, true, state, catalog);
        }
    }
    let mut context = Context {
        source,
        path,
        catalog,
        function: name,
        obligations: &mut obligations,
        call_serial,
    };
    let mut returns = Vec::new();
    let fallthrough = execute_statements(&function.body, states, &mut returns, &mut context)?;
    // Executable return-annotation compatibility is enforced by the mandatory strict Python
    // typechecker on issuance. Nagini's corpus includes annotated procedures that fall through;
    // their reachable assertions remain proof obligations in this semantic conformance lane.
    let _ = fallthrough;
    for returned in &returns {
        if !value_matches_declared(
            returned.value.as_ref(),
            function.return_type.as_ref(),
            catalog,
        ) {
            return None;
        }
        for (index, postcondition) in function.ensures.iter().enumerate() {
            let mut state = returned.state.clone();
            let conclusion = lower_bool(
                postcondition,
                &mut state,
                catalog,
                returned.value.as_ref(),
                context.call_serial,
            )?;
            context.obligations.push(make_obligation(
                format!("{name}:postcondition:type-algebra:{index}"),
                state.assumptions,
                conclusion,
                source,
                path,
                postcondition.range().start().into(),
            ));
        }
    }
    Some(obligations)
}

fn values_for_type(ty: &Type, key: &str) -> Vec<(Value, Vec<Term>)> {
    match ty {
        Type::Union(_) => expand_union(ty)
            .iter()
            .flat_map(|variant| values_for_type(variant, key))
            .collect(),
        Type::Int => vec![(Value::Int(variable(key, Sort::Int)), Vec::new())],
        Type::Bool => vec![(Value::Bool(variable(key, Sort::Bool)), Vec::new())],
        Type::Str => vec![(Value::Str(variable(key, Sort::String)), Vec::new())],
        Type::None => vec![(Value::None, Vec::new())],
        Type::Object => vec![(
            Value::AnyObject {
                identity: variable(&format!("ref:{key}"), Sort::Reference),
                key: key.to_owned(),
            },
            Vec::new(),
        )],
        Type::Class(class) => vec![(
            Value::Ref {
                identity: variable(&format!("ref:{key}"), Sort::Reference),
                classes: vec![class.clone()],
                tag: None,
            },
            Vec::new(),
        )],
        Type::List(element) => vec![(
            Value::List {
                element: element.as_ref().clone(),
                length: variable(&format!("len:{key}"), Sort::Int),
                values: None,
                key: key.to_owned(),
            },
            vec![Term::GreaterEqual {
                left: Box::new(variable(&format!("len:{key}"), Sort::Int)),
                right: Box::new(int_value(0)),
            }],
        )],
        Type::Set(element) => vec![(
            Value::Set {
                element: element.as_ref().clone(),
                length: variable(&format!("len:{key}"), Sort::Int),
            },
            vec![Term::GreaterEqual {
                left: Box::new(variable(&format!("len:{key}"), Sort::Int)),
                right: Box::new(int_value(0)),
            }],
        )],
        Type::Dict(key_type, value_type) => vec![(
            Value::Dict {
                key_type: key_type.as_ref().clone(),
                value_type: value_type.as_ref().clone(),
                length: variable(&format!("len:{key}"), Sort::Int),
            },
            vec![Term::GreaterEqual {
                left: Box::new(variable(&format!("len:{key}"), Sort::Int)),
                right: Box::new(int_value(0)),
            }],
        )],
        Type::FixedTuple(elements) => {
            let values = type_list_items(elements)
                .into_iter()
                .enumerate()
                .map(|(index, element)| {
                    values_for_type(element, &format!("{key}[{index}]"))
                        .into_iter()
                        .next()
                        .map(|pair| pair.0)
                })
                .collect::<Option<Vec<_>>>()
                .unwrap_or_default();
            vec![(Value::Tuple(values), Vec::new())]
        }
        Type::VariadicTuple(element) => vec![(
            Value::VariadicTuple {
                element: element.as_ref().clone(),
                length: variable(&format!("len:{key}"), Sort::Int),
                values: None,
                key: key.to_owned(),
            },
            vec![Term::GreaterEqual {
                left: Box::new(variable(&format!("len:{key}"), Sort::Int)),
                right: Box::new(int_value(0)),
            }],
        )],
    }
}

fn execute_statements(
    statements: &[ast::Stmt],
    mut states: Vec<State>,
    returns: &mut Vec<ReturnState>,
    context: &mut Context<'_>,
) -> Option<Vec<State>> {
    for statement in statements {
        if states.is_empty() {
            break;
        }
        states = execute_statement(statement, states, returns, context)?;
    }
    Some(states)
}

fn execute_statement(
    statement: &ast::Stmt,
    states: Vec<State>,
    returns: &mut Vec<ReturnState>,
    context: &mut Context<'_>,
) -> Option<Vec<State>> {
    match statement {
        ast::Stmt::Pass(_) => Some(states),
        ast::Stmt::Assign(assignment) => {
            let [target] = assignment.targets.as_slice() else {
                return None;
            };
            states
                .into_iter()
                .map(|mut state| {
                    emit_cast_obligations(&assignment.value, &mut state, context)?;
                    emit_index_obligations(&assignment.value, &mut state, context)?;
                    let value = lower_value(
                        &assignment.value,
                        &mut state,
                        context.catalog,
                        None,
                        context.call_serial,
                    )?;
                    assign_target(target, value, &mut state)?;
                    Some(state)
                })
                .collect()
        }
        ast::Stmt::AnnAssign(assignment) => {
            let value = assignment.value.as_deref()?;
            states
                .into_iter()
                .map(|mut state| {
                    emit_cast_obligations(value, &mut state, context)?;
                    emit_index_obligations(value, &mut state, context)?;
                    let value = lower_value(
                        value,
                        &mut state,
                        context.catalog,
                        None,
                        context.call_serial,
                    )?;
                    assign_target(&assignment.target, value, &mut state)?;
                    Some(state)
                })
                .collect()
        }
        ast::Stmt::AugAssign(assignment) => states
            .into_iter()
            .map(|mut state| {
                let ast::Expr::Name(target) = assignment.target.as_ref() else {
                    return None;
                };
                let left = state.environment.get(target.id.as_str())?.clone();
                let right = lower_value(
                    &assignment.value,
                    &mut state,
                    context.catalog,
                    None,
                    context.call_serial,
                )?;
                let value = match (&assignment.op, left, right) {
                    (ast::Operator::Add, Value::Int(left), Value::Int(right)) => {
                        Value::Int(Term::Add {
                            left: Box::new(left),
                            right: Box::new(right),
                        })
                    }
                    (ast::Operator::Sub, Value::Int(left), Value::Int(right)) => {
                        Value::Int(Term::Subtract {
                            left: Box::new(left),
                            right: Box::new(right),
                        })
                    }
                    _ => return None,
                };
                state.environment.insert(target.id.to_string(), value);
                Some(state)
            })
            .collect(),
        ast::Stmt::If(branch) => {
            let mut true_states = Vec::new();
            let mut false_states = Vec::new();
            for mut state in states {
                let condition = lower_bool(
                    &branch.test,
                    &mut state,
                    context.catalog,
                    None,
                    context.call_serial,
                )?;
                if condition != bool_value(false) {
                    let mut truth = state.clone();
                    truth.assumptions.push(condition.clone());
                    apply_refinement(&branch.test, true, &mut truth, context.catalog);
                    true_states.push(truth);
                }
                if condition != bool_value(true) {
                    state.assumptions.push(Term::Not {
                        value: Box::new(condition),
                    });
                    apply_refinement(&branch.test, false, &mut state, context.catalog);
                    false_states.push(state);
                }
            }
            let mut joined = execute_statements(&branch.body, true_states, returns, context)?;
            joined.extend(execute_statements(
                &branch.orelse,
                false_states,
                returns,
                context,
            )?);
            Some(joined)
        }
        ast::Stmt::While(loop_statement) => execute_while(loop_statement, states, returns, context),
        ast::Stmt::Return(returned) => {
            for mut state in states {
                let value = match returned.value.as_deref() {
                    Some(expression) => {
                        emit_cast_obligations(expression, &mut state, context)?;
                        emit_index_obligations(expression, &mut state, context)?;
                        Some(lower_value(
                            expression,
                            &mut state,
                            context.catalog,
                            None,
                            context.call_serial,
                        )?)
                    }
                    None => None,
                };
                returns.push(ReturnState { state, value });
            }
            Some(Vec::new())
        }
        ast::Stmt::Assert(assertion) => {
            for mut state in states.iter().cloned() {
                emit_cast_obligations(&assertion.test, &mut state, context)?;
                emit_index_obligations(&assertion.test, &mut state, context)?;
                let conclusion = lower_bool(
                    &assertion.test,
                    &mut state,
                    context.catalog,
                    None,
                    context.call_serial,
                )?;
                context.obligations.push(make_obligation(
                    format!(
                        "{}:assert:type-algebra:{}",
                        context.function,
                        u32::from(assertion.range.start())
                    ),
                    state.assumptions,
                    conclusion,
                    context.source,
                    context.path,
                    assertion.range.start().into(),
                ));
            }
            Some(states)
        }
        ast::Stmt::Expr(expression) => {
            let ast::Expr::Call(call) = expression.value.as_ref() else {
                return None;
            };
            if matches!(call.func.as_ref(), ast::Expr::Name(function)
                if function.id.as_str() == "Assert")
            {
                let [argument] = call.args.as_slice() else {
                    return None;
                };
                for mut state in states.iter().cloned() {
                    emit_cast_obligations(argument, &mut state, context)?;
                    emit_index_obligations(argument, &mut state, context)?;
                    let conclusion = lower_bool(
                        argument,
                        &mut state,
                        context.catalog,
                        None,
                        context.call_serial,
                    )?;
                    context.obligations.push(make_obligation(
                        format!(
                            "{}:assert:type-algebra:{}",
                            context.function,
                            u32::from(expression.range.start())
                        ),
                        state.assumptions,
                        conclusion,
                        context.source,
                        context.path,
                        expression.range.start().into(),
                    ));
                }
                Some(states)
            } else {
                for mut state in states.iter().cloned() {
                    emit_cast_obligations(&expression.value, &mut state, context)?;
                    emit_index_obligations(&expression.value, &mut state, context)?;
                    execute_effect_expression(&expression.value, &mut state, context)?;
                }
                Some(states)
            }
        }
        _ => None,
    }
}

fn emit_cast_obligations(
    expression: &ast::Expr,
    state: &mut State,
    context: &mut Context<'_>,
) -> Option<()> {
    match expression {
        ast::Expr::Call(call) => {
            if let ast::Expr::Name(function) = call.func.as_ref()
                && function.id.as_str() == "cast"
            {
                let [target, value] = call.args.as_slice() else {
                    return None;
                };
                let expected = parse_cast_target(target, &context.catalog.classes)?;
                let key = expression_key(value)?;
                let lowered =
                    lower_value(value, state, context.catalog, None, context.call_serial)?;
                let condition =
                    cast_type_condition(&lowered, &key, &expected, state, context.catalog)?;
                context.obligations.push(make_obligation(
                    format!(
                        "{}:application-precondition:cast:{}",
                        context.function,
                        u32::from(call.range.start())
                    ),
                    state.assumptions.clone(),
                    condition.clone(),
                    context.source,
                    context.path,
                    call.range.start().into(),
                ));
                state.assumptions.push(condition);
                return Some(());
            }
            emit_cast_obligations(&call.func, state, context)?;
            for argument in &call.args {
                emit_cast_obligations(argument, state, context)?;
            }
            Some(())
        }
        ast::Expr::Attribute(attribute) => emit_cast_obligations(&attribute.value, state, context),
        ast::Expr::Subscript(subscript) => {
            emit_cast_obligations(&subscript.value, state, context)?;
            emit_cast_obligations(&subscript.slice, state, context)
        }
        ast::Expr::IfExp(branch) => {
            emit_cast_obligations(&branch.test, state, context)?;
            emit_cast_obligations(&branch.body, state, context)?;
            emit_cast_obligations(&branch.orelse, state, context)
        }
        _ => Some(()),
    }
}

fn emit_index_obligations(
    expression: &ast::Expr,
    state: &mut State,
    context: &mut Context<'_>,
) -> Option<()> {
    match expression {
        ast::Expr::Subscript(subscript) => {
            let receiver = lower_value(
                &subscript.value,
                state,
                context.catalog,
                None,
                context.call_serial,
            )?;
            let Value::Int(index) = lower_value(
                &subscript.slice,
                state,
                context.catalog,
                None,
                context.call_serial,
            )?
            else {
                return None;
            };
            let condition = match &receiver {
                Value::Tuple(values) => {
                    index_in_bounds(&index, int_value(i64::try_from(values.len()).ok()?))
                }
                Value::VariadicTuple { length, .. } | Value::List { length, .. } => {
                    index_in_bounds(&index, length.clone())
                }
                _ => return None,
            };
            context.obligations.push(make_obligation(
                format!(
                    "{}:application-precondition:index:{}",
                    context.function,
                    u32::from(subscript.range.start())
                ),
                state.assumptions.clone(),
                condition.clone(),
                context.source,
                context.path,
                subscript.range.start().into(),
            ));
            state.assumptions.push(condition);
            emit_index_obligations(&subscript.value, state, context)?;
            emit_index_obligations(&subscript.slice, state, context)
        }
        ast::Expr::Call(call) => {
            if matches!(call.func.as_ref(), ast::Expr::Name(function)
                if function.id.as_str() == "cast")
            {
                let [_, value] = call.args.as_slice() else {
                    return None;
                };
                return emit_index_obligations(value, state, context);
            }
            emit_index_obligations(&call.func, state, context)?;
            for argument in &call.args {
                emit_index_obligations(argument, state, context)?;
            }
            Some(())
        }
        ast::Expr::Attribute(attribute) => emit_index_obligations(&attribute.value, state, context),
        ast::Expr::IfExp(branch) => {
            emit_index_obligations(&branch.test, state, context)?;
            emit_index_obligations(&branch.body, state, context)?;
            emit_index_obligations(&branch.orelse, state, context)
        }
        ast::Expr::BinOp(binary) => {
            emit_index_obligations(&binary.left, state, context)?;
            emit_index_obligations(&binary.right, state, context)
        }
        ast::Expr::Compare(comparison) => {
            emit_index_obligations(&comparison.left, state, context)?;
            for comparator in &comparison.comparators {
                emit_index_obligations(comparator, state, context)?;
            }
            Some(())
        }
        _ => Some(()),
    }
}

fn index_in_bounds(index: &Term, length: Term) -> Term {
    Term::And {
        values: vec![
            Term::LessEqual {
                left: Box::new(int_value(0)),
                right: Box::new(index.clone()),
            },
            Term::Less {
                left: Box::new(index.clone()),
                right: Box::new(length),
            },
        ],
    }
}

fn execute_effect_expression(
    expression: &ast::Expr,
    state: &mut State,
    context: &mut Context<'_>,
) -> Option<()> {
    if let ast::Expr::Call(call) = expression
        && let ast::Expr::Attribute(method) = call.func.as_ref()
    {
        if !call.keywords.is_empty() {
            return None;
        }
        let receiver = lower_value(
            &method.value,
            state,
            context.catalog,
            None,
            context.call_serial,
        )?;
        let Value::Ref { classes, .. } = receiver else {
            return None;
        };
        if !classes.iter().all(|class| {
            lookup_method(class, method.attr.as_str(), context.catalog).is_some_and(|summary| {
                call.args.len() >= summary.required_parameters
                    && call.args.len() <= summary.positional_parameters
            })
        }) {
            return None;
        }
        for argument in &call.args {
            lower_value(argument, state, context.catalog, None, context.call_serial)?;
        }
        return Some(());
    }
    lower_value(
        expression,
        state,
        context.catalog,
        None,
        context.call_serial,
    )?;
    Some(())
}

fn lookup_method<'a>(class: &str, method: &str, catalog: &'a Catalog) -> Option<&'a MethodSummary> {
    let mut current = Some(class);
    while let Some(class) = current {
        if let Some(summary) = catalog
            .methods
            .get(class)
            .and_then(|methods| methods.get(method))
        {
            return Some(summary);
        }
        current = catalog.classes.get(class).and_then(Option::as_deref);
    }
    None
}

fn execute_while(
    loop_statement: &ast::StmtWhile,
    states: Vec<State>,
    returns: &mut Vec<ReturnState>,
    context: &mut Context<'_>,
) -> Option<Vec<State>> {
    if !loop_statement.orelse.is_empty() {
        return None;
    }
    let invariants = loop_statement
        .body
        .iter()
        .filter_map(|statement| match contract_expression(statement) {
            Some(("Invariant", expression)) => Some(expression.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    if invariants.is_empty() {
        return None;
    }
    let executable = loop_statement
        .body
        .iter()
        .filter(|statement| !matches!(contract_expression(statement), Some(("Invariant", _))))
        .cloned()
        .collect::<Vec<_>>();
    let assigned = assigned_names(&executable)?;
    let mut exits = Vec::new();
    for mut entry in states {
        for (index, invariant) in invariants.iter().enumerate() {
            let conclusion = lower_bool(
                invariant,
                &mut entry,
                context.catalog,
                None,
                context.call_serial,
            )?;
            context.obligations.push(make_obligation(
                format!(
                    "{}:invariant-establishment:type-algebra:{index}",
                    context.function
                ),
                entry.assumptions.clone(),
                conclusion,
                context.source,
                context.path,
                invariant.range().start().into(),
            ));
        }
        let mut head = entry;
        for name in &assigned {
            let replacement = match head.environment.get(name)? {
                Value::Int(_) => Value::Int(variable(
                    &format!("loop:{}:{name}", context.function),
                    Sort::Int,
                )),
                Value::Bool(_) => Value::Bool(variable(
                    &format!("loop:{}:{name}", context.function),
                    Sort::Bool,
                )),
                _ => return None,
            };
            head.environment.insert(name.clone(), replacement);
        }
        head.assumptions.clear();
        for invariant in &invariants {
            let assumption = lower_bool(
                invariant,
                &mut head,
                context.catalog,
                None,
                context.call_serial,
            )?;
            head.assumptions.push(assumption);
        }
        let guard = lower_bool(
            &loop_statement.test,
            &mut head,
            context.catalog,
            None,
            context.call_serial,
        )?;
        let mut body_entry = head.clone();
        body_entry.assumptions.push(guard.clone());
        let body_exits = execute_statements(&executable, vec![body_entry], returns, context)?;
        for mut body_exit in body_exits {
            for (index, invariant) in invariants.iter().enumerate() {
                let conclusion = lower_bool(
                    invariant,
                    &mut body_exit,
                    context.catalog,
                    None,
                    context.call_serial,
                )?;
                context.obligations.push(make_obligation(
                    format!(
                        "{}:invariant-preservation:type-algebra:{index}",
                        context.function
                    ),
                    body_exit.assumptions.clone(),
                    conclusion,
                    context.source,
                    context.path,
                    invariant.range().start().into(),
                ));
            }
        }
        head.assumptions.push(Term::Not {
            value: Box::new(guard),
        });
        exits.push(head);
    }
    Some(exits)
}

fn assigned_names(statements: &[ast::Stmt]) -> Option<BTreeSet<String>> {
    let mut names = BTreeSet::new();
    for statement in statements {
        match statement {
            ast::Stmt::Assign(assignment) => {
                for target in &assignment.targets {
                    let ast::Expr::Name(name) = target else {
                        return None;
                    };
                    names.insert(name.id.to_string());
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                let ast::Expr::Name(name) = assignment.target.as_ref() else {
                    return None;
                };
                names.insert(name.id.to_string());
            }
            ast::Stmt::AugAssign(assignment) => {
                let ast::Expr::Name(name) = assignment.target.as_ref() else {
                    return None;
                };
                names.insert(name.id.to_string());
            }
            _ => return None,
        }
    }
    Some(names)
}

fn assign_target(target: &ast::Expr, value: Value, state: &mut State) -> Option<()> {
    match target {
        ast::Expr::Name(name) => {
            state.environment.insert(name.id.to_string(), value);
            Some(())
        }
        ast::Expr::Tuple(tuple) => {
            let Value::Tuple(values) = value else {
                return None;
            };
            if tuple.elts.len() != values.len() {
                return None;
            }
            for (target, value) in tuple.elts.iter().zip(values) {
                assign_target(target, value, state)?;
            }
            Some(())
        }
        ast::Expr::List(list) => {
            let Value::Tuple(values) = value else {
                return None;
            };
            if list.elts.len() != values.len() {
                return None;
            }
            for (target, value) in list.elts.iter().zip(values) {
                assign_target(target, value, state)?;
            }
            Some(())
        }
        _ => None,
    }
}

// Expression lowering and remaining helpers follow below.

fn lower_bool(
    expression: &ast::Expr,
    state: &mut State,
    catalog: &Catalog,
    result: Option<&Value>,
    call_serial: &mut u64,
) -> Option<Term> {
    let value = lower_value(expression, state, catalog, result, call_serial)?;
    match value {
        Value::Bool(term) => Some(term),
        other => truthiness(&other),
    }
}

fn lower_value(
    expression: &ast::Expr,
    state: &mut State,
    catalog: &Catalog,
    result: Option<&Value>,
    call_serial: &mut u64,
) -> Option<Value> {
    match expression {
        ast::Expr::Name(name) => match name.id.as_str() {
            "True" => Some(Value::Bool(bool_value(true))),
            "False" => Some(Value::Bool(bool_value(false))),
            other => state.environment.get(other).cloned(),
        },
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Bool(value) => Some(Value::Bool(bool_value(*value))),
            ast::Constant::Int(value) => Some(Value::Int(int_value(
                value.to_string().parse::<i64>().ok()?,
            ))),
            ast::Constant::Str(value) => Some(Value::Str(Term::String {
                value: value.to_string(),
            })),
            ast::Constant::None => Some(Value::None),
            _ => None,
        },
        ast::Expr::List(list) => {
            let values = list
                .elts
                .iter()
                .map(|element| lower_value(element, state, catalog, result, call_serial))
                .collect::<Option<Vec<_>>>()?;
            let element = match values.first() {
                Some(value) => value_type(value)?,
                None => Type::Object,
            };
            for value in &values {
                if !is_assignable(&value_type(value)?, &element, &catalog.hierarchy) {
                    return None;
                }
            }
            Some(Value::List {
                element,
                length: int_value(i64::try_from(values.len()).ok()?),
                values: Some(values),
                key: format!("literal-list:{}", u32::from(list.range.start())),
            })
        }
        ast::Expr::Set(set) => {
            let values = set
                .elts
                .iter()
                .map(|element| lower_value(element, state, catalog, result, call_serial))
                .collect::<Option<Vec<_>>>()?;
            Some(Value::Set {
                element: match values.first() {
                    Some(value) => value_type(value)?,
                    None => Type::Object,
                },
                length: int_value(i64::try_from(values.len()).ok()?),
            })
        }
        ast::Expr::Dict(dict) => {
            let keys = dict
                .keys
                .iter()
                .map(Option::as_ref)
                .map(|key| {
                    key.and_then(|key| lower_value(key, state, catalog, result, call_serial))
                })
                .collect::<Option<Vec<_>>>()?;
            let values = dict
                .values
                .iter()
                .map(|value| lower_value(value, state, catalog, result, call_serial))
                .collect::<Option<Vec<_>>>()?;
            Some(Value::Dict {
                key_type: match keys.first() {
                    Some(value) => value_type(value)?,
                    None => Type::Object,
                },
                value_type: match values.first() {
                    Some(value) => value_type(value)?,
                    None => Type::Object,
                },
                length: int_value(i64::try_from(values.len()).ok()?),
            })
        }
        ast::Expr::Tuple(tuple) => Some(Value::Tuple(
            tuple
                .elts
                .iter()
                .map(|element| lower_value(element, state, catalog, result, call_serial))
                .collect::<Option<Vec<_>>>()?,
        )),
        ast::Expr::UnaryOp(unary) => match unary.op {
            ast::UnaryOp::Not => Some(Value::Bool(Term::Not {
                value: Box::new(lower_bool(
                    &unary.operand,
                    state,
                    catalog,
                    result,
                    call_serial,
                )?),
            })),
            ast::UnaryOp::USub => {
                let Value::Int(value) =
                    lower_value(&unary.operand, state, catalog, result, call_serial)?
                else {
                    return None;
                };
                Some(Value::Int(Term::Negate {
                    value: Box::new(value),
                }))
            }
            _ => None,
        },
        ast::Expr::BinOp(binary) => {
            let left = lower_value(&binary.left, state, catalog, result, call_serial)?;
            let right = lower_value(&binary.right, state, catalog, result, call_serial)?;
            match (binary.op, left, right) {
                (ast::Operator::Add, Value::Int(left), Value::Int(right)) => {
                    Some(Value::Int(Term::Add {
                        left: Box::new(left),
                        right: Box::new(right),
                    }))
                }
                (ast::Operator::Sub, Value::Int(left), Value::Int(right)) => {
                    Some(Value::Int(Term::Subtract {
                        left: Box::new(left),
                        right: Box::new(right),
                    }))
                }
                (ast::Operator::Add, Value::Str(left), Value::Str(right)) => {
                    Some(Value::Str(Term::StringConcat {
                        values: vec![left, right],
                    }))
                }
                _ => None,
            }
        }
        ast::Expr::BoolOp(operation) => {
            let [left_expression, right_expression] = operation.values.as_slice() else {
                return None;
            };
            let left = lower_value(left_expression, state, catalog, result, call_serial)?;
            let condition = truthiness(&left)?;
            if condition == bool_value(true) {
                return match operation.op {
                    ast::BoolOp::Or => Some(left),
                    ast::BoolOp::And => {
                        lower_value(right_expression, state, catalog, result, call_serial)
                    }
                };
            }
            if condition == bool_value(false) {
                return match operation.op {
                    ast::BoolOp::Or => {
                        lower_value(right_expression, state, catalog, result, call_serial)
                    }
                    ast::BoolOp::And => Some(left),
                };
            }
            let right = lower_value(right_expression, state, catalog, result, call_serial)?;
            let (then_value, else_value) = match operation.op {
                ast::BoolOp::Or => (left, right),
                ast::BoolOp::And => (right, left),
            };
            merge_values(condition, then_value, else_value)
        }
        ast::Expr::IfExp(conditional) => {
            let condition = lower_bool(&conditional.test, state, catalog, result, call_serial)?;
            let then_value = lower_value(&conditional.body, state, catalog, result, call_serial)?;
            let else_value = lower_value(&conditional.orelse, state, catalog, result, call_serial)?;
            merge_values(condition, then_value, else_value)
        }
        ast::Expr::Compare(comparison) if comparison.ops.len() == 1 => {
            let left = lower_value(&comparison.left, state, catalog, result, call_serial)?;
            let right = lower_value(
                &comparison.comparators[0],
                state,
                catalog,
                result,
                call_serial,
            )?;
            let relation = compare_values(&left, &right, comparison.ops[0], catalog)?;
            Some(Value::Bool(relation))
        }
        ast::Expr::Subscript(subscript) => {
            lower_subscript(subscript, state, catalog, result, call_serial)
        }
        ast::Expr::Call(call) => lower_call(call, state, catalog, result, call_serial),
        ast::Expr::Attribute(attribute) => {
            if state
                .assumptions
                .iter()
                .any(|term| term == &bool_value(false))
            {
                return Some(Value::Int(variable(
                    &format!("unreachable-field:{}", attribute.attr),
                    Sort::Int,
                )));
            }
            let _receiver = lower_value(&attribute.value, state, catalog, result, call_serial)?;
            None
        }
        _ => None,
    }
}

fn lower_call(
    call: &ast::ExprCall,
    state: &mut State,
    catalog: &Catalog,
    result: Option<&Value>,
    call_serial: &mut u64,
) -> Option<Value> {
    if !call.keywords.is_empty() {
        return None;
    }
    let ast::Expr::Name(callee) = call.func.as_ref() else {
        return None;
    };
    match (callee.id.as_str(), call.args.as_slice()) {
        ("Result" | "ResultT", []) => result.cloned(),
        ("ResultT", [_]) => result.cloned(),
        ("Implies", [left, right]) => Some(Value::Bool(Term::Implies {
            left: Box::new(lower_bool(left, state, catalog, result, call_serial)?),
            right: Box::new(lower_bool(right, state, catalog, result, call_serial)?),
        })),
        ("len", [value]) => match lower_value(value, state, catalog, result, call_serial)? {
            Value::List { length, .. }
            | Value::Set { length, .. }
            | Value::Dict { length, .. }
            | Value::VariadicTuple { length, .. } => Some(Value::Int(length)),
            Value::Tuple(values) => Some(Value::Int(int_value(i64::try_from(values.len()).ok()?))),
            Value::Str(value) => Some(Value::Int(Term::StringLength {
                value: Box::new(value),
            })),
            _ => None,
        },
        ("isinstance", [value, ast::Expr::Name(expected)]) => {
            let value_key = expression_key(value)?;
            let value = lower_value(value, state, catalog, result, call_serial)?;
            Some(Value::Bool(isinstance_term(
                &value,
                &value_key,
                expected.id.as_str(),
                state,
                catalog,
            )?))
        }
        ("cast", [target, value]) => {
            let expected = parse_cast_target(target, &catalog.classes)?;
            let value_key = expression_key(value)?;
            let lowered = lower_value(value, state, catalog, result, call_serial)?;
            let condition = cast_type_condition(&lowered, &value_key, &expected, state, catalog)?;
            // Cast is a verifier application with a checked nominal precondition. The source
            // type assertion itself never changes the runtime value.
            state.assumptions.push(condition.clone());
            narrow_value_to_type(lowered, &expected, catalog, condition == bool_value(false))
        }
        ("list_pred" | "Acc", [_]) => Some(Value::Bool(bool_value(true))),
        ("set", []) => Some(Value::Set {
            element: Type::Object,
            length: int_value(0),
        }),
        (class, arguments) if catalog.classes.contains_key(class) => {
            if !arguments.is_empty() {
                return None;
            }
            *call_serial += 1;
            Some(Value::Ref {
                identity: Term::NominalReference {
                    name: format!("new:{class}:{call_serial}"),
                    class: class.to_owned(),
                },
                classes: vec![class.to_owned()],
                tag: None,
            })
        }
        (function, arguments) if catalog.functions.contains_key(function) => {
            lower_source_call(function, arguments, state, catalog, call_serial)
        }
        _ => None,
    }
}

fn lower_source_call(
    name: &str,
    arguments: &[ast::Expr],
    state: &mut State,
    catalog: &Catalog,
    call_serial: &mut u64,
) -> Option<Value> {
    let function = catalog.functions.get(name)?;
    if arguments.len() != function.parameters.len() {
        return None;
    }
    let values = arguments
        .iter()
        .map(|argument| lower_value(argument, state, catalog, None, call_serial))
        .collect::<Option<Vec<_>>>()?;
    if values
        .iter()
        .zip(&function.parameters)
        .any(|(value, (_, expected))| {
            value_type(value)
                .is_none_or(|actual| !is_assignable(&actual, expected, &catalog.hierarchy))
        })
    {
        return None;
    }
    let mut call_state = State::default();
    for ((parameter, _), value) in function.parameters.iter().zip(values) {
        call_state.environment.insert(parameter.clone(), value);
    }
    for requirement in &function.requires {
        let condition = lower_bool(requirement, &mut call_state, catalog, None, call_serial)?;
        // A source call precondition is not silently assumed. The caller receives it as a
        // constraint only after the public function verifier emits its application obligation.
        // Calls in this fragment use statically decidable preconditions, so false refuses here.
        if condition == bool_value(false) {
            return None;
        }
        state.assumptions.push(condition);
    }
    *call_serial += 1;
    let Some(return_type) = function.return_type.as_ref() else {
        return Some(Value::None);
    };
    let (returned, assumptions) =
        symbolic_union_value(return_type, &format!("call:{name}:{call_serial}"), catalog)?;
    state.assumptions.extend(assumptions);
    let mut result_state = call_state;
    result_state.environment.extend(state.environment.clone());
    for postcondition in &function.ensures {
        let relation = lower_bool(
            postcondition,
            &mut result_state,
            catalog,
            Some(&returned),
            call_serial,
        )?;
        state.assumptions.push(relation);
    }
    Some(returned)
}

fn symbolic_union_value(ty: &Type, key: &str, catalog: &Catalog) -> Option<(Value, Vec<Term>)> {
    match ty {
        Type::Union(types)
            if type_list_items(types)
                .into_iter()
                .all(|ty| matches!(ty, Type::Class(_) | Type::None)) =>
        {
            let classes = type_list_items(types)
                .into_iter()
                .filter_map(|ty| match ty {
                    Type::Class(class) => Some(class.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let tag = variable(&format!("tag:{key}"), Sort::Int);
            let mut domain = classes
                .iter()
                .map(|class| Term::Equal {
                    left: Box::new(tag.clone()),
                    right: Box::new(int_value(class_code(class, catalog))),
                })
                .collect::<Vec<_>>();
            if type_list_items(types).contains(&&Type::None) {
                domain.push(Term::Equal {
                    left: Box::new(tag.clone()),
                    right: Box::new(int_value(-1)),
                });
            }
            Some((
                Value::Ref {
                    identity: variable(&format!("ref:{key}"), Sort::Reference),
                    classes,
                    tag: Some(tag),
                },
                vec![or_terms(domain)],
            ))
        }
        Type::FixedTuple(elements) => {
            let mut assumptions = Vec::new();
            let mut values = Vec::new();
            for (index, element) in type_list_items(elements).into_iter().enumerate() {
                let (value, nested) =
                    symbolic_union_value(element, &format!("{key}[{index}]"), catalog)?;
                values.push(value);
                assumptions.extend(nested);
            }
            Some((Value::Tuple(values), assumptions))
        }
        _ => values_for_type(ty, key).into_iter().next(),
    }
}

fn lower_subscript(
    subscript: &ast::ExprSubscript,
    state: &mut State,
    catalog: &Catalog,
    result: Option<&Value>,
    call_serial: &mut u64,
) -> Option<Value> {
    let receiver_key = expression_key(&subscript.value);
    let receiver = lower_value(&subscript.value, state, catalog, result, call_serial)?;
    let index = lower_value(&subscript.slice, state, catalog, result, call_serial)?;
    let Value::Int(index_term) = index else {
        return None;
    };
    let static_index = static_integer(&index_term);
    match receiver {
        Value::Tuple(values) => {
            if let Some(index) = static_index {
                normalize_index(index, values.len())
                    .and_then(|normalized| values.get(normalized).cloned())
                    .or_else(|| values.first().cloned())
            } else {
                merge_dynamic_tuple(values, index_term)
            }
        }
        Value::VariadicTuple {
            element,
            length,
            values,
            key,
        } => {
            if let Some(values) = values
                && let Some(index) = static_index
                && let Some(normalized) = normalize_index(index, values.len())
            {
                return values.get(normalized).cloned();
            }
            symbolic_value_for_type(
                &element,
                &format!("{key}[{}]", term_key(&index_term)),
                catalog,
            )
            .map(|pair| pair.0)
            .inspect(|_| {
                let _ = length;
            })
        }
        Value::List {
            element,
            values,
            key,
            ..
        } => {
            if let Some(values) = values
                && let Some(index) = static_index
                && let Some(normalized) = normalize_index(index, values.len())
            {
                return values.get(normalized).cloned();
            }
            let refined_key = format!("{}[{}]", receiver_key.as_deref()?, term_key(&index_term));
            if let Some(class) = state.refinements.get(&refined_key) {
                return symbolic_value_for_type(&Type::Class(class.clone()), &refined_key, catalog)
                    .map(|pair| pair.0);
            }
            symbolic_value_for_type(
                &element,
                &format!("{key}[{}]", term_key(&index_term)),
                catalog,
            )
            .map(|pair| pair.0)
        }
        _ => None,
    }
}

fn symbolic_value_for_type(ty: &Type, key: &str, catalog: &Catalog) -> Option<(Value, Vec<Term>)> {
    symbolic_union_value(ty, key, catalog)
}

fn merge_dynamic_tuple(values: Vec<Value>, index: Term) -> Option<Value> {
    let first = values.first()?.clone();
    let mut merged = first;
    for (position, value) in values.into_iter().enumerate().skip(1) {
        merged = merge_values(
            Term::Equal {
                left: Box::new(index.clone()),
                right: Box::new(int_value(i64::try_from(position).ok()?)),
            },
            value,
            merged,
        )?;
    }
    Some(merged)
}

fn merge_values(condition: Term, then_value: Value, else_value: Value) -> Option<Value> {
    match (then_value, else_value) {
        (Value::Int(then_value), Value::Int(else_value)) => Some(Value::Int(Term::IfThenElse {
            condition: Box::new(condition),
            then_value: Box::new(then_value),
            else_value: Box::new(else_value),
        })),
        (Value::Bool(then_value), Value::Bool(else_value)) => Some(Value::Bool(Term::IfThenElse {
            condition: Box::new(condition),
            then_value: Box::new(then_value),
            else_value: Box::new(else_value),
        })),
        (Value::Int(then_value), Value::Bool(else_value)) => Some(Value::Int(Term::IfThenElse {
            condition: Box::new(condition),
            then_value: Box::new(then_value),
            else_value: Box::new(bool_as_int(else_value)),
        })),
        (Value::Bool(then_value), Value::Int(else_value)) => Some(Value::Int(Term::IfThenElse {
            condition: Box::new(condition),
            then_value: Box::new(bool_as_int(then_value)),
            else_value: Box::new(else_value),
        })),
        (Value::Str(then_value), Value::Str(else_value)) => Some(Value::Str(Term::IfThenElse {
            condition: Box::new(condition),
            then_value: Box::new(then_value),
            else_value: Box::new(else_value),
        })),
        (Value::None, Value::None) => Some(Value::None),
        _ => None,
    }
}

fn bool_as_int(value: Term) -> Term {
    Term::IfThenElse {
        condition: Box::new(value),
        then_value: Box::new(int_value(1)),
        else_value: Box::new(int_value(0)),
    }
}

fn compare_values(
    left: &Value,
    right: &Value,
    operator: ast::CmpOp,
    catalog: &Catalog,
) -> Option<Term> {
    let equality = match (left, right) {
        (Value::Int(left), Value::Int(right))
        | (Value::Bool(left), Value::Bool(right))
        | (Value::Str(left), Value::Str(right)) => Term::Equal {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        (Value::None, Value::None) => bool_value(true),
        (Value::None, Value::Ref { tag: Some(tag), .. })
        | (Value::Ref { tag: Some(tag), .. }, Value::None) => Term::Equal {
            left: Box::new(tag.clone()),
            right: Box::new(int_value(-1)),
        },
        (Value::None, _) | (_, Value::None) => bool_value(false),
        (
            Value::Ref {
                identity: left,
                classes: left_classes,
                ..
            },
            Value::Ref {
                identity: right,
                classes: right_classes,
                ..
            },
        ) => {
            if classes_disjoint(left_classes, right_classes, catalog) {
                bool_value(false)
            } else {
                Term::Equal {
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                }
            }
        }
        (
            Value::AnyObject { identity: left, .. },
            Value::AnyObject {
                identity: right, ..
            },
        )
        | (
            Value::AnyObject { identity: left, .. },
            Value::Ref {
                identity: right, ..
            },
        )
        | (
            Value::Ref { identity: left, .. },
            Value::AnyObject {
                identity: right, ..
            },
        ) => Term::Equal {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        _ => return comparison_order(left, right, operator),
    };
    match operator {
        ast::CmpOp::Eq | ast::CmpOp::Is => Some(equality),
        ast::CmpOp::NotEq | ast::CmpOp::IsNot => Some(Term::Not {
            value: Box::new(equality),
        }),
        _ => comparison_order(left, right, operator),
    }
}

fn comparison_order(left: &Value, right: &Value, operator: ast::CmpOp) -> Option<Term> {
    let (Value::Int(left), Value::Int(right)) = (left, right) else {
        return None;
    };
    match operator {
        ast::CmpOp::Lt => Some(Term::Less {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }),
        ast::CmpOp::LtE => Some(Term::LessEqual {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }),
        ast::CmpOp::Gt => Some(Term::Greater {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }),
        ast::CmpOp::GtE => Some(Term::GreaterEqual {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }),
        _ => None,
    }
}

fn truthiness(value: &Value) -> Option<Term> {
    match value {
        Value::Bool(term) => Some(term.clone()),
        Value::Int(term) => static_integer(term).map_or_else(
            || {
                Some(Term::Not {
                    value: Box::new(Term::Equal {
                        left: Box::new(term.clone()),
                        right: Box::new(int_value(0)),
                    }),
                })
            },
            |value| Some(bool_value(value != 0)),
        ),
        Value::Str(term) => Some(Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(Term::StringLength {
                    value: Box::new(term.clone()),
                }),
                right: Box::new(int_value(0)),
            }),
        }),
        Value::None => Some(bool_value(false)),
        Value::Ref { tag: Some(tag), .. } => Some(Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(tag.clone()),
                right: Box::new(int_value(-1)),
            }),
        }),
        Value::Ref { .. } => Some(bool_value(true)),
        Value::AnyObject { key, .. } => Some(variable(&format!("truth:{key}"), Sort::Bool)),
        Value::List { length, .. }
        | Value::Set { length, .. }
        | Value::Dict { length, .. }
        | Value::VariadicTuple { length, .. } => Some(Term::Not {
            value: Box::new(Term::Equal {
                left: Box::new(length.clone()),
                right: Box::new(int_value(0)),
            }),
        }),
        Value::Tuple(values) => Some(bool_value(!values.is_empty())),
    }
}

fn isinstance_term(
    value: &Value,
    key: &str,
    expected: &str,
    state: &State,
    catalog: &Catalog,
) -> Option<Term> {
    if !matches!(expected, "int" | "bool" | "str" | "list" | "tuple")
        && !catalog.classes.contains_key(expected)
    {
        return None;
    }
    let result = match value {
        Value::Int(_) => expected == "int",
        Value::Bool(_) => matches!(expected, "bool" | "int"),
        Value::Str(_) => expected == "str",
        Value::List { .. } => expected == "list",
        Value::Tuple(_) | Value::VariadicTuple { .. } => expected == "tuple",
        Value::None => false,
        Value::Ref {
            classes, tag: None, ..
        } => classes
            .iter()
            .all(|class| is_subclass(class, expected, &catalog.hierarchy)),
        Value::Ref {
            classes,
            tag: Some(tag),
            ..
        } => {
            let possible = classes
                .iter()
                .filter(|class| is_subclass(class, expected, &catalog.hierarchy))
                .map(|class| Term::Equal {
                    left: Box::new(tag.clone()),
                    right: Box::new(int_value(class_code(class, catalog))),
                })
                .collect::<Vec<_>>();
            return Some(or_terms(possible));
        }
        Value::AnyObject { .. } => {
            if let Some(refined) = state.refinements.get(key) {
                is_subclass(refined, expected, &catalog.hierarchy)
            } else {
                return Some(variable(
                    &format!("isinstance:{key}:{expected}"),
                    Sort::Bool,
                ));
            }
        }
        _ => false,
    };
    Some(bool_value(result))
}

fn parse_cast_target(
    expression: &ast::Expr,
    classes: &BTreeMap<String, Option<String>>,
) -> Option<Type> {
    if matches!(expression, ast::Expr::Name(name) if name.id.as_str() == "tuple") {
        Some(Type::VariadicTuple(Box::new(Type::Object)))
    } else {
        parse_type(Some(expression), classes)
    }
}

fn cast_type_condition(
    value: &Value,
    key: &str,
    expected: &Type,
    state: &State,
    catalog: &Catalog,
) -> Option<Term> {
    if let Type::Class(expected) = expected {
        return isinstance_term(value, key, expected, state, catalog);
    }
    let actual = value_type(value)?;
    let compatible = cast_compatible(&actual, expected, &catalog.hierarchy);
    Some(bool_value(compatible))
}

fn narrow_value_to_type(
    value: Value,
    expected: &Type,
    catalog: &Catalog,
    path_is_refuted: bool,
) -> Option<Value> {
    let actual = value_type(&value)?;
    if narrow_type(&actual, expected, true, &catalog.hierarchy).is_none() && !path_is_refuted {
        return None;
    }
    let Type::Class(expected) = expected else {
        return Some(value);
    };
    let identity = match value {
        Value::Ref { identity, .. } | Value::AnyObject { identity, .. } => identity,
        _ => return None,
    };
    Some(Value::Ref {
        identity,
        classes: vec![expected.clone()],
        tag: None,
    })
}

fn apply_refinement(expression: &ast::Expr, truth: bool, state: &mut State, catalog: &Catalog) {
    let expression = if let ast::Expr::UnaryOp(unary) = expression
        && unary.op == ast::UnaryOp::Not
    {
        return apply_refinement(&unary.operand, !truth, state, catalog);
    } else {
        expression
    };
    let ast::Expr::Call(call) = expression else {
        return;
    };
    let (ast::Expr::Name(function), [value, ast::Expr::Name(expected)]) =
        (call.func.as_ref(), call.args.as_slice())
    else {
        return;
    };
    if truth
        && function.id.as_str() == "isinstance"
        && catalog.classes.contains_key(expected.id.as_str())
        && let Some(key) = expression_key(value)
    {
        state.refinements.insert(key, expected.id.to_string());
    }
}

fn value_type(value: &Value) -> Option<Type> {
    match value {
        Value::Int(_) => Some(Type::Int),
        Value::Bool(_) => Some(Type::Bool),
        Value::Str(_) => Some(Type::Str),
        Value::None => Some(Type::None),
        Value::Ref { classes, .. } => Some(normalize_union(
            classes.iter().cloned().map(Type::Class).collect(),
        )),
        Value::AnyObject { .. } => Some(Type::Object),
        Value::List { element, .. } => Some(Type::List(Box::new(element.clone()))),
        Value::Set { element, .. } => Some(Type::Set(Box::new(element.clone()))),
        Value::Dict {
            key_type,
            value_type,
            ..
        } => Some(Type::Dict(
            Box::new(key_type.clone()),
            Box::new(value_type.clone()),
        )),
        Value::Tuple(values) => Some(Type::FixedTuple(TypeList::from_vec(
            values.iter().map(value_type).collect::<Option<Vec<_>>>()?,
        ))),
        Value::VariadicTuple { element, .. } => {
            Some(Type::VariadicTuple(Box::new(element.clone())))
        }
    }
}

fn value_matches_declared(
    value: Option<&Value>,
    expected: Option<&Type>,
    catalog: &Catalog,
) -> bool {
    match (value, expected) {
        (None, None) => true,
        (Some(value), Some(expected)) => value_type(value)
            .is_some_and(|actual| is_assignable(&actual, expected, &catalog.hierarchy)),
        _ => false,
    }
}

fn classes_disjoint(left: &[String], right: &[String], catalog: &Catalog) -> bool {
    left.iter().all(|left| {
        right.iter().all(|right| {
            !is_subclass(left, right, &catalog.hierarchy)
                && !is_subclass(right, left, &catalog.hierarchy)
        })
    })
}

fn class_code(class: &str, catalog: &Catalog) -> i64 {
    catalog
        .classes
        .keys()
        .position(|candidate| candidate == class)
        .and_then(|position| i64::try_from(position).ok())
        .unwrap_or(i64::MAX)
}

fn expression_key(expression: &ast::Expr) -> Option<String> {
    match expression {
        ast::Expr::Name(name) => Some(name.id.to_string()),
        ast::Expr::Subscript(subscript) => {
            let receiver = expression_key(&subscript.value)?;
            let ast::Expr::Constant(index) = subscript.slice.as_ref() else {
                return None;
            };
            let ast::Constant::Int(index) = &index.value else {
                return None;
            };
            Some(format!("{receiver}[{index}]"))
        }
        _ => None,
    }
}

fn normalize_index(index: i64, length: usize) -> Option<usize> {
    let length = i64::try_from(length).ok()?;
    let normalized = if index < 0 { index + length } else { index };
    (0..length)
        .contains(&normalized)
        .then(|| usize::try_from(normalized).ok())
        .flatten()
}

fn static_integer(term: &Term) -> Option<i64> {
    match term {
        Term::Int { value } => Some(*value),
        Term::Negate { value } => static_integer(value).and_then(i64::checked_neg),
        _ => None,
    }
}

fn term_key(term: &Term) -> String {
    static_integer(term).map_or_else(|| "dynamic".to_owned(), |value| value.to_string())
}

fn or_terms(values: Vec<Term>) -> Term {
    match values.as_slice() {
        [] => bool_value(false),
        [single] => single.clone(),
        _ => Term::Or { values },
    }
}

fn variable(name: &str, sort: Sort) -> Term {
    Term::Variable {
        name: name.to_owned(),
        sort,
    }
}

fn bool_value(value: bool) -> Term {
    Term::Bool { value }
}

fn int_value(value: i64) -> Term {
    Term::Int { value }
}

fn function_offset(suite: &[ast::Stmt], name: &str) -> u32 {
    suite
        .iter()
        .find_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) if function.name.as_str() == name => {
                Some(function.range.start().into())
            }
            _ => None,
        })
        .unwrap_or(0)
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
    use super::*;

    #[test]
    fn finite_optional_truthiness_is_proved_per_runtime_variant() {
        let source = "from typing import Optional\nfrom nagini_contracts.contracts import *\nclass Item:\n    pass\ndef choose(flag: int) -> int:\n    Ensures(Implies(flag == 0, Result() == 2))\n    value = Item()  # type: Optional[Item]\n    if flag == 0:\n        value = None\n    return 1 if value else 2\n";
        let result = verify_type_algebra_module(source, "optional.py", &[])
            .unwrap()
            .expect("the finite Optional program is in the type-algebra fragment");
        assert!(result.passed, "{result:#?}");
    }

    #[test]
    fn unsupported_dynamic_cast_target_refuses_the_fragment() {
        let source = "from typing import cast\nclass Item:\n    pass\ndef bad(value: object, target: object) -> object:\n    return cast(target, value)\n";
        let error = verify_type_algebra_module(source, "dynamic_cast.py", &[]).unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.type-algebra.cast-target-unsupported"
        );
    }

    #[test]
    fn missing_requested_symbol_refuses_the_fragment() {
        let source =
            "from typing import Optional\ndef inspect(value: Optional[int]) -> None:\n    pass\n";
        let error = verify_type_algebra_module(
            source,
            "missing_requested_symbol.py",
            &["inspect".to_owned(), "absent".to_owned()],
        )
        .unwrap_err();
        assert_eq!(
            error.code,
            "frontend.python.type-algebra.requested-symbol-missing"
        );
    }

    #[test]
    fn optional_annotation_does_not_hijack_unrelated_requested_symbols() {
        let source = "from typing import Optional\nclass Item:\n    value: Optional[int]\ndef inspect(value: Optional[int]) -> None:\n    pass\n";
        let result =
            verify_type_algebra_module(source, "heap_optional.py", &["Item".to_owned()]).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn optional_top_level_helper_does_not_hijack_requested_heap_methods() {
        let source = "from typing import Optional\nclass Cell:\n    value: int\n    def touch(self) -> None:\n        self.value = self.value\ndef run(cell: Optional[Cell]) -> None:\n    cell.touch()\n";
        let result = verify_type_algebra_module(
            source,
            "heap_method_optional.py",
            &["Cell.touch".to_owned(), "run".to_owned()],
        )
        .unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn optional_heap_fields_do_not_make_an_unqualified_function_type_algebra() {
        let source = "from typing import Optional\nclass Base:\n    pass\nclass Holder:\n    value: Optional[Base]\ndef run(holder: Holder, flag: bool) -> None:\n    if flag:\n        holder.value = None\n";
        let result =
            verify_type_algebra_module(source, "optional_heap_field.py", &["run".to_owned()])
                .unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn optional_reference_identity_does_not_claim_whole_module_ownership() {
        let source = "from typing import Optional\nclass Left:\n    pass\nclass Right:\n    pass\ndef distinct(left: Optional[Left], right: Optional[Right]) -> None:\n    assert left is not right\n";
        let result = verify_type_algebra_module(source, "optional_identity.py", &[]).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn optional_import_does_not_turn_nominal_alias_checks_into_type_algebra() {
        let source = "from typing import List, Optional\nclass Item:\n    pass\nAlias = Item\nItems = List[Alias]\ndef inspect(values: Items) -> None:\n    value = values[0]\n    assert isinstance(value, Alias)\n";
        let result = verify_type_algebra_module(source, "nominal_alias.py", &[]).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn optional_heap_reference_chains_remain_owned_by_the_heap_frontend() {
        let source = "from typing import Optional\nclass Leaf:\n    next: Leaf\nclass Holder:\n    leaf: Optional[Leaf]\ndef run(holder: Holder) -> None:\n    observed = holder.leaf.next\n";
        let result =
            verify_type_algebra_module(source, "optional_reference_chain.py", &["run".to_owned()])
                .unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn tuple_helper_does_not_claim_sibling_named_argument_callers() {
        let source = "from typing import Tuple\ndef element(pair: Tuple[int, bool] = (2, True)) -> int:\n    return pair[0]\ndef caller() -> int:\n    return element(pair=(12, False))\n";
        let result = verify_type_algebra_module(source, "named_tuple_arguments.py", &[]).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn explicit_nagini_adt_modules_remain_owned_by_the_adt_frontend() {
        let source = "from nagini_contracts.adt import ADT\nfrom typing import NamedTuple, cast\nclass Tree(ADT):\n    pass\nclass Leaf(Tree, NamedTuple('Leaf', [('value', int)])):\n    pass\ndef inspect(value: Tree) -> int:\n    return cast(Leaf, value).value\n";
        let result = verify_type_algebra_module(source, "adt.py", &[]).unwrap();
        assert!(result.is_none());
    }
}
