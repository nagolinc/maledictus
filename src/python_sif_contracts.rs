//! Secure-information-flow lowering for canonical `Low(...)` contracts.
//!
//! This pass is deliberately separate from the ordinary scalar VC language.  `Low(e)` is a
//! relational assertion about two executions, not a boolean property of one value, so treating
//! it as `True` in the ordinary solver would be unsound.  Instead, this module performs a small,
//! fail-closed label analysis over source control flow.  Only after that analysis has established
//! the label at a particular contract occurrence is the occurrence elaborated to the boolean
//! result consumed by the ordinary VC pipeline.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use rustpython_ast::{Fold, Ranged, Visitor};
use rustpython_parser::ast;

use crate::python_contract_positions::InformationFlowVerificationProfile;
use crate::python_contracts::ContractFailure;

const LOW_UNSUPPORTED: &str = "frontend.python.sif.low-form-unsupported";
const CONTRACT_NAMES: [&str; 5] = ["Requires", "Ensures", "Exsures", "Invariant", "Assert"];
const NAGINI_VALUE_NAMES: [&str; 1] = ["Result"];
const BUILTIN_VALUE_CALLS: [&str; 5] = ["len", "type", "bool", "int", "str"];
const TERMINATION_CONTRACT_NAMES: [&str; 5] =
    ["Requires", "Invariant", "Low", "LowEvent", "TerminatesSif"];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SifTerminationFailureKind {
    ConditionNotLow,
    NotLowEvent,
    ConditionNotTight,
    LoopPromiseNotKept,
    CallConditionNotLow,
    CallerUnsatisfied,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SifTerminationFailure {
    pub(super) owner: String,
    pub(super) kind: SifTerminationFailureKind,
    pub(super) offset: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SifTerminationAnalysis {
    pub(super) methods: Vec<String>,
    pub(super) failures: Vec<SifTerminationFailure>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum FlowExit {
    Normal,
    Return { low: bool },
    Raise { class: String, low_control: bool },
    Break,
    Continue,
}

#[derive(Clone, Debug)]
struct LabelState {
    locals: BTreeMap<String, bool>,
    /// Canonical values proved to depend only on Low inputs. These terms deliberately omit the
    /// current PC label: a high conditional may assign the same public value on every arm, in
    /// which case the join can prove that the assignment itself reveals nothing about the guard.
    canonical_low_terms: BTreeMap<String, String>,
    /// Source-independent symbolic terms used only for local relational equalities in the closed
    /// termination-channel fragment. Unlike `canonical_low_terms`, these terms carry no Low
    /// claim; they merely preserve exact assignment identity.
    symbolic_terms: BTreeMap<String, String>,
    fields: BTreeMap<String, bool>,
    exact_low_facts: BTreeSet<String>,
    exact_low_fact_dependencies: BTreeMap<String, BTreeSet<String>>,
    canonical_calls: BTreeSet<String>,
    /// Closed, source-bound direct calls whose complete normal result has been derived from the
    /// real source body or a value postcondition that the ordinary verifier must independently
    /// prove. Keeping this catalog in the path state makes call resolution respect each
    /// function's lexical shadowing without introducing a second global name oracle.
    source_calls: Arc<BTreeMap<String, SourceCallSummary>>,
    pc_low: bool,
    exit: FlowExit,
}

impl LabelState {
    fn normal(parameters: impl Iterator<Item = String>, canonical_calls: BTreeSet<String>) -> Self {
        let parameters = parameters.collect::<Vec<_>>();
        Self {
            locals: parameters
                .iter()
                .cloned()
                .map(|name| (name, false))
                .collect(),
            symbolic_terms: parameters
                .iter()
                .map(|name| (name.clone(), format!("source:{name}")))
                .collect(),
            canonical_low_terms: BTreeMap::new(),
            fields: BTreeMap::new(),
            exact_low_facts: BTreeSet::new(),
            exact_low_fact_dependencies: BTreeMap::new(),
            canonical_calls,
            source_calls: Arc::new(BTreeMap::new()),
            pc_low: true,
            exit: FlowExit::Normal,
        }
    }
}

/// A deliberately small symbolic value algebra for total direct source calls.  It contains no
/// arbitrary Python evaluation: every node is produced only after the source body has passed the
/// exception-closed call scan below.  Parameter nodes are substituted with the caller's actual
/// expressions when labels and canonical terms are evaluated.
#[derive(Clone, Debug, Eq, PartialEq)]
enum SourceSummaryExpression {
    Constant(String),
    Parameter(usize),
    Attribute(Box<SourceSummaryExpression>, String),
    Unary(String, Box<SourceSummaryExpression>),
    Binary(
        String,
        Box<SourceSummaryExpression>,
        Box<SourceSummaryExpression>,
    ),
    Boolean(String, Vec<SourceSummaryExpression>),
    Compare(
        Box<SourceSummaryExpression>,
        Vec<(String, SourceSummaryExpression)>,
    ),
    Conditional(
        Box<SourceSummaryExpression>,
        Box<SourceSummaryExpression>,
        Box<SourceSummaryExpression>,
    ),
    Tuple(Vec<SourceSummaryExpression>),
    List(Vec<SourceSummaryExpression>),
    Set(Vec<SourceSummaryExpression>),
    Dict(Vec<(SourceSummaryExpression, SourceSummaryExpression)>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceCallSummary {
    parameters: Vec<String>,
    result: SourceSummaryExpression,
}

#[derive(Default)]
struct CanonicalLowCalls {
    offsets: Vec<u32>,
}

impl Visitor for CanonicalLowCalls {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if matches!(node.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Low") {
            self.offsets.push(u32::from(node.range.start()));
        }
        self.generic_visit_expr_call(node);
    }
}

struct LowResultRewriter<'a> {
    results: &'a BTreeMap<u32, bool>,
}

struct NamedExpressionBinding {
    name: String,
    found: bool,
}

impl Visitor for NamedExpressionBinding {
    fn visit_expr_named_expr(&mut self, node: ast::ExprNamedExpr) {
        if target_binds_name(&node.target, &self.name) {
            self.found = true;
        }
        self.generic_visit_expr_named_expr(node);
    }

    // Assignment expressions in a nested lexical scope do not bind the containing function.
    fn visit_stmt_function_def(&mut self, _node: ast::StmtFunctionDef) {}

    fn visit_stmt_class_def(&mut self, _node: ast::StmtClassDef) {}

    fn visit_expr_lambda(&mut self, _node: ast::ExprLambda) {}
}

impl Fold<rustpython_ast::text_size::TextRange> for LowResultRewriter<'_> {
    type TargetU = rustpython_ast::text_size::TextRange;
    type Error = ContractFailure;
    type UserContext = ();

    fn will_map_user(&mut self, _user: &rustpython_ast::text_size::TextRange) {}

    fn map_user(
        &mut self,
        user: rustpython_ast::text_size::TextRange,
        _context: (),
    ) -> Result<rustpython_ast::text_size::TextRange, ContractFailure> {
        Ok(user)
    }

    fn fold_expr(&mut self, node: ast::Expr) -> Result<ast::Expr, ContractFailure> {
        if let ast::Expr::Call(call) = &node
            && let ast::Expr::Name(name) = call.func.as_ref()
            && name.id.as_str() == "Low"
            && let Some(value) = self.results.get(&u32::from(call.range.start()))
        {
            return Ok(ast::ExprConstant {
                range: node.range(),
                value: ast::Constant::Bool(*value),
                kind: None,
            }
            .into());
        }
        rustpython_ast::fold::fold_expr(self, node)
    }
}

/// Check the relational termination channel promised by canonical `TerminatesSif` loop
/// invariants. A function is claimed only when every statement affecting a checked loop belongs
/// to this closed label fragment; all other constructs refuse instead of being approximated.
pub(super) fn analyze_termination_channels(
    suite: &[ast::Stmt],
    profile: InformationFlowVerificationProfile,
) -> Result<Option<SifTerminationAnalysis>, ContractFailure> {
    if !profile.is_secure() {
        return Ok(None);
    }
    let canonical = canonical_termination_bindings(suite);
    if !canonical.contains("TerminatesSif")
        || !canonical.contains("Invariant")
        || !canonical.contains("Requires")
    {
        return Ok(None);
    }

    let mut analysis = SifTerminationAnalysis {
        methods: Vec::new(),
        failures: Vec::new(),
    };
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                analyze_termination_function(function, &canonical, &mut analysis)?;
            }
            ast::Stmt::ClassDef(class) => {
                for statement in &class.body {
                    if let ast::Stmt::FunctionDef(function) = statement {
                        analyze_termination_function(function, &canonical, &mut analysis)?;
                    }
                }
            }
            _ => {}
        }
    }
    analyze_termination_call_boundaries(suite, &canonical, &mut analysis)?;
    Ok((!analysis.methods.is_empty() && !analysis.failures.is_empty()).then_some(analysis))
}

#[derive(Clone)]
struct TerminationPrecondition {
    parameters: Vec<String>,
    condition: ast::Expr,
    ranking: ast::Expr,
}

fn analyze_termination_call_boundaries(
    suite: &[ast::Stmt],
    canonical: &BTreeSet<String>,
    analysis: &mut SifTerminationAnalysis,
) -> Result<(), ContractFailure> {
    let summaries = suite
        .iter()
        .filter_map(|statement| match statement {
            ast::Stmt::FunctionDef(function) => termination_precondition(function, canonical)
                .map(|summary| (function.name.to_string(), summary)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    if summaries.is_empty() {
        return Ok(());
    }
    for statement in suite {
        let ast::Stmt::FunctionDef(function) = statement else {
            continue;
        };
        if let Some(summary) = summaries.get(function.name.as_str()) {
            if let Some(failure) = terminating_caller_failure(function, summary, &summaries, suite)?
            {
                if !analysis
                    .methods
                    .iter()
                    .any(|method| method == function.name.as_str())
                {
                    analysis.methods.push(function.name.to_string());
                }
                analysis.failures.push(failure);
            }
            continue;
        }
        let mut state = LabelState::normal(
            function_parameter_names(function).into_iter(),
            BTreeSet::new(),
        );
        let mut ignored_low_results = BTreeMap::new();
        for statement in &function.body {
            if let Some(("Requires", expression)) = direct_contract(statement) {
                assume_low_requirements(expression, &mut state, &mut ignored_low_results)?;
            }
        }
        if let Some(failure) = analyze_termination_calls_in_statements(
            &function.body,
            function.name.as_str(),
            &summaries,
            &mut state,
        )? {
            if !analysis
                .methods
                .iter()
                .any(|method| method == function.name.as_str())
            {
                analysis.methods.push(function.name.to_string());
            }
            analysis.failures.push(failure);
        }
    }
    Ok(())
}

fn termination_precondition(
    function: &ast::StmtFunctionDef,
    canonical: &BTreeSet<String>,
) -> Option<TerminationPrecondition> {
    if !canonical.contains("TerminatesSif") || function_binds_name(function, "TerminatesSif") {
        return None;
    }
    for statement in &function.body {
        let Some(("Requires", expression)) = direct_contract(statement) else {
            continue;
        };
        let ast::Expr::Call(call) = expression else {
            continue;
        };
        if call.args.len() == 2
            && call.keywords.is_empty()
            && matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "TerminatesSif")
        {
            return Some(TerminationPrecondition {
                parameters: function_parameter_names(function),
                condition: call.args[0].clone(),
                ranking: call.args[1].clone(),
            });
        }
    }
    None
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearTerm {
    base: Option<String>,
    offset: i64,
}

fn terminating_caller_failure(
    function: &ast::StmtFunctionDef,
    caller: &TerminationPrecondition,
    summaries: &BTreeMap<String, TerminationPrecondition>,
    suite: &[ast::Stmt],
) -> Result<Option<SifTerminationFailure>, ContractFailure> {
    let mut aliases = caller
        .parameters
        .iter()
        .map(|parameter| {
            (
                parameter.clone(),
                LinearTerm {
                    base: Some(parameter.clone()),
                    offset: 0,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let Some((base, lower_bound)) = termination_lower_bound(&caller.condition, &aliases) else {
        // Constant conditions need no value bound; non-linear conditions remain outside this
        // affine caller-obligation fragment.
        if !expression_is_constant_bool(&caller.condition) {
            return Ok(None);
        }
        return terminating_constant_condition_caller_failure(
            function,
            caller,
            summaries,
            suite,
            &mut aliases,
        );
    };
    let mut excluded = BTreeSet::new();
    scan_terminating_caller_statements(
        &function.body,
        function.name.as_str(),
        caller,
        summaries,
        suite,
        &mut aliases,
        &base,
        lower_bound,
        &mut excluded,
    )
}

fn terminating_constant_condition_caller_failure(
    function: &ast::StmtFunctionDef,
    caller: &TerminationPrecondition,
    summaries: &BTreeMap<String, TerminationPrecondition>,
    suite: &[ast::Stmt],
    aliases: &mut BTreeMap<String, LinearTerm>,
) -> Result<Option<SifTerminationFailure>, ContractFailure> {
    let mut excluded = BTreeSet::new();
    scan_terminating_caller_statements(
        &function.body,
        function.name.as_str(),
        caller,
        summaries,
        suite,
        aliases,
        "",
        i64::MIN / 4,
        &mut excluded,
    )
}

#[allow(clippy::too_many_arguments)]
fn scan_terminating_caller_statements(
    statements: &[ast::Stmt],
    owner: &str,
    caller: &TerminationPrecondition,
    summaries: &BTreeMap<String, TerminationPrecondition>,
    suite: &[ast::Stmt],
    aliases: &mut BTreeMap<String, LinearTerm>,
    base: &str,
    lower_bound: i64,
    excluded: &mut BTreeSet<i64>,
) -> Result<Option<SifTerminationFailure>, ContractFailure> {
    for statement in statements {
        match statement {
            ast::Stmt::Assign(assignment) => {
                if let Some(failure) = terminating_call_obligation_failure(
                    &assignment.value,
                    owner,
                    caller,
                    summaries,
                    suite,
                    aliases,
                    base,
                    lower_bound,
                    excluded,
                )? {
                    return Ok(Some(failure));
                }
                let assigned = if let Some(call) = direct_expression_call(&assignment.value)
                    && call_is_identity(call, suite)
                    && call.args.len() == 1
                {
                    linear_term(&call.args[0], aliases)
                } else {
                    linear_term(&assignment.value, aliases)
                };
                for target in &assignment.targets {
                    let ast::Expr::Name(name) = target else {
                        return unsupported(
                            "termination caller obligations require local-name assignment targets",
                        );
                    };
                    if let Some(term) = &assigned {
                        aliases.insert(name.id.to_string(), term.clone());
                    } else {
                        aliases.remove(name.id.as_str());
                    }
                }
            }
            ast::Stmt::If(branch)
                if branch.orelse.is_empty() && block_always_returns(&branch.body) =>
            {
                if let Some(value) = zero_equality_value(&branch.test, aliases)
                    && value.base.as_deref() == Some(base)
                {
                    excluded.insert(-value.offset);
                }
            }
            ast::Stmt::Expr(expression) => {
                if let Some(failure) = terminating_call_obligation_failure(
                    &expression.value,
                    owner,
                    caller,
                    summaries,
                    suite,
                    aliases,
                    base,
                    lower_bound,
                    excluded,
                )? {
                    return Ok(Some(failure));
                }
            }
            ast::Stmt::Return(return_) => {
                if let Some(value) = return_.value.as_deref()
                    && let Some(failure) = terminating_call_obligation_failure(
                        value,
                        owner,
                        caller,
                        summaries,
                        suite,
                        aliases,
                        base,
                        lower_bound,
                        excluded,
                    )?
                {
                    return Ok(Some(failure));
                }
            }
            ast::Stmt::Pass(_) => {}
            ast::Stmt::If(_) => {
                return unsupported(
                    "termination caller obligations require an early-return affine branch",
                );
            }
            _ if direct_contract(statement).is_some() => {}
            _ => {
                return unsupported(
                    "termination caller obligations encountered an unmodeled statement",
                );
            }
        }
    }
    Ok(None)
}

#[allow(clippy::too_many_arguments)]
fn terminating_call_obligation_failure(
    expression: &ast::Expr,
    owner: &str,
    caller: &TerminationPrecondition,
    summaries: &BTreeMap<String, TerminationPrecondition>,
    suite: &[ast::Stmt],
    aliases: &BTreeMap<String, LinearTerm>,
    base: &str,
    lower_bound: i64,
    excluded: &BTreeSet<i64>,
) -> Result<Option<SifTerminationFailure>, ContractFailure> {
    let Some(call) = direct_expression_call(expression) else {
        return Ok(None);
    };
    let ast::Expr::Name(callee_name) = call.func.as_ref() else {
        return Ok(None);
    };
    let Some(callee) = summaries.get(callee_name.id.as_str()) else {
        return Ok(None);
    };
    if call.args.len() != callee.parameters.len() || !call.keywords.is_empty() {
        return unsupported("termination caller obligations require exact positional binding");
    }
    let bindings = callee
        .parameters
        .iter()
        .zip(&call.args)
        .filter_map(|(formal, actual)| {
            linear_term(actual, aliases).map(|term| (formal.clone(), term))
        })
        .collect::<BTreeMap<_, _>>();
    if bindings.len() != callee.parameters.len() {
        return Ok(None);
    }
    let condition_established = expression_is_constant_true(&callee.condition)
        || termination_condition_established(
            &callee.condition,
            &bindings,
            base,
            lower_bound,
            excluded,
        );
    let recursive_cycle = callee_name.id.as_str() == owner
        || function_directly_calls(suite, callee_name.id.as_str(), owner);
    let rank_decreases = if recursive_cycle {
        let caller_rank = linear_term(&caller.ranking, aliases);
        let callee_rank = linear_term(&callee.ranking, &bindings);
        matches!((caller_rank, callee_rank), (Some(caller), Some(callee))
            if caller.base == callee.base && callee.offset < caller.offset)
    } else {
        true
    };
    Ok(
        (!condition_established || !rank_decreases).then_some(SifTerminationFailure {
            owner: owner.to_owned(),
            kind: SifTerminationFailureKind::CallerUnsatisfied,
            offset: u32::from(call.range.start()),
        }),
    )
}

fn direct_expression_call(expression: &ast::Expr) -> Option<&ast::ExprCall> {
    match expression {
        ast::Expr::Call(call) => Some(call),
        _ => None,
    }
}

fn linear_term(
    expression: &ast::Expr,
    aliases: &BTreeMap<String, LinearTerm>,
) -> Option<LinearTerm> {
    match expression {
        ast::Expr::Name(name) => aliases.get(name.id.as_str()).cloned(),
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Int(value) => Some(LinearTerm {
                base: None,
                offset: value.to_string().parse().ok()?,
            }),
            _ => None,
        },
        ast::Expr::BinOp(binary) => {
            let left = linear_term(&binary.left, aliases)?;
            let right = linear_term(&binary.right, aliases)?;
            match binary.op {
                ast::Operator::Add => combine_linear_terms(left, right, false),
                ast::Operator::Sub => combine_linear_terms(left, right, true),
                _ => None,
            }
        }
        _ => None,
    }
}

fn combine_linear_terms(left: LinearTerm, right: LinearTerm, subtract: bool) -> Option<LinearTerm> {
    if right.base.is_some() {
        return None;
    }
    Some(LinearTerm {
        base: left.base,
        offset: if subtract {
            left.offset.checked_sub(right.offset)?
        } else {
            left.offset.checked_add(right.offset)?
        },
    })
}

fn termination_lower_bound(
    condition: &ast::Expr,
    aliases: &BTreeMap<String, LinearTerm>,
) -> Option<(String, i64)> {
    let ast::Expr::Compare(compare) = condition else {
        return None;
    };
    let [operator] = compare.ops.as_slice() else {
        return None;
    };
    let [right] = compare.comparators.as_slice() else {
        return None;
    };
    let left = linear_term(&compare.left, aliases)?;
    let right = linear_term(right, aliases)?;
    let base = left.base?;
    if right.base.is_some() {
        return None;
    }
    let threshold = right.offset.checked_sub(left.offset)?;
    match operator {
        ast::CmpOp::GtE => Some((base, threshold)),
        ast::CmpOp::Gt => Some((base, threshold.checked_add(1)?)),
        _ => None,
    }
}

fn termination_condition_established(
    condition: &ast::Expr,
    bindings: &BTreeMap<String, LinearTerm>,
    base: &str,
    lower_bound: i64,
    excluded: &BTreeSet<i64>,
) -> bool {
    let Some((condition_base, required)) = termination_lower_bound(condition, bindings) else {
        return false;
    };
    if condition_base != base {
        return false;
    }
    let mut minimum = lower_bound;
    while excluded.contains(&minimum) {
        let Some(next) = minimum.checked_add(1) else {
            return false;
        };
        minimum = next;
    }
    minimum >= required
}

fn expression_is_constant_true(expression: &ast::Expr) -> bool {
    matches!(expression, ast::Expr::Constant(constant) if constant.value == ast::Constant::Bool(true))
}

fn zero_equality_value(
    expression: &ast::Expr,
    aliases: &BTreeMap<String, LinearTerm>,
) -> Option<LinearTerm> {
    let ast::Expr::Compare(compare) = expression else {
        return None;
    };
    let [ast::CmpOp::Eq] = compare.ops.as_slice() else {
        return None;
    };
    let [right] = compare.comparators.as_slice() else {
        return None;
    };
    let right = linear_term(right, aliases)?;
    if right.base.is_some() || right.offset != 0 {
        return None;
    }
    linear_term(&compare.left, aliases)
}

fn block_always_returns(statements: &[ast::Stmt]) -> bool {
    statements
        .last()
        .is_some_and(|statement| matches!(statement, ast::Stmt::Return(_)))
}

fn call_is_identity(call: &ast::ExprCall, suite: &[ast::Stmt]) -> bool {
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return false;
    };
    let canonical = canonical_contract_bindings(suite);
    if !canonical.contains("Ensures") || !canonical.contains("Result") {
        return false;
    }
    suite.iter().any(|statement| {
        let ast::Stmt::FunctionDef(function) = statement else {
            return false;
        };
        let parameters = function_parameter_names(function);
        function.name == name.id
            && parameters.len() == 1
            && !function_binds_name(function, "Ensures")
            && !function_binds_name(function, "Result")
            && function.body.iter().any(|statement| {
                let Some(("Ensures", expression)) = direct_contract(statement) else {
                    return false;
                };
                matches!(expression, ast::Expr::Compare(compare)
                    if compare.ops.as_slice() == [ast::CmpOp::Is]
                        && matches!(compare.left.as_ref(), ast::Expr::Call(result)
                            if result.args.is_empty()
                                && matches!(result.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Result"))
                        && matches!(compare.comparators.as_slice(), [ast::Expr::Name(argument)]
                            if argument.id.as_str() == parameters[0]))
            })
    })
}

fn function_directly_calls(suite: &[ast::Stmt], function_name: &str, target: &str) -> bool {
    let Some(function) = suite.iter().find_map(|statement| match statement {
        ast::Stmt::FunctionDef(function) if function.name.as_str() == function_name => {
            Some(function)
        }
        _ => None,
    }) else {
        return false;
    };
    let mut calls = DirectCallNames::default();
    for statement in function.body.iter().cloned() {
        calls.visit_stmt(statement);
    }
    calls.names.contains(target)
}

#[derive(Default)]
struct DirectCallNames {
    names: BTreeSet<String>,
}

impl Visitor for DirectCallNames {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        if let ast::Expr::Name(name) = node.func.as_ref() {
            self.names.insert(name.id.to_string());
        }
        self.generic_visit_expr_call(node);
    }
}

fn analyze_termination_calls_in_statements(
    statements: &[ast::Stmt],
    owner: &str,
    summaries: &BTreeMap<String, TerminationPrecondition>,
    state: &mut LabelState,
) -> Result<Option<SifTerminationFailure>, ContractFailure> {
    for statement in statements {
        match statement {
            ast::Stmt::Expr(expression) => {
                if direct_contract(statement).is_some() {
                    continue;
                }
                if let Some(failure) =
                    termination_call_failure(&expression.value, owner, summaries, state)?
                {
                    return Ok(Some(failure));
                }
            }
            ast::Stmt::Return(return_) => {
                if let Some(value) = return_.value.as_deref()
                    && let Some(failure) = termination_call_failure(value, owner, summaries, state)?
                {
                    return Ok(Some(failure));
                }
            }
            ast::Stmt::Assign(assignment) => {
                if let Some(failure) =
                    termination_call_failure(&assignment.value, owner, summaries, state)?
                {
                    return Ok(Some(failure));
                }
                let low = channel_expression_is_low(&assignment.value, state)? && state.pc_low;
                for target in &assignment.targets {
                    assign_label(target, low, state)?;
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                if let Some(value) = assignment.value.as_deref() {
                    if let Some(failure) = termination_call_failure(value, owner, summaries, state)?
                    {
                        return Ok(Some(failure));
                    }
                    let low = channel_expression_is_low(value, state)? && state.pc_low;
                    assign_label(&assignment.target, low, state)?;
                }
            }
            ast::Stmt::If(branch) => {
                let guard_low = channel_expression_is_low(&branch.test, state)?;
                let mut when_true = state.clone();
                when_true.pc_low &= guard_low;
                let mut when_false = when_true.clone();
                if let Some(failure) = analyze_termination_calls_in_statements(
                    &branch.body,
                    owner,
                    summaries,
                    &mut when_true,
                )? {
                    return Ok(Some(failure));
                }
                if let Some(failure) = analyze_termination_calls_in_statements(
                    &branch.orelse,
                    owner,
                    summaries,
                    &mut when_false,
                )? {
                    return Ok(Some(failure));
                }
                merge_channel_states(&mut when_true, &when_false);
                *state = when_true;
            }
            ast::Stmt::Import(_) | ast::Stmt::ImportFrom(_) | ast::Stmt::Pass(_) => {}
            ast::Stmt::While(_) | ast::Stmt::For(_) => {
                // Loop-contained call conditions require a relational fixpoint. Leave them to the
                // full verifier rather than deriving a one-iteration result.
                continue;
            }
            _ => {}
        }
    }
    Ok(None)
}

fn termination_call_failure(
    expression: &ast::Expr,
    owner: &str,
    summaries: &BTreeMap<String, TerminationPrecondition>,
    state: &LabelState,
) -> Result<Option<SifTerminationFailure>, ContractFailure> {
    let ast::Expr::Call(call) = expression else {
        return Ok(None);
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return Ok(None);
    };
    let Some(summary) = summaries.get(name.id.as_str()) else {
        return Ok(None);
    };
    if !call.keywords.is_empty() || call.args.len() != summary.parameters.len() {
        return unsupported("termination-conditional calls require exact positional binding");
    }
    let dependencies = expression_names(&summary.condition);
    let mut condition_low = true;
    for dependency in dependencies {
        let Some(index) = summary
            .parameters
            .iter()
            .position(|parameter| parameter == &dependency)
        else {
            continue;
        };
        condition_low &= channel_expression_is_low(&call.args[index], state)?;
    }
    Ok((!condition_low).then_some(SifTerminationFailure {
        owner: owner.to_owned(),
        kind: SifTerminationFailureKind::CallConditionNotLow,
        offset: u32::from(call.range.start()),
    }))
}

fn canonical_termination_bindings(suite: &[ast::Stmt]) -> BTreeSet<String> {
    let mut canonical = BTreeSet::new();
    for statement in suite {
        match statement {
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import
                        .module
                        .as_ref()
                        .is_some_and(|module| module.as_str() == "nagini_contracts.contracts") =>
            {
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        canonical.extend(TERMINATION_CONTRACT_NAMES.into_iter().map(str::to_owned));
                        canonical.insert("Declassify".to_owned());
                        continue;
                    }
                    let bound = alias
                        .asname
                        .as_ref()
                        .map_or(alias.name.as_str(), |name| name.as_str());
                    canonical.remove(bound);
                    if bound == alias.name.as_str()
                        && (TERMINATION_CONTRACT_NAMES.contains(&bound) || bound == "Declassify")
                    {
                        canonical.insert(bound.to_owned());
                    }
                }
            }
            other => {
                for name in canonical.clone() {
                    if statement_binds_name_recursive(other, &name) {
                        canonical.remove(&name);
                    }
                }
            }
        }
    }
    canonical
}

fn analyze_termination_function(
    function: &ast::StmtFunctionDef,
    canonical: &BTreeSet<String>,
    analysis: &mut SifTerminationAnalysis,
) -> Result<(), ContractFailure> {
    if !function_contains_termination_loop(&function.body, canonical) {
        return Ok(());
    }
    for name in TERMINATION_CONTRACT_NAMES.into_iter().chain(["Declassify"]) {
        if canonical.contains(name) && function_binds_name(function, name) {
            return unsupported(format!(
                "lexically shadowed {name} cannot participate in SIF termination analysis"
            ));
        }
    }

    let owner = function.name.to_string();
    analysis.methods.push(owner.clone());
    let mut state = LabelState::normal(
        function_parameter_names(function).into_iter(),
        BTreeSet::new(),
    );
    let mut low_event = false;
    let mut ignored_low_results = BTreeMap::new();
    for statement in &function.body {
        if let Some(("Requires", expression)) = direct_contract(statement) {
            if canonical.contains("Low") {
                assume_low_requirements(expression, &mut state, &mut ignored_low_results)?;
            }
            if canonical.contains("LowEvent") && positive_low_event(expression) {
                low_event = true;
            }
        }
    }
    analyze_termination_statements(
        &function.body,
        &owner,
        canonical,
        low_event,
        &mut state,
        &mut analysis.failures,
        false,
    )?;
    Ok(())
}

fn function_contains_termination_loop(
    statements: &[ast::Stmt],
    canonical: &BTreeSet<String>,
) -> bool {
    statements.iter().any(|statement| match statement {
        ast::Stmt::While(loop_) => {
            loop_
                .body
                .iter()
                .any(|item| termination_contract(item, canonical).is_some())
                || function_contains_termination_loop(&loop_.body, canonical)
                || function_contains_termination_loop(&loop_.orelse, canonical)
        }
        ast::Stmt::If(branch) => {
            function_contains_termination_loop(&branch.body, canonical)
                || function_contains_termination_loop(&branch.orelse, canonical)
        }
        _ => false,
    })
}

fn positive_low_event(expression: &ast::Expr) -> bool {
    match expression {
        ast::Expr::Call(call) => {
            call.args.is_empty()
                && call.keywords.is_empty()
                && matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "LowEvent")
        }
        ast::Expr::BoolOp(boolean) if boolean.op == ast::BoolOp::And => {
            boolean.values.iter().any(positive_low_event)
        }
        _ => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn analyze_termination_statements(
    statements: &[ast::Stmt],
    owner: &str,
    canonical: &BTreeSet<String>,
    low_event: bool,
    state: &mut LabelState,
    failures: &mut Vec<SifTerminationFailure>,
    already_failed: bool,
) -> Result<bool, ContractFailure> {
    let mut failed = already_failed;
    for statement in statements {
        match statement {
            ast::Stmt::Import(_) | ast::Stmt::ImportFrom(_) | ast::Stmt::Pass(_) => {}
            ast::Stmt::Expr(expression) => {
                if direct_contract(statement).is_some() {
                    continue;
                }
                if let ast::Expr::Call(call) = expression.value.as_ref()
                    && canonical.contains("Declassify")
                    && matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Declassify")
                    && call.args.len() == 1
                    && call.keywords.is_empty()
                {
                    assume_expression_and_complement_low(&call.args[0], state)?;
                }
            }
            ast::Stmt::Assign(assignment) => {
                let low = channel_expression_is_low(&assignment.value, state)? && state.pc_low;
                let symbolic = channel_symbolic_term(&assignment.value, state);
                for target in &assignment.targets {
                    assign_label(target, low, state)?;
                    assign_channel_symbolic_term(target, symbolic.as_deref(), state);
                }
            }
            ast::Stmt::AnnAssign(assignment) => {
                if let Some(value) = assignment.value.as_deref() {
                    let low = channel_expression_is_low(value, state)? && state.pc_low;
                    let symbolic = channel_symbolic_term(value, state);
                    assign_label(&assignment.target, low, state)?;
                    assign_channel_symbolic_term(&assignment.target, symbolic.as_deref(), state);
                }
            }
            ast::Stmt::AugAssign(assignment) => {
                let low = channel_expression_is_low(&assignment.target, state)?
                    && channel_expression_is_low(&assignment.value, state)?
                    && state.pc_low;
                let symbolic = Some(format!(
                    "binary:{:?}:{}:{}",
                    assignment.op,
                    channel_symbolic_term(&assignment.target, state)
                        .unwrap_or_else(|| "unknown".to_owned()),
                    channel_symbolic_term(&assignment.value, state)
                        .unwrap_or_else(|| "unknown".to_owned())
                ));
                assign_label(&assignment.target, low, state)?;
                assign_channel_symbolic_term(&assignment.target, symbolic.as_deref(), state);
            }
            ast::Stmt::While(loop_) => {
                if !failed
                    && let Some((condition, ranking, offset)) = loop_
                        .body
                        .iter()
                        .find_map(|item| termination_contract(item, canonical))
                {
                    let condition_low = channel_expression_is_low(condition, state)?;
                    let kind = if !condition_low {
                        Some(SifTerminationFailureKind::ConditionNotLow)
                    } else if !low_event && !expression_is_constant_bool(condition) {
                        Some(SifTerminationFailureKind::NotLowEvent)
                    } else if termination_condition_has_tightness_counterexample(
                        loop_, condition, state,
                    ) {
                        Some(SifTerminationFailureKind::ConditionNotTight)
                    } else if termination_loop_has_non_decreasing_back_edge(loop_, ranking)? {
                        Some(SifTerminationFailureKind::LoopPromiseNotKept)
                    } else {
                        None
                    };
                    if let Some(kind) = kind {
                        let offset = if kind == SifTerminationFailureKind::LoopPromiseNotKept {
                            u32::from(loop_.range.start())
                        } else {
                            offset
                        };
                        failures.push(SifTerminationFailure {
                            owner: owner.to_owned(),
                            kind,
                            offset,
                        });
                        failed = true;
                    }
                }
                let guard_low = channel_expression_is_low(&loop_.test, state)?;
                let mut body_state = state.clone();
                body_state.pc_low &= guard_low;
                failed = analyze_termination_statements(
                    &loop_.body,
                    owner,
                    canonical,
                    low_event,
                    &mut body_state,
                    failures,
                    failed,
                )?;
                merge_channel_states(state, &body_state);
                failed = analyze_termination_statements(
                    &loop_.orelse,
                    owner,
                    canonical,
                    low_event,
                    state,
                    failures,
                    failed,
                )?;
            }
            ast::Stmt::If(branch) => {
                let guard_low = channel_expression_is_low(&branch.test, state)?;
                let mut when_true = state.clone();
                when_true.pc_low &= guard_low;
                let mut when_false = when_true.clone();
                failed = analyze_termination_statements(
                    &branch.body,
                    owner,
                    canonical,
                    low_event,
                    &mut when_true,
                    failures,
                    failed,
                )?;
                failed = analyze_termination_statements(
                    &branch.orelse,
                    owner,
                    canonical,
                    low_event,
                    &mut when_false,
                    failures,
                    failed,
                )?;
                merge_channel_states(&mut when_true, &when_false);
                when_true.pc_low = state.pc_low;
                *state = when_true;
            }
            ast::Stmt::Return(_) | ast::Stmt::Continue(_) | ast::Stmt::Break(_) => {}
            other => {
                return unsupported(format!(
                    "statement {:?} is outside the closed SIF termination-channel analysis",
                    statement_name(other)
                ));
            }
        }
    }
    Ok(failed)
}

fn termination_contract<'a>(
    statement: &'a ast::Stmt,
    canonical: &BTreeSet<String>,
) -> Option<(&'a ast::Expr, &'a ast::Expr, u32)> {
    let ("Invariant", expression) = direct_contract(statement)? else {
        return None;
    };
    if !canonical.contains("Invariant") || !canonical.contains("TerminatesSif") {
        return None;
    }
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    if call.args.len() != 2
        || !call.keywords.is_empty()
        || !matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "TerminatesSif")
    {
        return None;
    }
    Some((
        &call.args[0],
        &call.args[1],
        u32::from(statement.range().start()),
    ))
}

fn channel_expression_is_low(
    expression: &ast::Expr,
    state: &LabelState,
) -> Result<bool, ContractFailure> {
    match expression_is_low(expression, state) {
        Ok(low) => Ok(low),
        Err(failure)
            if failure.code == LOW_UNSUPPORTED && matches!(expression, ast::Expr::Call(_)) =>
        {
            Ok(false)
        }
        Err(failure) => Err(failure),
    }
}

fn expression_is_constant_bool(expression: &ast::Expr) -> bool {
    matches!(expression, ast::Expr::Constant(constant) if matches!(constant.value, ast::Constant::Bool(_)))
}

fn channel_symbolic_term(expression: &ast::Expr, state: &LabelState) -> Option<String> {
    match expression {
        ast::Expr::Constant(constant) => Some(format!("constant:{:?}", constant.value)),
        ast::Expr::Name(name) => state.symbolic_terms.get(name.id.as_str()).cloned(),
        ast::Expr::UnaryOp(unary) => Some(format!(
            "unary:{:?}:{}",
            unary.op,
            channel_symbolic_term(&unary.operand, state)?
        )),
        ast::Expr::BinOp(binary) => Some(format!(
            "binary:{:?}:{}:{}",
            binary.op,
            channel_symbolic_term(&binary.left, state)?,
            channel_symbolic_term(&binary.right, state)?
        )),
        ast::Expr::Compare(compare) => {
            let mut term = format!("compare:{}", channel_symbolic_term(&compare.left, state)?);
            for (operator, value) in compare.ops.iter().zip(&compare.comparators) {
                term.push_str(&format!(
                    ":{operator:?}:{}",
                    channel_symbolic_term(value, state)?
                ));
            }
            Some(term)
        }
        _ => None,
    }
}

fn assign_channel_symbolic_term(target: &ast::Expr, term: Option<&str>, state: &mut LabelState) {
    match target {
        ast::Expr::Name(name) => {
            if let Some(term) = term {
                state
                    .symbolic_terms
                    .insert(name.id.to_string(), term.to_owned());
            } else {
                state.symbolic_terms.remove(name.id.as_str());
            }
        }
        ast::Expr::Tuple(tuple) => {
            for item in &tuple.elts {
                assign_channel_symbolic_term(item, None, state);
            }
        }
        ast::Expr::List(list) => {
            for item in &list.elts {
                assign_channel_symbolic_term(item, None, state);
            }
        }
        _ => {}
    }
}

/// Exhibit the concrete zero-input counterexample for the supported unit-decrement loop shape:
/// `x = h; while x != 0: x -= 1` terminates at `h == 0`, so `h > 0` is not a tight termination
/// condition. Returning false outside this exact proof fragment makes no tightness claim.
fn termination_condition_has_tightness_counterexample(
    loop_: &ast::StmtWhile,
    condition: &ast::Expr,
    state: &LabelState,
) -> bool {
    let ast::Expr::Compare(condition) = condition else {
        return false;
    };
    let (ast::Expr::Name(condition_name), [ast::CmpOp::Gt], [ast::Expr::Constant(zero)]) = (
        condition.left.as_ref(),
        condition.ops.as_slice(),
        condition.comparators.as_slice(),
    ) else {
        return false;
    };
    if zero.value != ast::Constant::Int(0.into()) {
        return false;
    }
    let ast::Expr::Compare(guard) = loop_.test.as_ref() else {
        return false;
    };
    let (ast::Expr::Name(loop_name), [ast::CmpOp::NotEq], [ast::Expr::Constant(loop_zero)]) = (
        guard.left.as_ref(),
        guard.ops.as_slice(),
        guard.comparators.as_slice(),
    ) else {
        return false;
    };
    if loop_zero.value != ast::Constant::Int(0.into())
        || state.symbolic_terms.get(loop_name.id.as_str())
            != state.symbolic_terms.get(condition_name.id.as_str())
    {
        return false;
    }
    loop_.body.iter().any(|statement| {
        matches!(statement,
            ast::Stmt::AugAssign(assignment)
                if assignment.op == ast::Operator::Sub
                    && matches!(assignment.target.as_ref(), ast::Expr::Name(name) if name.id == loop_name.id)
                    && matches!(assignment.value.as_ref(), ast::Expr::Constant(one) if one.value == ast::Constant::Int(1.into())))
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LoopBackFlow {
    Normal,
    Continue,
    Exit,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LoopBackState {
    decreased: bool,
    flow: LoopBackFlow,
}

fn termination_loop_has_non_decreasing_back_edge(
    loop_: &ast::StmtWhile,
    ranking: &ast::Expr,
) -> Result<bool, ContractFailure> {
    let ast::Expr::Name(ranking) = ranking else {
        return Ok(false);
    };
    let paths = analyze_loop_back_paths(
        &loop_.body,
        vec![LoopBackState {
            decreased: false,
            flow: LoopBackFlow::Normal,
        }],
        ranking.id.as_str(),
    )?;
    Ok(paths.iter().any(|path| {
        matches!(path.flow, LoopBackFlow::Normal | LoopBackFlow::Continue) && !path.decreased
    }))
}

fn analyze_loop_back_paths(
    statements: &[ast::Stmt],
    mut paths: Vec<LoopBackState>,
    ranking: &str,
) -> Result<Vec<LoopBackState>, ContractFailure> {
    for statement in statements {
        let mut next = Vec::new();
        for mut path in paths {
            if path.flow != LoopBackFlow::Normal {
                next.push(path);
                continue;
            }
            match statement {
                ast::Stmt::Expr(_) | ast::Stmt::Pass(_) => next.push(path),
                ast::Stmt::AugAssign(assignment)
                    if assignment.op == ast::Operator::Sub
                        && matches!(assignment.target.as_ref(), ast::Expr::Name(name) if name.id.as_str() == ranking)
                        && positive_int_constant(&assignment.value) =>
                {
                    path.decreased = true;
                    next.push(path);
                }
                ast::Stmt::Assign(assignment)
                    if assignment.targets.iter().any(
                        |target| matches!(target, ast::Expr::Name(name) if name.id.as_str() == ranking),
                    ) =>
                {
                    return unsupported(
                        "termination ranking reassignment requires a proved strict-decrease relation",
                    );
                }
                ast::Stmt::AnnAssign(assignment)
                    if matches!(assignment.target.as_ref(), ast::Expr::Name(name) if name.id.as_str() == ranking) =>
                {
                    return unsupported(
                        "termination ranking reassignment requires a proved strict-decrease relation",
                    );
                }
                ast::Stmt::Continue(_) => {
                    path.flow = LoopBackFlow::Continue;
                    next.push(path);
                }
                ast::Stmt::Break(_) | ast::Stmt::Return(_) | ast::Stmt::Raise(_) => {
                    path.flow = LoopBackFlow::Exit;
                    next.push(path);
                }
                ast::Stmt::If(branch) => {
                    let (take_true, take_false) = match eval_static_bool(&branch.test) {
                        Some(true) => (true, false),
                        Some(false) => (false, true),
                        None => (true, true),
                    };
                    if take_true {
                        next.extend(analyze_loop_back_paths(
                            &branch.body,
                            vec![path],
                            ranking,
                        )?);
                    }
                    if take_false {
                        next.extend(analyze_loop_back_paths(
                            &branch.orelse,
                            vec![path],
                            ranking,
                        )?);
                    }
                }
                ast::Stmt::Assign(_)
                | ast::Stmt::AnnAssign(_)
                | ast::Stmt::AugAssign(_) => next.push(path),
                _ => {
                    return unsupported(
                        "loop promise paths require assignments, calls, conditionals, or explicit exits",
                    );
                }
            }
        }
        paths = next;
    }
    Ok(paths)
}

fn positive_int_constant(expression: &ast::Expr) -> bool {
    matches!(expression, ast::Expr::Constant(constant)
        if matches!(&constant.value, ast::Constant::Int(value)
            if value.to_string().parse::<i64>().is_ok_and(|value| value > 0)))
}

fn eval_static_bool(expression: &ast::Expr) -> Option<bool> {
    match expression {
        ast::Expr::Constant(constant) => match constant.value {
            ast::Constant::Bool(value) => Some(value),
            _ => None,
        },
        ast::Expr::Compare(compare) => {
            let [operator] = compare.ops.as_slice() else {
                return None;
            };
            let [right] = compare.comparators.as_slice() else {
                return None;
            };
            let left = eval_static_int(&compare.left)?;
            let right = eval_static_int(right)?;
            Some(match operator {
                ast::CmpOp::Eq => left == right,
                ast::CmpOp::NotEq => left != right,
                ast::CmpOp::Lt => left < right,
                ast::CmpOp::LtE => left <= right,
                ast::CmpOp::Gt => left > right,
                ast::CmpOp::GtE => left >= right,
                _ => return None,
            })
        }
        _ => None,
    }
}

fn eval_static_int(expression: &ast::Expr) -> Option<i64> {
    match expression {
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Int(value) => value.to_string().parse().ok(),
            _ => None,
        },
        ast::Expr::BinOp(binary) => {
            let left = eval_static_int(&binary.left)?;
            let right = eval_static_int(&binary.right)?;
            match binary.op {
                ast::Operator::Add => left.checked_add(right),
                ast::Operator::Sub => left.checked_sub(right),
                ast::Operator::Mult => left.checked_mul(right),
                _ => None,
            }
        }
        _ => None,
    }
}

fn assume_expression_and_complement_low(
    expression: &ast::Expr,
    state: &mut LabelState,
) -> Result<(), ContractFailure> {
    assume_expression_low(expression, state)?;
    let ast::Expr::Compare(compare) = expression else {
        return Ok(());
    };
    let [operator] = compare.ops.as_slice() else {
        return Ok(());
    };
    let [right] = compare.comparators.as_slice() else {
        return Ok(());
    };
    let complement = match operator {
        ast::CmpOp::Eq => ast::CmpOp::NotEq,
        ast::CmpOp::NotEq => ast::CmpOp::Eq,
        ast::CmpOp::Lt => ast::CmpOp::GtE,
        ast::CmpOp::LtE => ast::CmpOp::Gt,
        ast::CmpOp::Gt => ast::CmpOp::LtE,
        ast::CmpOp::GtE => ast::CmpOp::Lt,
        _ => return Ok(()),
    };
    let complement: ast::Expr = ast::ExprCompare {
        range: compare.range,
        left: compare.left.clone(),
        ops: vec![complement],
        comparators: vec![right.clone()],
    }
    .into();
    let key = expression_key(&complement)?;
    state.exact_low_facts.insert(key.clone());
    state
        .exact_low_fact_dependencies
        .insert(key, expression_names(&complement));
    Ok(())
}

fn merge_channel_states(target: &mut LabelState, other: &LabelState) {
    for (name, low) in target.locals.clone() {
        target.locals.insert(
            name.clone(),
            low && other.locals.get(&name).copied().unwrap_or(false),
        );
    }
    target
        .exact_low_facts
        .retain(|fact| other.exact_low_facts.contains(fact));
    target
        .exact_low_fact_dependencies
        .retain(|fact, _| target.exact_low_facts.contains(fact));
    target
        .symbolic_terms
        .retain(|name, term| other.symbolic_terms.get(name) == Some(term));
    target.pc_low &= other.pc_low;
}

struct SourceFunctionCandidate<'a> {
    function: &'a ast::StmtFunctionDef,
    parameters: Vec<String>,
    dependencies: BTreeSet<String>,
}

/// Build summaries monotonically.  The first fixed point removes any function whose executable
/// body has an unsupported or exceptional edge, including transitive callees.  The result pass
/// then iterates dependencies to a fixed point. A recursive call cycle is not itself a totality
/// proof, so cycles without a separately modeled well-founded ranking are removed before that
/// pass rather than being accepted from a circular postcondition.
fn source_call_summaries(
    suite: &[ast::Stmt],
    canonical_names: &BTreeSet<String>,
) -> BTreeMap<String, SourceCallSummary> {
    let mut counts = BTreeMap::<String, usize>::new();
    for statement in suite {
        if let ast::Stmt::FunctionDef(function) = statement {
            *counts.entry(function.name.to_string()).or_default() += 1;
        }
    }
    let mut functions = BTreeMap::<String, &ast::StmtFunctionDef>::new();
    for statement in suite {
        let ast::Stmt::FunctionDef(function) = statement else {
            continue;
        };
        let name = function.name.to_string();
        if counts.get(&name) != Some(&1)
            || suite.iter().any(|other| {
                !matches!(other, ast::Stmt::FunctionDef(item) if item.name == function.name)
                    && statement_binds_name_recursive(other, &name)
            })
        {
            continue;
        }
        functions.insert(name, function);
    }
    let signatures = functions
        .iter()
        .filter_map(|(name, function)| {
            source_summary_parameters(function).map(|parameters| (name.clone(), parameters))
        })
        .collect::<BTreeMap<_, _>>();

    let mut candidates = BTreeMap::<String, SourceFunctionCandidate<'_>>::new();
    for (name, function) in &functions {
        let Some(parameters) = signatures.get(name).cloned() else {
            continue;
        };
        let shadowed = signatures
            .keys()
            .filter(|callee| function_binds_name(function, callee))
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut dependencies = BTreeSet::new();
        if source_summary_statements_are_normal(
            &function.body,
            function,
            canonical_names,
            &signatures,
            &shadowed,
            &mut dependencies,
        ) {
            candidates.insert(
                name.clone(),
                SourceFunctionCandidate {
                    function,
                    parameters,
                    dependencies,
                },
            );
        }
    }
    loop {
        let names = candidates.keys().cloned().collect::<BTreeSet<_>>();
        let removed = candidates
            .iter()
            .filter_map(|(name, candidate)| {
                (!candidate
                    .dependencies
                    .iter()
                    .all(|dependency| names.contains(dependency)))
                .then_some(name.clone())
            })
            .collect::<Vec<_>>();
        if removed.is_empty() {
            break;
        }
        for name in removed {
            candidates.remove(&name);
        }
    }
    let recursive = candidates
        .keys()
        .filter(|name| source_candidate_reaches(name, name, &candidates, &mut BTreeSet::new()))
        .cloned()
        .collect::<Vec<_>>();
    for name in recursive {
        candidates.remove(&name);
    }
    loop {
        let names = candidates.keys().cloned().collect::<BTreeSet<_>>();
        let removed = candidates
            .iter()
            .filter_map(|(name, candidate)| {
                (!candidate
                    .dependencies
                    .iter()
                    .all(|dependency| names.contains(dependency)))
                .then_some(name.clone())
            })
            .collect::<Vec<_>>();
        if removed.is_empty() {
            break;
        }
        for name in removed {
            candidates.remove(&name);
        }
    }

    let mut summaries = BTreeMap::new();
    loop {
        let mut changed = false;
        for (name, candidate) in &candidates {
            if summaries.contains_key(name) {
                continue;
            }
            let parameters = candidate
                .parameters
                .iter()
                .enumerate()
                .map(|(index, parameter)| {
                    (parameter.clone(), SourceSummaryExpression::Parameter(index))
                })
                .collect::<BTreeMap<_, _>>();
            let result = source_value_postcondition(candidate.function, canonical_names)
                .and_then(|expression| {
                    source_summary_expression(expression, &parameters, &summaries)
                })
                .or_else(|| {
                    source_summary_block_result(
                        &candidate.function.body.iter().collect::<Vec<_>>(),
                        parameters,
                        candidate.function,
                        canonical_names,
                        &summaries,
                    )
                });
            if let Some(result) = result {
                summaries.insert(
                    name.clone(),
                    SourceCallSummary {
                        parameters: candidate.parameters.clone(),
                        result,
                    },
                );
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    summaries
}

fn source_candidate_reaches(
    current: &str,
    target: &str,
    candidates: &BTreeMap<String, SourceFunctionCandidate<'_>>,
    visited: &mut BTreeSet<String>,
) -> bool {
    let Some(candidate) = candidates.get(current) else {
        return false;
    };
    for dependency in &candidate.dependencies {
        if dependency == target {
            return true;
        }
        if visited.insert(dependency.clone())
            && source_candidate_reaches(dependency, target, candidates, visited)
        {
            return true;
        }
    }
    false
}

fn source_summary_parameters(function: &ast::StmtFunctionDef) -> Option<Vec<String>> {
    if function.args.vararg.is_some()
        || function.args.kwarg.is_some()
        || !function.args.kwonlyargs.is_empty()
        || function
            .args
            .posonlyargs
            .iter()
            .chain(function.args.args.iter())
            .any(|argument| argument.default.is_some())
    {
        return None;
    }
    Some(
        function
            .args
            .posonlyargs
            .iter()
            .chain(function.args.args.iter())
            .map(|argument| argument.def.arg.to_string())
            .collect(),
    )
}

fn source_summary_statements_are_normal(
    statements: &[ast::Stmt],
    owner: &ast::StmtFunctionDef,
    canonical_names: &BTreeSet<String>,
    signatures: &BTreeMap<String, Vec<String>>,
    shadowed: &BTreeSet<String>,
    dependencies: &mut BTreeSet<String>,
) -> bool {
    statements.iter().all(|statement| match statement {
        ast::Stmt::Pass(_) => true,
        ast::Stmt::Expr(expression) => {
            matches!(expression.value.as_ref(), ast::Expr::Constant(_))
                || source_summary_contract_statement(statement, owner, canonical_names)
        }
        ast::Stmt::Assign(assignment) => {
            assignment.targets.iter().all(source_summary_local_target)
                && source_summary_expression_is_normal(
                    &assignment.value,
                    signatures,
                    shadowed,
                    dependencies,
                )
        }
        ast::Stmt::AnnAssign(assignment) => {
            source_summary_local_target(&assignment.target)
                && assignment.value.as_deref().is_none_or(|value| {
                    source_summary_expression_is_normal(value, signatures, shadowed, dependencies)
                })
        }
        ast::Stmt::If(branch) => {
            source_summary_expression_is_normal(&branch.test, signatures, shadowed, dependencies)
                && source_summary_statements_are_normal(
                    &branch.body,
                    owner,
                    canonical_names,
                    signatures,
                    shadowed,
                    dependencies,
                )
                && source_summary_statements_are_normal(
                    &branch.orelse,
                    owner,
                    canonical_names,
                    signatures,
                    shadowed,
                    dependencies,
                )
        }
        ast::Stmt::Return(return_) => return_.value.as_deref().is_none_or(|value| {
            source_summary_expression_is_normal(value, signatures, shadowed, dependencies)
        }),
        // Writes through references, handlers, explicit raises, loops, and every other statement
        // have effects that this summary does not model. They are intentionally not accepted.
        _ => false,
    })
}

fn source_summary_local_target(target: &ast::Expr) -> bool {
    match target {
        ast::Expr::Name(_) => true,
        ast::Expr::Tuple(tuple) => tuple.elts.iter().all(source_summary_local_target),
        ast::Expr::List(list) => list.elts.iter().all(source_summary_local_target),
        _ => false,
    }
}

fn source_summary_expression_is_normal(
    expression: &ast::Expr,
    signatures: &BTreeMap<String, Vec<String>>,
    shadowed: &BTreeSet<String>,
    dependencies: &mut BTreeSet<String>,
) -> bool {
    match expression {
        ast::Expr::Constant(_) | ast::Expr::Name(_) => true,
        ast::Expr::Attribute(attribute) => source_summary_expression_is_normal(
            &attribute.value,
            signatures,
            shadowed,
            dependencies,
        ),
        ast::Expr::UnaryOp(unary) => {
            source_summary_expression_is_normal(&unary.operand, signatures, shadowed, dependencies)
        }
        ast::Expr::BinOp(binary)
            if matches!(
                binary.op,
                ast::Operator::Add | ast::Operator::Sub | ast::Operator::Mult
            ) =>
        {
            source_summary_expression_is_normal(&binary.left, signatures, shadowed, dependencies)
                && source_summary_expression_is_normal(
                    &binary.right,
                    signatures,
                    shadowed,
                    dependencies,
                )
        }
        ast::Expr::BoolOp(boolean) => boolean.values.iter().all(|value| {
            source_summary_expression_is_normal(value, signatures, shadowed, dependencies)
        }),
        ast::Expr::Compare(compare) => {
            source_summary_expression_is_normal(&compare.left, signatures, shadowed, dependencies)
                && compare.comparators.iter().all(|value| {
                    source_summary_expression_is_normal(value, signatures, shadowed, dependencies)
                })
        }
        ast::Expr::IfExp(conditional) => {
            source_summary_expression_is_normal(
                &conditional.test,
                signatures,
                shadowed,
                dependencies,
            ) && source_summary_expression_is_normal(
                &conditional.body,
                signatures,
                shadowed,
                dependencies,
            ) && source_summary_expression_is_normal(
                &conditional.orelse,
                signatures,
                shadowed,
                dependencies,
            )
        }
        ast::Expr::Tuple(tuple) => tuple.elts.iter().all(|value| {
            source_summary_expression_is_normal(value, signatures, shadowed, dependencies)
        }),
        ast::Expr::List(list) => list.elts.iter().all(|value| {
            source_summary_expression_is_normal(value, signatures, shadowed, dependencies)
        }),
        ast::Expr::Set(set) => set.elts.iter().all(|value| {
            source_summary_expression_is_normal(value, signatures, shadowed, dependencies)
        }),
        ast::Expr::Dict(dict) if dict.keys.iter().all(Option::is_some) => {
            dict.keys.iter().flatten().all(|value| {
                source_summary_expression_is_normal(value, signatures, shadowed, dependencies)
            }) && dict.values.iter().all(|value| {
                source_summary_expression_is_normal(value, signatures, shadowed, dependencies)
            })
        }
        ast::Expr::Call(call) if call.keywords.is_empty() => {
            let ast::Expr::Name(name) = call.func.as_ref() else {
                return false;
            };
            let callee = name.id.as_str();
            let Some(parameters) = signatures.get(callee) else {
                return false;
            };
            if shadowed.contains(callee) || call.args.len() != parameters.len() {
                return false;
            }
            dependencies.insert(callee.to_owned());
            call.args.iter().all(|argument| {
                source_summary_expression_is_normal(argument, signatures, shadowed, dependencies)
            })
        }
        _ => false,
    }
}

fn source_summary_contract_statement(
    statement: &ast::Stmt,
    owner: &ast::StmtFunctionDef,
    canonical_names: &BTreeSet<String>,
) -> bool {
    let ast::Stmt::Expr(expression) = statement else {
        return false;
    };
    let ast::Expr::Call(call) = expression.value.as_ref() else {
        return false;
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return false;
    };
    CONTRACT_NAMES.contains(&name.id.as_str())
        && canonical_names.contains(name.id.as_str())
        && !function_binds_name(owner, name.id.as_str())
}

fn source_value_postcondition<'a>(
    function: &'a ast::StmtFunctionDef,
    canonical_names: &BTreeSet<String>,
) -> Option<&'a ast::Expr> {
    if !canonical_names.contains("Ensures")
        || !canonical_names.contains("Result")
        || function_binds_name(function, "Ensures")
        || function_binds_name(function, "Result")
    {
        return None;
    }
    function.body.iter().find_map(|statement| {
        let Some(("Ensures", expression)) = direct_contract(statement) else {
            return None;
        };
        source_result_equality(expression)
    })
}

fn source_result_equality(expression: &ast::Expr) -> Option<&ast::Expr> {
    if let ast::Expr::BoolOp(boolean) = expression
        && boolean.op == ast::BoolOp::And
    {
        return boolean.values.iter().find_map(source_result_equality);
    }
    let ast::Expr::Compare(compare) = expression else {
        return None;
    };
    let [operator] = compare.ops.as_slice() else {
        return None;
    };
    if !matches!(operator, ast::CmpOp::Eq | ast::CmpOp::Is) {
        return None;
    }
    let [right] = compare.comparators.as_slice() else {
        return None;
    };
    if canonical_result_call(&compare.left) {
        Some(right)
    } else if canonical_result_call(right) {
        Some(&compare.left)
    } else {
        None
    }
}

fn canonical_result_call(expression: &ast::Expr) -> bool {
    matches!(expression, ast::Expr::Call(call)
        if call.args.is_empty()
            && call.keywords.is_empty()
            && matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Result"))
}

fn source_summary_block_result(
    statements: &[&ast::Stmt],
    mut environment: BTreeMap<String, SourceSummaryExpression>,
    owner: &ast::StmtFunctionDef,
    canonical_names: &BTreeSet<String>,
    summaries: &BTreeMap<String, SourceCallSummary>,
) -> Option<SourceSummaryExpression> {
    let Some((statement, rest)) = statements.split_first() else {
        return Some(SourceSummaryExpression::Constant("None".to_owned()));
    };
    match statement {
        ast::Stmt::Pass(_) => {
            source_summary_block_result(rest, environment, owner, canonical_names, summaries)
        }
        ast::Stmt::Expr(expression)
            if matches!(expression.value.as_ref(), ast::Expr::Constant(_))
                || source_summary_contract_statement(statement, owner, canonical_names) =>
        {
            source_summary_block_result(rest, environment, owner, canonical_names, summaries)
        }
        ast::Stmt::Assign(assignment) => {
            let value = source_summary_expression(&assignment.value, &environment, summaries)?;
            for target in &assignment.targets {
                source_summary_bind_target(target, &value, &mut environment)?;
            }
            source_summary_block_result(rest, environment, owner, canonical_names, summaries)
        }
        ast::Stmt::AnnAssign(assignment) => {
            let Some(value) = assignment.value.as_deref() else {
                return source_summary_block_result(
                    rest,
                    environment,
                    owner,
                    canonical_names,
                    summaries,
                );
            };
            let value = source_summary_expression(value, &environment, summaries)?;
            source_summary_bind_target(&assignment.target, &value, &mut environment)?;
            source_summary_block_result(rest, environment, owner, canonical_names, summaries)
        }
        ast::Stmt::If(branch) => {
            let guard = source_summary_expression(&branch.test, &environment, summaries)?;
            let mut when_true = branch.body.iter().collect::<Vec<_>>();
            when_true.extend_from_slice(rest);
            let mut when_false = branch.orelse.iter().collect::<Vec<_>>();
            when_false.extend_from_slice(rest);
            let true_result = source_summary_block_result(
                &when_true,
                environment.clone(),
                owner,
                canonical_names,
                summaries,
            )?;
            let false_result = source_summary_block_result(
                &when_false,
                environment,
                owner,
                canonical_names,
                summaries,
            )?;
            if true_result == false_result {
                Some(true_result)
            } else {
                Some(SourceSummaryExpression::Conditional(
                    Box::new(guard),
                    Box::new(true_result),
                    Box::new(false_result),
                ))
            }
        }
        ast::Stmt::Return(return_) => return_.value.as_deref().map_or_else(
            || Some(SourceSummaryExpression::Constant("None".to_owned())),
            |value| source_summary_expression(value, &environment, summaries),
        ),
        _ => None,
    }
}

fn source_summary_bind_target(
    target: &ast::Expr,
    value: &SourceSummaryExpression,
    environment: &mut BTreeMap<String, SourceSummaryExpression>,
) -> Option<()> {
    match target {
        ast::Expr::Name(name) => {
            environment.insert(name.id.to_string(), value.clone());
            Some(())
        }
        // Exact destructuring would require projecting components from the symbolic value. Keep
        // it structurally normal but unavailable as a reusable result summary for now.
        _ => None,
    }
}

fn source_summary_expression(
    expression: &ast::Expr,
    environment: &BTreeMap<String, SourceSummaryExpression>,
    summaries: &BTreeMap<String, SourceCallSummary>,
) -> Option<SourceSummaryExpression> {
    match expression {
        ast::Expr::Constant(constant) => Some(SourceSummaryExpression::Constant(format!(
            "{:?}",
            constant.value
        ))),
        ast::Expr::Name(name) => environment.get(name.id.as_str()).cloned(),
        ast::Expr::Attribute(attribute) => Some(SourceSummaryExpression::Attribute(
            Box::new(source_summary_expression(
                &attribute.value,
                environment,
                summaries,
            )?),
            attribute.attr.to_string(),
        )),
        ast::Expr::UnaryOp(unary) => Some(SourceSummaryExpression::Unary(
            format!("{:?}", unary.op),
            Box::new(source_summary_expression(
                &unary.operand,
                environment,
                summaries,
            )?),
        )),
        ast::Expr::BinOp(binary)
            if matches!(
                binary.op,
                ast::Operator::Add | ast::Operator::Sub | ast::Operator::Mult
            ) =>
        {
            Some(SourceSummaryExpression::Binary(
                format!("{:?}", binary.op),
                Box::new(source_summary_expression(
                    &binary.left,
                    environment,
                    summaries,
                )?),
                Box::new(source_summary_expression(
                    &binary.right,
                    environment,
                    summaries,
                )?),
            ))
        }
        ast::Expr::BoolOp(boolean) => Some(SourceSummaryExpression::Boolean(
            format!("{:?}", boolean.op),
            boolean
                .values
                .iter()
                .map(|value| source_summary_expression(value, environment, summaries))
                .collect::<Option<Vec<_>>>()?,
        )),
        ast::Expr::Compare(compare) => Some(SourceSummaryExpression::Compare(
            Box::new(source_summary_expression(
                &compare.left,
                environment,
                summaries,
            )?),
            compare
                .ops
                .iter()
                .zip(&compare.comparators)
                .map(|(operator, value)| {
                    Some((
                        format!("{operator:?}"),
                        source_summary_expression(value, environment, summaries)?,
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
        )),
        ast::Expr::IfExp(conditional) => Some(SourceSummaryExpression::Conditional(
            Box::new(source_summary_expression(
                &conditional.test,
                environment,
                summaries,
            )?),
            Box::new(source_summary_expression(
                &conditional.body,
                environment,
                summaries,
            )?),
            Box::new(source_summary_expression(
                &conditional.orelse,
                environment,
                summaries,
            )?),
        )),
        ast::Expr::Tuple(tuple) => Some(SourceSummaryExpression::Tuple(
            tuple
                .elts
                .iter()
                .map(|value| source_summary_expression(value, environment, summaries))
                .collect::<Option<Vec<_>>>()?,
        )),
        ast::Expr::List(list) => Some(SourceSummaryExpression::List(
            list.elts
                .iter()
                .map(|value| source_summary_expression(value, environment, summaries))
                .collect::<Option<Vec<_>>>()?,
        )),
        ast::Expr::Set(set) => Some(SourceSummaryExpression::Set(
            set.elts
                .iter()
                .map(|value| source_summary_expression(value, environment, summaries))
                .collect::<Option<Vec<_>>>()?,
        )),
        ast::Expr::Dict(dict) if dict.keys.iter().all(Option::is_some) => {
            Some(SourceSummaryExpression::Dict(
                dict.keys
                    .iter()
                    .flatten()
                    .zip(&dict.values)
                    .map(|(key, value)| {
                        Some((
                            source_summary_expression(key, environment, summaries)?,
                            source_summary_expression(value, environment, summaries)?,
                        ))
                    })
                    .collect::<Option<Vec<_>>>()?,
            ))
        }
        ast::Expr::Call(call) if call.keywords.is_empty() => {
            let ast::Expr::Name(name) = call.func.as_ref() else {
                return None;
            };
            let summary = summaries.get(name.id.as_str())?;
            if call.args.len() != summary.parameters.len() {
                return None;
            }
            let arguments = call
                .args
                .iter()
                .map(|argument| source_summary_expression(argument, environment, summaries))
                .collect::<Option<Vec<_>>>()?;
            substitute_source_summary_expression(&summary.result, &arguments)
        }
        _ => None,
    }
}

fn substitute_source_summary_expression(
    expression: &SourceSummaryExpression,
    arguments: &[SourceSummaryExpression],
) -> Option<SourceSummaryExpression> {
    Some(match expression {
        SourceSummaryExpression::Constant(value) => {
            SourceSummaryExpression::Constant(value.clone())
        }
        SourceSummaryExpression::Parameter(index) => arguments.get(*index)?.clone(),
        SourceSummaryExpression::Attribute(value, field) => SourceSummaryExpression::Attribute(
            Box::new(substitute_source_summary_expression(value, arguments)?),
            field.clone(),
        ),
        SourceSummaryExpression::Unary(operator, value) => SourceSummaryExpression::Unary(
            operator.clone(),
            Box::new(substitute_source_summary_expression(value, arguments)?),
        ),
        SourceSummaryExpression::Binary(operator, left, right) => SourceSummaryExpression::Binary(
            operator.clone(),
            Box::new(substitute_source_summary_expression(left, arguments)?),
            Box::new(substitute_source_summary_expression(right, arguments)?),
        ),
        SourceSummaryExpression::Boolean(operator, values) => SourceSummaryExpression::Boolean(
            operator.clone(),
            values
                .iter()
                .map(|value| substitute_source_summary_expression(value, arguments))
                .collect::<Option<Vec<_>>>()?,
        ),
        SourceSummaryExpression::Compare(left, comparisons) => SourceSummaryExpression::Compare(
            Box::new(substitute_source_summary_expression(left, arguments)?),
            comparisons
                .iter()
                .map(|(operator, value)| {
                    Some((
                        operator.clone(),
                        substitute_source_summary_expression(value, arguments)?,
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
        ),
        SourceSummaryExpression::Conditional(test, body, otherwise) => {
            SourceSummaryExpression::Conditional(
                Box::new(substitute_source_summary_expression(test, arguments)?),
                Box::new(substitute_source_summary_expression(body, arguments)?),
                Box::new(substitute_source_summary_expression(otherwise, arguments)?),
            )
        }
        SourceSummaryExpression::Tuple(values) => SourceSummaryExpression::Tuple(
            values
                .iter()
                .map(|value| substitute_source_summary_expression(value, arguments))
                .collect::<Option<Vec<_>>>()?,
        ),
        SourceSummaryExpression::List(values) => SourceSummaryExpression::List(
            values
                .iter()
                .map(|value| substitute_source_summary_expression(value, arguments))
                .collect::<Option<Vec<_>>>()?,
        ),
        SourceSummaryExpression::Set(values) => SourceSummaryExpression::Set(
            values
                .iter()
                .map(|value| substitute_source_summary_expression(value, arguments))
                .collect::<Option<Vec<_>>>()?,
        ),
        SourceSummaryExpression::Dict(entries) => SourceSummaryExpression::Dict(
            entries
                .iter()
                .map(|(key, value)| {
                    Some((
                        substitute_source_summary_expression(key, arguments)?,
                        substitute_source_summary_expression(value, arguments)?,
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
        ),
    })
}

/// Elaborate canonical secure-information-flow contracts into ordinary boolean VCs only after a
/// closed label analysis has established their truth value.
pub(super) fn lower_canonical_low_contracts(
    suite: Vec<ast::Stmt>,
    profile: InformationFlowVerificationProfile,
) -> Result<Vec<ast::Stmt>, ContractFailure> {
    if !profile.is_secure() {
        return Ok(suite);
    }
    let canonical_contracts = canonical_contract_bindings(&suite);
    if !canonical_contracts.contains("Low") {
        return Ok(suite);
    }
    let class_bases = collect_class_bases(&suite);
    let source_calls = Arc::new(source_call_summaries(&suite, &canonical_contracts));
    let mut results = BTreeMap::new();
    for statement in &suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                analyze_function(
                    function,
                    &canonical_contracts,
                    &class_bases,
                    &source_calls,
                    &mut results,
                )?;
            }
            ast::Stmt::ClassDef(class) => {
                for item in &class.body {
                    if let ast::Stmt::FunctionDef(function) = item {
                        analyze_function(
                            function,
                            &canonical_contracts,
                            &class_bases,
                            &source_calls,
                            &mut results,
                        )?;
                    }
                }
            }
            _ => {}
        }
    }
    suite
        .into_iter()
        .map(|statement| LowResultRewriter { results: &results }.fold_stmt(statement))
        .collect()
}

fn canonical_contract_bindings(suite: &[ast::Stmt]) -> BTreeSet<String> {
    let mut canonical = BUILTIN_VALUE_CALLS
        .into_iter()
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    for statement in suite {
        match statement {
            ast::Stmt::ImportFrom(import)
                if import.level.is_none_or(|level| level == 0_u32)
                    && import
                        .module
                        .as_ref()
                        .is_some_and(|module| module.as_str() == "nagini_contracts.contracts") =>
            {
                for alias in &import.names {
                    if alias.name.as_str() == "*" {
                        canonical.insert("Low".to_owned());
                        canonical.extend(CONTRACT_NAMES.into_iter().map(str::to_owned));
                        canonical.extend(NAGINI_VALUE_NAMES.into_iter().map(str::to_owned));
                        continue;
                    }
                    let bound = alias
                        .asname
                        .as_ref()
                        .map_or(alias.name.as_str(), |name| name.as_str());
                    // Every import binds its target, even when the imported symbol is unrelated
                    // to SIF.  For example, `Acc as len` shadows the builtin and must not leave
                    // `len` privileged.  Aliased SIF primitives remain unsupported rather than
                    // losing their provenance in this name-only binding table.
                    canonical.remove(bound);
                    if bound == alias.name.as_str()
                        && (bound == "Low"
                            || CONTRACT_NAMES.contains(&bound)
                            || NAGINI_VALUE_NAMES.contains(&bound))
                    {
                        canonical.insert(bound.to_owned());
                    }
                }
            }
            other => {
                for name in canonical.clone() {
                    if statement_binds_name_recursive(other, &name) {
                        canonical.remove(&name);
                    }
                }
            }
        }
    }
    canonical
}

fn collect_class_bases(suite: &[ast::Stmt]) -> BTreeMap<String, Vec<String>> {
    let mut classes = BTreeMap::from([
        ("BaseException".to_owned(), Vec::new()),
        ("Exception".to_owned(), vec!["BaseException".to_owned()]),
    ]);
    for statement in suite {
        let ast::Stmt::ClassDef(class) = statement else {
            continue;
        };
        let bases = class
            .bases
            .iter()
            .filter_map(|base| match base {
                ast::Expr::Name(name) => Some(name.id.to_string()),
                _ => None,
            })
            .collect();
        classes.insert(class.name.to_string(), bases);
    }
    classes
}

fn analyze_function(
    function: &ast::StmtFunctionDef,
    canonical_names: &BTreeSet<String>,
    class_bases: &BTreeMap<String, Vec<String>>,
    source_calls: &Arc<BTreeMap<String, SourceCallSummary>>,
    results: &mut BTreeMap<u32, bool>,
) -> Result<(), ContractFailure> {
    let mut calls = CanonicalLowCalls::default();
    for statement in function.body.iter().cloned() {
        calls.visit_stmt(statement);
    }
    if calls.offsets.is_empty() {
        return Ok(());
    }
    let low_active = !function_binds_name(function, "Low");
    if !low_active {
        // Lexically shadowed names are ordinary Python callables.  Leaving them unchanged is
        // essential: the regular call frontend must resolve or reject them without SIF magic.
        return Ok(());
    }
    if canonical_names.iter().any(|name| {
        name != "Low"
            && !CONTRACT_NAMES.contains(&name.as_str())
            && !NAGINI_VALUE_NAMES.contains(&name.as_str())
            && !BUILTIN_VALUE_CALLS.contains(&name.as_str())
    }) {
        return unsupported("aliased Low bindings are not yet accepted by the heap SIF frontend");
    }
    let active_contracts = CONTRACT_NAMES
        .into_iter()
        .filter(|name| canonical_names.contains(*name) && !function_binds_name(function, name))
        .collect::<BTreeSet<_>>();
    let mut canonical_calls = BTreeSet::new();
    for name in NAGINI_VALUE_NAMES {
        if canonical_names.contains(name) && !function_binds_name(function, name) {
            canonical_calls.insert(name.to_owned());
        }
    }
    for name in BUILTIN_VALUE_CALLS {
        if canonical_names.contains(name) && !function_binds_name(function, name) {
            canonical_calls.insert(name.to_owned());
        }
    }

    let active_source_calls = source_calls
        .iter()
        .filter(|(name, _)| !function_binds_name(function, name))
        .map(|(name, summary)| (name.clone(), summary.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut initial = LabelState::normal(
        function_parameter_names(function).into_iter(),
        canonical_calls,
    );
    initial.source_calls = Arc::new(active_source_calls);
    let mut executable = Vec::new();
    let mut postconditions = Vec::new();
    let mut exception_postconditions = Vec::new();
    for statement in &function.body {
        match direct_contract(statement).filter(|(name, _)| active_contracts.contains(name)) {
            Some(("Requires", expression)) => {
                assume_low_requirements(expression, &mut initial, results)?;
            }
            Some(("Ensures", expression)) => postconditions.push(expression),
            Some(("Exsures", expression)) => exception_postconditions.push(expression),
            Some(("Invariant", expression)) if contains_canonical_low(expression) => {
                return unsupported(
                    "Low(...) loop invariants require the relational loop-label engine",
                );
            }
            _ => executable.push(statement),
        }
    }
    let exits = analyze_statements(
        &executable,
        vec![initial],
        class_bases,
        &active_contracts,
        results,
    )?;
    let normal = exits
        .iter()
        .filter(|state| matches!(state.exit, FlowExit::Normal | FlowExit::Return { .. }))
        .collect::<Vec<_>>();
    for expression in postconditions {
        evaluate_low_contracts(expression, &normal, results)?;
    }
    for expression in exception_postconditions {
        let exceptional = exits
            .iter()
            .filter(|state| matches!(state.exit, FlowExit::Raise { .. }))
            .collect::<Vec<_>>();
        evaluate_low_contracts(expression, &exceptional, results)?;
    }
    Ok(())
}

fn function_parameter_names(function: &ast::StmtFunctionDef) -> Vec<String> {
    let mut names = function
        .args
        .posonlyargs
        .iter()
        .chain(function.args.args.iter())
        .chain(function.args.kwonlyargs.iter())
        .map(|argument| argument.def.arg.to_string())
        .collect::<Vec<_>>();
    if let Some(argument) = function.args.vararg.as_deref() {
        names.push(argument.arg.to_string());
    }
    if let Some(argument) = function.args.kwarg.as_deref() {
        names.push(argument.arg.to_string());
    }
    names
}

fn function_binds_name(function: &ast::StmtFunctionDef, name: &str) -> bool {
    function_parameter_names(function)
        .iter()
        .any(|item| item == name)
        || function
            .body
            .iter()
            .any(|statement| statement_binds_name_recursive(statement, name))
        || function.body.iter().any(|statement| {
            let mut binding = NamedExpressionBinding {
                name: name.to_owned(),
                found: false,
            };
            binding.visit_stmt(statement.clone());
            binding.found
        })
}

fn statement_binds_name_recursive(statement: &ast::Stmt, name: &str) -> bool {
    if statement_binds_name(statement, name) {
        return true;
    }
    match statement {
        ast::Stmt::If(branch) => branch
            .body
            .iter()
            .chain(branch.orelse.iter())
            .any(|item| statement_binds_name_recursive(item, name)),
        ast::Stmt::Try(try_) => {
            try_.body
                .iter()
                .chain(try_.orelse.iter())
                .chain(try_.finalbody.iter())
                .any(|item| statement_binds_name_recursive(item, name))
                || try_.handlers.iter().any(|handler| {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    handler
                        .name
                        .as_ref()
                        .is_some_and(|item| item.as_str() == name)
                        || handler
                            .body
                            .iter()
                            .any(|item| statement_binds_name_recursive(item, name))
                })
        }
        ast::Stmt::While(loop_) => loop_
            .body
            .iter()
            .chain(loop_.orelse.iter())
            .any(|item| statement_binds_name_recursive(item, name)),
        ast::Stmt::For(loop_) => {
            target_binds_name(&loop_.target, name)
                || loop_
                    .body
                    .iter()
                    .chain(loop_.orelse.iter())
                    .any(|item| statement_binds_name_recursive(item, name))
        }
        ast::Stmt::With(with_) => with_.body.iter().any(|item| {
            statement_binds_name_recursive(item, name)
                || with_.items.iter().any(|item| {
                    item.optional_vars
                        .as_deref()
                        .is_some_and(|v| target_binds_name(v, name))
                })
        }),
        _ => false,
    }
}

fn statement_binds_name(statement: &ast::Stmt, name: &str) -> bool {
    match statement {
        ast::Stmt::FunctionDef(function) => function.name.as_str() == name,
        ast::Stmt::ClassDef(class) => class.name.as_str() == name,
        ast::Stmt::Assign(assignment) => assignment
            .targets
            .iter()
            .any(|target| target_binds_name(target, name)),
        ast::Stmt::AnnAssign(assignment) => target_binds_name(&assignment.target, name),
        ast::Stmt::AugAssign(assignment) => target_binds_name(&assignment.target, name),
        ast::Stmt::Import(import) => import.names.iter().any(|alias| {
            alias.asname.as_ref().map_or_else(
                || alias.name.as_str().split('.').next().unwrap_or_default(),
                |alias| alias.as_str(),
            ) == name
        }),
        ast::Stmt::ImportFrom(import) => import.names.iter().any(|alias| {
            alias
                .asname
                .as_ref()
                .map_or(alias.name.as_str(), |alias| alias.as_str())
                == name
        }),
        _ => false,
    }
}

fn target_binds_name(target: &ast::Expr, name: &str) -> bool {
    match target {
        ast::Expr::Name(target) => target.id.as_str() == name,
        ast::Expr::Tuple(tuple) => tuple.elts.iter().any(|item| target_binds_name(item, name)),
        ast::Expr::List(list) => list.elts.iter().any(|item| target_binds_name(item, name)),
        _ => false,
    }
}

fn direct_contract(statement: &ast::Stmt) -> Option<(&str, &ast::Expr)> {
    let ast::Stmt::Expr(expression) = statement else {
        return None;
    };
    let ast::Expr::Call(call) = expression.value.as_ref() else {
        return None;
    };
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return None;
    };
    if call.args.len() != 1 || !call.keywords.is_empty() {
        return None;
    }
    matches!(
        name.id.as_str(),
        "Requires" | "Ensures" | "Exsures" | "Invariant" | "Assert"
    )
    .then_some((name.id.as_str(), &call.args[0]))
}

fn assume_low_requirements(
    expression: &ast::Expr,
    state: &mut LabelState,
    results: &mut BTreeMap<u32, bool>,
) -> Result<(), ContractFailure> {
    let calls = collect_positive_conjunctive_low_calls(expression)?;
    for call in calls {
        let argument = low_argument(call)?;
        assume_expression_low(argument, state)?;
        results.insert(u32::from(call.range.start()), true);
    }
    Ok(())
}

/// Return only `Low` facts which are logically entailed by the complete precondition.
///
/// A direct `Low(e)` conjunct is entailed by a conjunction.  A `Low` occurrence under any other
/// connective is not unconditional: in particular, neither `not Low(e)` nor `Low(e) or p`
/// establishes that `e` is low.  Refusing those shapes prevents the ordinary boolean backend
/// from obtaining a vacuous precondition after relational lowering.
fn collect_positive_conjunctive_low_calls(
    expression: &ast::Expr,
) -> Result<Vec<&ast::ExprCall>, ContractFailure> {
    match expression {
        ast::Expr::Call(call) if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Low") => {
            Ok(vec![call])
        }
        ast::Expr::BoolOp(boolean) if boolean.op == ast::BoolOp::And => {
            let mut calls = Vec::new();
            for value in &boolean.values {
                calls.extend(collect_positive_conjunctive_low_calls(value)?);
            }
            Ok(calls)
        }
        _ if contains_canonical_low(expression) => {
            unsupported("Low(...) preconditions must occur as positive, unconditional conjunctions")
        }
        _ => Ok(Vec::new()),
    }
}

fn evaluate_low_contracts(
    expression: &ast::Expr,
    states: &[&LabelState],
    results: &mut BTreeMap<u32, bool>,
) -> Result<(), ContractFailure> {
    validate_positive_low_polarity(expression)?;
    let calls = collect_direct_low_calls(expression)?;
    for call in calls {
        let argument = low_argument(call)?;
        let mut proved = true;
        for state in states {
            if !expression_is_low(argument, state)? {
                proved = false;
                break;
            }
        }
        results.insert(u32::from(call.range.start()), proved);
    }
    Ok(())
}

/// The pass summarizes each `Low(e)` across all reachable states before the ordinary solver sees
/// the surrounding formula.  That universal summary is sound in positive boolean positions, but
/// not under negation or in an implication antecedent: `(forall p, Low_p(x)) -> ...` is weaker
/// than `forall p, (Low_p(x) -> ...)`.  Refuse those positions until the relational formula itself
/// is discharged per path.
fn validate_positive_low_polarity(expression: &ast::Expr) -> Result<(), ContractFailure> {
    match expression {
        ast::Expr::Call(call) if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Low") => {
            Ok(())
        }
        ast::Expr::BoolOp(boolean) => {
            for value in &boolean.values {
                validate_positive_low_polarity(value)?;
            }
            Ok(())
        }
        ast::Expr::Call(call)
            if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Implies")
                && call.args.len() == 2
                && call.keywords.is_empty() =>
        {
            if contains_canonical_low(&call.args[0]) {
                return unsupported(
                    "Low(...) in an implication antecedent requires path-relational discharge",
                );
            }
            validate_positive_low_polarity(&call.args[1])
        }
        ast::Expr::UnaryOp(unary) if contains_canonical_low(&unary.operand) => {
            unsupported("Low(...) under unary negation requires path-relational discharge")
        }
        _ if contains_canonical_low(expression) => {
            unsupported("Low(...) occurs in a non-positive information-flow contract position")
        }
        _ => Ok(()),
    }
}

fn collect_direct_low_calls(
    expression: &ast::Expr,
) -> Result<Vec<&ast::ExprCall>, ContractFailure> {
    fn walk<'a>(
        expression: &'a ast::Expr,
        calls: &mut Vec<&'a ast::ExprCall>,
    ) -> Result<(), ContractFailure> {
        match expression {
            ast::Expr::Call(call) if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Low") =>
            {
                calls.push(call);
                Ok(())
            }
            ast::Expr::BoolOp(boolean) => {
                for value in &boolean.values {
                    walk(value, calls)?;
                }
                Ok(())
            }
            ast::Expr::UnaryOp(unary) => walk(&unary.operand, calls),
            ast::Expr::BinOp(binary) => {
                walk(&binary.left, calls)?;
                walk(&binary.right, calls)
            }
            ast::Expr::Compare(compare) => {
                walk(&compare.left, calls)?;
                for value in &compare.comparators {
                    walk(value, calls)?;
                }
                Ok(())
            }
            ast::Expr::IfExp(conditional) => {
                walk(&conditional.test, calls)?;
                walk(&conditional.body, calls)?;
                walk(&conditional.orelse, calls)
            }
            ast::Expr::Call(call) => {
                for argument in &call.args {
                    walk(argument, calls)?;
                }
                for keyword in &call.keywords {
                    walk(&keyword.value, calls)?;
                }
                Ok(())
            }
            ast::Expr::Attribute(attribute) => walk(&attribute.value, calls),
            ast::Expr::Tuple(tuple) => {
                for item in &tuple.elts {
                    walk(item, calls)?;
                }
                Ok(())
            }
            _ if contains_canonical_low(expression) => unsupported(
                "Low(...) occurs in an unsupported information-flow contract expression",
            ),
            _ => Ok(()),
        }
    }
    let mut calls = Vec::new();
    walk(expression, &mut calls)?;
    Ok(calls)
}

fn contains_canonical_low(expression: &ast::Expr) -> bool {
    let mut calls = CanonicalLowCalls::default();
    calls.visit_expr(expression.clone());
    !calls.offsets.is_empty()
}

fn low_argument(call: &ast::ExprCall) -> Result<&ast::Expr, ContractFailure> {
    if !call.keywords.is_empty() || call.args.len() != 1 {
        return unsupported("Low(...) requires exactly one positional expression");
    }
    Ok(&call.args[0])
}

fn assume_expression_low(
    expression: &ast::Expr,
    state: &mut LabelState,
) -> Result<(), ContractFailure> {
    if let ast::Expr::Name(name) = expression {
        let name = name.id.to_string();
        state.locals.insert(name.clone(), true);
        state
            .canonical_low_terms
            .entry(name.clone())
            .or_insert_with(|| format!("source:{name}"));
    } else if let Some(field) = field_key(expression) {
        state.fields.insert(field, true);
    } else {
        let key = expression_key(expression)?;
        state.exact_low_facts.insert(key.clone());
        state
            .exact_low_fact_dependencies
            .insert(key, expression_names(expression));
    }
    Ok(())
}

fn analyze_statements(
    statements: &[&ast::Stmt],
    mut states: Vec<LabelState>,
    class_bases: &BTreeMap<String, Vec<String>>,
    active_contracts: &BTreeSet<&str>,
    results: &mut BTreeMap<u32, bool>,
) -> Result<Vec<LabelState>, ContractFailure> {
    for statement in statements {
        let mut next = Vec::new();
        for state in states {
            if state.exit != FlowExit::Normal {
                next.push(state);
            } else {
                next.extend(analyze_statement(
                    statement,
                    state,
                    class_bases,
                    active_contracts,
                    results,
                )?);
            }
        }
        states = next;
    }
    Ok(states)
}

fn analyze_statement(
    statement: &ast::Stmt,
    mut state: LabelState,
    class_bases: &BTreeMap<String, Vec<String>>,
    active_contracts: &BTreeSet<&str>,
    results: &mut BTreeMap<u32, bool>,
) -> Result<Vec<LabelState>, ContractFailure> {
    match statement {
        ast::Stmt::Pass(_) => Ok(vec![state]),
        ast::Stmt::Assign(assignment) => {
            validate_runtime_expression(&assignment.value, &state)?;
            let value_low = expression_is_low(&assignment.value, &state)?;
            let canonical = value_low
                .then(|| canonical_low_term(&assignment.value, &state))
                .flatten();
            let low = state.pc_low && value_low;
            for target in &assignment.targets {
                assign_label(target, low, &mut state)?;
                assign_canonical_low_term(target, canonical.as_deref(), &mut state);
            }
            Ok(vec![state])
        }
        ast::Stmt::AnnAssign(assignment) => {
            let Some(value) = assignment.value.as_deref() else {
                return Ok(vec![state]);
            };
            validate_runtime_expression(value, &state)?;
            let value_low = expression_is_low(value, &state)?;
            let canonical = value_low
                .then(|| canonical_low_term(value, &state))
                .flatten();
            let low = state.pc_low && value_low;
            assign_label(&assignment.target, low, &mut state)?;
            assign_canonical_low_term(&assignment.target, canonical.as_deref(), &mut state);
            Ok(vec![state])
        }
        ast::Stmt::AugAssign(assignment) => {
            if !matches!(
                assignment.op,
                ast::Operator::Add | ast::Operator::Sub | ast::Operator::Mult
            ) {
                return unsupported(
                    "augmented assignment may have an unmodeled exceptional control channel",
                );
            }
            validate_runtime_expression(&assignment.target, &state)?;
            validate_runtime_expression(&assignment.value, &state)?;
            let old_low = expression_is_low(&assignment.target, &state)?;
            let value_low = expression_is_low(&assignment.value, &state)?;
            let canonical = (old_low && value_low)
                .then(|| {
                    Some(format!(
                        "binary:{:?}:{}:{}",
                        assignment.op,
                        canonical_low_term(&assignment.target, &state)?,
                        canonical_low_term(&assignment.value, &state)?
                    ))
                })
                .flatten();
            assign_label(
                &assignment.target,
                state.pc_low && old_low && value_low,
                &mut state,
            )?;
            assign_canonical_low_term(&assignment.target, canonical.as_deref(), &mut state);
            Ok(vec![state])
        }
        ast::Stmt::If(branch) => {
            validate_runtime_expression(&branch.test, &state)?;
            let guard_low = expression_is_low(&branch.test, &state)?;
            let outer = state.clone();
            let mut when_true = state.clone();
            when_true.pc_low &= guard_low;
            let mut when_false = state;
            when_false.pc_low &= guard_low;
            let mut paths = analyze_statements(
                &branch.body.iter().collect::<Vec<_>>(),
                vec![when_true],
                class_bases,
                active_contracts,
                results,
            )?;
            paths.extend(analyze_statements(
                &branch.orelse.iter().collect::<Vec<_>>(),
                vec![when_false],
                class_bases,
                active_contracts,
                results,
            )?);
            restore_if_fallthrough_labels(&mut paths, &outer, guard_low);
            Ok(paths)
        }
        ast::Stmt::Try(try_) => analyze_try(try_, state, class_bases, active_contracts, results),
        ast::Stmt::Raise(raise) => {
            if raise.cause.is_some() {
                return unsupported(
                    "exception causes require an explicit SIF evaluation-effect model",
                );
            }
            let Some(exception) = raise.exc.as_deref() else {
                return unsupported("bare raise requires active-handler label state");
            };
            let class = raised_exception_class(exception)?;
            state.exit = FlowExit::Raise {
                class,
                low_control: state.pc_low,
            };
            Ok(vec![state])
        }
        ast::Stmt::Return(return_) => {
            if let Some(value) = return_.value.as_deref() {
                validate_runtime_expression(value, &state)?;
            }
            let low = return_
                .value
                .as_deref()
                .map(|value| expression_is_low(value, &state))
                .transpose()?
                .unwrap_or(true)
                && state.pc_low;
            state.exit = FlowExit::Return { low };
            Ok(vec![state])
        }
        ast::Stmt::Break(_) => {
            state.exit = FlowExit::Break;
            Ok(vec![state])
        }
        ast::Stmt::Continue(_) => {
            state.exit = FlowExit::Continue;
            Ok(vec![state])
        }
        ast::Stmt::Expr(expression) => {
            if let Some(("Assert", inner)) = direct_contract(statement)
                && active_contracts.contains("Assert")
            {
                evaluate_low_contracts(inner, &[&state], results)?;
            } else if contains_canonical_low(&expression.value) {
                return unsupported("runtime Low(...) is supported only in Assert(...) contracts");
            } else if !matches!(expression.value.as_ref(), ast::Expr::Constant(_)) {
                return unsupported(
                    "runtime expression effects are outside the closed Low label analysis",
                );
            }
            Ok(vec![state])
        }
        _ => unsupported(format!(
            "statement {:?} is outside the closed Low label analysis",
            statement_name(statement)
        )),
    }
}

/// Accept only runtime expressions whose supported scalar interpretation has no unmodeled
/// exception edge.  Exceptions are control-flow observations in SIF: silently treating a
/// division, subscript, or call as a normal expression could make a handler selection depend on
/// secret data while the label analysis sees only the normal path.
fn validate_runtime_expression(
    expression: &ast::Expr,
    state: &LabelState,
) -> Result<(), ContractFailure> {
    match expression {
        ast::Expr::Constant(_) | ast::Expr::Name(_) => Ok(()),
        ast::Expr::Attribute(attribute) => validate_runtime_expression(&attribute.value, state),
        ast::Expr::UnaryOp(unary) => validate_runtime_expression(&unary.operand, state),
        ast::Expr::BinOp(binary)
            if matches!(
                binary.op,
                ast::Operator::Add | ast::Operator::Sub | ast::Operator::Mult
            ) =>
        {
            validate_runtime_expression(&binary.left, state)?;
            validate_runtime_expression(&binary.right, state)
        }
        ast::Expr::BoolOp(boolean) => {
            for value in &boolean.values {
                validate_runtime_expression(value, state)?;
            }
            Ok(())
        }
        ast::Expr::Compare(compare) => {
            validate_runtime_expression(&compare.left, state)?;
            for value in &compare.comparators {
                validate_runtime_expression(value, state)?;
            }
            Ok(())
        }
        ast::Expr::IfExp(conditional) => {
            validate_runtime_expression(&conditional.test, state)?;
            validate_runtime_expression(&conditional.body, state)?;
            validate_runtime_expression(&conditional.orelse, state)
        }
        ast::Expr::Tuple(tuple) => validate_runtime_expressions(&tuple.elts, state),
        ast::Expr::List(list) => validate_runtime_expressions(&list.elts, state),
        ast::Expr::Set(set) => validate_runtime_expressions(&set.elts, state),
        ast::Expr::Dict(dict) if dict.keys.iter().all(Option::is_some) => {
            for key in dict.keys.iter().flatten() {
                validate_runtime_expression(key, state)?;
            }
            validate_runtime_expressions(&dict.values, state)
        }
        ast::Expr::Call(call) if call.keywords.is_empty() => {
            let ast::Expr::Name(name) = call.func.as_ref() else {
                return unsupported(
                    "dynamic calls may have an unmodeled exceptional control channel",
                );
            };
            let Some(summary) = state.source_calls.get(name.id.as_str()) else {
                return unsupported(
                    "unknown calls may have an unmodeled exceptional control channel",
                );
            };
            if call.args.len() != summary.parameters.len() {
                return unsupported(
                    "source calls require the complete positional source signature",
                );
            }
            validate_runtime_expressions(&call.args, state)
        }
        _ => unsupported("runtime expression may have an unmodeled exceptional control channel"),
    }
}

fn validate_runtime_expressions(
    expressions: &[ast::Expr],
    state: &LabelState,
) -> Result<(), ContractFailure> {
    for expression in expressions {
        validate_runtime_expression(expression, state)?;
    }
    Ok(())
}

fn analyze_try(
    try_: &ast::StmtTry,
    state: LabelState,
    class_bases: &BTreeMap<String, Vec<String>>,
    active_contracts: &BTreeSet<&str>,
    results: &mut BTreeMap<u32, bool>,
) -> Result<Vec<LabelState>, ContractFailure> {
    let body = analyze_statements(
        &try_.body.iter().collect::<Vec<_>>(),
        vec![state],
        class_bases,
        active_contracts,
        results,
    )?;
    let mut before_finally = Vec::new();
    for mut path in body {
        match path.exit.clone() {
            FlowExit::Normal => before_finally.extend(analyze_statements(
                &try_.orelse.iter().collect::<Vec<_>>(),
                vec![path],
                class_bases,
                active_contracts,
                results,
            )?),
            FlowExit::Raise { class, low_control } => {
                let selected = try_.handlers.iter().find_map(|handler| {
                    let ast::ExceptHandler::ExceptHandler(handler) = handler;
                    handler_matches(handler.type_.as_deref(), &class, class_bases)
                        .then_some(handler)
                });
                let Some(handler) = selected else {
                    before_finally.push(path);
                    continue;
                };
                path.exit = FlowExit::Normal;
                path.pc_low &= low_control;
                if let Some(name) = &handler.name {
                    path.locals.insert(name.to_string(), low_control);
                }
                let mut handled = analyze_statements(
                    &handler.body.iter().collect::<Vec<_>>(),
                    vec![path],
                    class_bases,
                    active_contracts,
                    results,
                )?;
                for state in &mut handled {
                    if let Some(name) = &handler.name {
                        state.locals.remove(name.as_str());
                    }
                }
                before_finally.append(&mut handled);
            }
            _ => before_finally.push(path),
        }
    }
    if try_.finalbody.is_empty() {
        return Ok(before_finally);
    }
    let mut completed = Vec::new();
    for mut path in before_finally {
        let pending = path.exit.clone();
        path.exit = FlowExit::Normal;
        let final_paths = analyze_statements(
            &try_.finalbody.iter().collect::<Vec<_>>(),
            vec![path],
            class_bases,
            active_contracts,
            results,
        )?;
        for mut final_path in final_paths {
            if final_path.exit == FlowExit::Normal {
                final_path.exit = pending.clone();
            }
            completed.push(final_path);
        }
    }
    Ok(completed)
}

fn handler_matches(
    handler: Option<&ast::Expr>,
    exception: &str,
    class_bases: &BTreeMap<String, Vec<String>>,
) -> bool {
    match handler {
        None => true,
        Some(ast::Expr::Name(name)) => is_subtype(exception, name.id.as_str(), class_bases),
        Some(ast::Expr::Tuple(tuple)) => tuple
            .elts
            .iter()
            .any(|item| handler_matches(Some(item), exception, class_bases)),
        _ => false,
    }
}

fn is_subtype(actual: &str, expected: &str, class_bases: &BTreeMap<String, Vec<String>>) -> bool {
    if actual == expected {
        return true;
    }
    let mut work = vec![actual];
    let mut seen = BTreeSet::new();
    while let Some(current) = work.pop() {
        if !seen.insert(current.to_owned()) {
            continue;
        }
        if let Some(bases) = class_bases.get(current) {
            for base in bases {
                if base == expected {
                    return true;
                }
                work.push(base);
            }
        }
    }
    false
}

fn raised_exception_class(expression: &ast::Expr) -> Result<String, ContractFailure> {
    match expression {
        ast::Expr::Name(name) => Ok(name.id.to_string()),
        ast::Expr::Call(call) if call.args.is_empty() && call.keywords.is_empty() => {
            let ast::Expr::Name(name) = call.func.as_ref() else {
                return unsupported("raised Low-analyzed exception requires a direct class name");
            };
            Ok(name.id.to_string())
        }
        _ => unsupported(
            "raised Low-analyzed exception requires a direct class or zero-argument constructor",
        ),
    }
}

fn assign_label(
    target: &ast::Expr,
    low: bool,
    state: &mut LabelState,
) -> Result<(), ContractFailure> {
    match target {
        ast::Expr::Name(name) => {
            let rebound = name.id.as_str();
            state.exact_low_facts.retain(|fact| {
                !state
                    .exact_low_fact_dependencies
                    .get(fact)
                    .is_some_and(|dependencies| dependencies.contains(rebound))
            });
            state
                .exact_low_fact_dependencies
                .retain(|fact, _| state.exact_low_facts.contains(fact));
            let field_prefix = format!("name:{}.field:", name.id);
            state
                .fields
                .retain(|field, _| !field.starts_with(&field_prefix));
            state.locals.insert(name.id.to_string(), low);
            Ok(())
        }
        ast::Expr::Attribute(_) => {
            state.exact_low_facts.clear();
            state.exact_low_fact_dependencies.clear();
            let key = field_key(target).ok_or_else(|| ContractFailure {
                code: LOW_UNSUPPORTED,
                message: "Low label field writes require a direct local attribute chain".to_owned(),
            })?;
            // A source-level name is not an object identity: another local may alias this
            // receiver, and writing a parent field also invalidates every tracked descendant.
            // Without an alias analysis, retaining any prior syntactic field key can manufacture
            // a Low proof after a heap mutation.  Forget all prior heap labels, then record only
            // the field value established by this write.
            state.fields.clear();
            state.fields.insert(key, low);
            Ok(())
        }
        ast::Expr::Tuple(tuple) => {
            for item in &tuple.elts {
                assign_label(item, low, state)?;
            }
            Ok(())
        }
        ast::Expr::List(list) => {
            for item in &list.elts {
                assign_label(item, low, state)?;
            }
            Ok(())
        }
        _ => unsupported("Low label assignments require names, fields, or exact unpacking targets"),
    }
}

#[derive(Default)]
struct ExpressionNames {
    names: BTreeSet<String>,
}

impl Visitor for ExpressionNames {
    fn visit_expr_name(&mut self, node: ast::ExprName) {
        self.names.insert(node.id.to_string());
    }
}

fn expression_names(expression: &ast::Expr) -> BTreeSet<String> {
    let mut names = ExpressionNames::default();
    names.visit_expr(expression.clone());
    names.names
}

fn assign_canonical_low_term(target: &ast::Expr, term: Option<&str>, state: &mut LabelState) {
    match target {
        ast::Expr::Name(name) => {
            let name = name.id.to_string();
            if let Some(term) = term {
                state.canonical_low_terms.insert(name, term.to_owned());
            } else {
                state.canonical_low_terms.remove(&name);
            }
        }
        // Heap values are intentionally excluded from branch-value recovery until alias-aware
        // canonical heap terms exist. Equal source spelling is not object-identity proof.
        ast::Expr::Attribute(_) => {}
        ast::Expr::Tuple(tuple) => {
            for item in &tuple.elts {
                assign_canonical_low_term(item, None, state);
            }
        }
        ast::Expr::List(list) => {
            for item in &list.elts {
                assign_canonical_low_term(item, None, state);
            }
        }
        _ => {}
    }
}

fn source_call_summary<'a>(
    call: &ast::ExprCall,
    state: &'a LabelState,
) -> Option<&'a SourceCallSummary> {
    if !call.keywords.is_empty() {
        return None;
    }
    let ast::Expr::Name(name) = call.func.as_ref() else {
        return None;
    };
    let summary = state.source_calls.get(name.id.as_str())?;
    (call.args.len() == summary.parameters.len()).then_some(summary)
}

fn source_summary_expression_is_low(
    expression: &SourceSummaryExpression,
    arguments: &[ast::Expr],
    state: &LabelState,
) -> Result<bool, ContractFailure> {
    match expression {
        SourceSummaryExpression::Constant(_) => Ok(true),
        SourceSummaryExpression::Parameter(index) => arguments
            .get(*index)
            .map(|argument| expression_is_low(argument, state))
            .transpose()
            .map(Option::unwrap_or_default),
        SourceSummaryExpression::Attribute(_, _) => {
            Ok(source_summary_field_key(expression, arguments, state)
                .and_then(|key| state.fields.get(&key).copied())
                .unwrap_or(false))
        }
        SourceSummaryExpression::Unary(_, value) => {
            source_summary_expression_is_low(value, arguments, state)
        }
        SourceSummaryExpression::Binary(_, left, right) => {
            Ok(source_summary_expression_is_low(left, arguments, state)?
                && source_summary_expression_is_low(right, arguments, state)?)
        }
        SourceSummaryExpression::Boolean(_, values)
        | SourceSummaryExpression::Tuple(values)
        | SourceSummaryExpression::List(values)
        | SourceSummaryExpression::Set(values) => {
            for value in values {
                if !source_summary_expression_is_low(value, arguments, state)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        SourceSummaryExpression::Compare(left, comparisons) => {
            if !source_summary_expression_is_low(left, arguments, state)? {
                return Ok(false);
            }
            for (_, value) in comparisons {
                if !source_summary_expression_is_low(value, arguments, state)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        SourceSummaryExpression::Conditional(test, body, otherwise) => {
            Ok(source_summary_expression_is_low(test, arguments, state)?
                && source_summary_expression_is_low(body, arguments, state)?
                && source_summary_expression_is_low(otherwise, arguments, state)?)
        }
        SourceSummaryExpression::Dict(entries) => {
            for (key, value) in entries {
                if !source_summary_expression_is_low(key, arguments, state)?
                    || !source_summary_expression_is_low(value, arguments, state)?
                {
                    return Ok(false);
                }
            }
            Ok(true)
        }
    }
}

fn source_summary_field_key(
    expression: &SourceSummaryExpression,
    arguments: &[ast::Expr],
    state: &LabelState,
) -> Option<String> {
    match expression {
        SourceSummaryExpression::Parameter(index) => {
            expression_field_key(arguments.get(*index)?, state)
        }
        SourceSummaryExpression::Attribute(value, field) => Some(format!(
            "{}.field:{field}",
            source_summary_field_key(value, arguments, state)?
        )),
        _ => None,
    }
}

fn expression_field_key(expression: &ast::Expr, state: &LabelState) -> Option<String> {
    if let Some(key) = field_key(expression) {
        return Some(key);
    }
    let ast::Expr::Call(call) = expression else {
        return None;
    };
    let summary = source_call_summary(call, state)?;
    source_summary_field_key(&summary.result, &call.args, state)
}

fn source_summary_canonical_low_term(
    expression: &SourceSummaryExpression,
    arguments: &[ast::Expr],
    state: &LabelState,
) -> Option<String> {
    match expression {
        SourceSummaryExpression::Constant(value) => Some(format!("constant:{value}")),
        SourceSummaryExpression::Parameter(index) => {
            canonical_low_term(arguments.get(*index)?, state)
        }
        // Attribute identity is deliberately not reconstructed without alias-aware heap terms.
        SourceSummaryExpression::Attribute(_, _) => None,
        SourceSummaryExpression::Unary(operator, value) => Some(format!(
            "unary:{operator}:{}",
            source_summary_canonical_low_term(value, arguments, state)?
        )),
        SourceSummaryExpression::Binary(operator, left, right) => Some(format!(
            "binary:{operator}:{}:{}",
            source_summary_canonical_low_term(left, arguments, state)?,
            source_summary_canonical_low_term(right, arguments, state)?
        )),
        SourceSummaryExpression::Boolean(operator, values) => Some(format!(
            "bool:{operator}:[{}]",
            source_summary_canonical_values(values, arguments, state)?.join(",")
        )),
        SourceSummaryExpression::Compare(left, comparisons) => {
            let mut term = format!(
                "compare:{}",
                source_summary_canonical_low_term(left, arguments, state)?
            );
            for (operator, value) in comparisons {
                term.push_str(&format!(
                    ":{operator}:{}",
                    source_summary_canonical_low_term(value, arguments, state)?
                ));
            }
            Some(term)
        }
        SourceSummaryExpression::Conditional(test, body, otherwise) => Some(format!(
            "if:{}:{}:{}",
            source_summary_canonical_low_term(test, arguments, state)?,
            source_summary_canonical_low_term(body, arguments, state)?,
            source_summary_canonical_low_term(otherwise, arguments, state)?
        )),
        SourceSummaryExpression::Tuple(values) => Some(format!(
            "tuple:[{}]",
            source_summary_canonical_values(values, arguments, state)?.join(",")
        )),
        SourceSummaryExpression::List(values) => Some(format!(
            "list:[{}]",
            source_summary_canonical_values(values, arguments, state)?.join(",")
        )),
        SourceSummaryExpression::Set(values) => Some(format!(
            "set:[{}]",
            source_summary_canonical_values(values, arguments, state)?.join(",")
        )),
        SourceSummaryExpression::Dict(entries) => {
            let mut terms = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                terms.push(format!(
                    "{}:{}",
                    source_summary_canonical_low_term(key, arguments, state)?,
                    source_summary_canonical_low_term(value, arguments, state)?
                ));
            }
            Some(format!("dict:[{}]", terms.join(",")))
        }
    }
}

fn source_summary_canonical_values(
    values: &[SourceSummaryExpression],
    arguments: &[ast::Expr],
    state: &LabelState,
) -> Option<Vec<String>> {
    values
        .iter()
        .map(|value| source_summary_canonical_low_term(value, arguments, state))
        .collect()
}

/// Produce a source-stable symbolic value only for expressions already proved Low. Names are
/// substituted through earlier assignments, so z = 1; x = z and x = 1 have the same term.
/// Returning None merely disables equality recovery at a high-PC join; it never grants Low.
fn canonical_low_term(expression: &ast::Expr, state: &LabelState) -> Option<String> {
    match expression {
        ast::Expr::Constant(constant) => Some(format!("constant:{:?}", constant.value)),
        ast::Expr::Name(name) => state.canonical_low_terms.get(name.id.as_str()).cloned(),
        ast::Expr::UnaryOp(unary) => Some(format!(
            "unary:{:?}:{}",
            unary.op,
            canonical_low_term(&unary.operand, state)?
        )),
        ast::Expr::BinOp(binary) => Some(format!(
            "binary:{:?}:{}:{}",
            binary.op,
            canonical_low_term(&binary.left, state)?,
            canonical_low_term(&binary.right, state)?
        )),
        ast::Expr::BoolOp(boolean) => {
            let values = boolean
                .values
                .iter()
                .map(|value| canonical_low_term(value, state))
                .collect::<Option<Vec<_>>>()?;
            Some(format!("bool:{:?}:[{}]", boolean.op, values.join(",")))
        }
        ast::Expr::Compare(compare) => {
            let mut term = format!("compare:{}", canonical_low_term(&compare.left, state)?);
            for (operator, value) in compare.ops.iter().zip(&compare.comparators) {
                term.push_str(&format!(
                    ":{operator:?}:{}",
                    canonical_low_term(value, state)?
                ));
            }
            Some(term)
        }
        ast::Expr::IfExp(conditional) => Some(format!(
            "if:{}:{}:{}",
            canonical_low_term(&conditional.test, state)?,
            canonical_low_term(&conditional.body, state)?,
            canonical_low_term(&conditional.orelse, state)?
        )),
        ast::Expr::Tuple(tuple) => canonical_collection_term("tuple", &tuple.elts, state),
        ast::Expr::List(list) => canonical_collection_term("list", &list.elts, state),
        ast::Expr::Set(set) => canonical_collection_term("set", &set.elts, state),
        ast::Expr::Dict(dict) if dict.keys.iter().all(Option::is_some) => {
            let mut entries = Vec::with_capacity(dict.values.len());
            for (key, value) in dict.keys.iter().flatten().zip(&dict.values) {
                entries.push(format!(
                    "{}:{}",
                    canonical_low_term(key, state)?,
                    canonical_low_term(value, state)?
                ));
            }
            Some(format!("dict:[{}]", entries.join(",")))
        }
        ast::Expr::Subscript(subscript) => Some(format!(
            "subscript:{}:{}",
            canonical_low_term(&subscript.value, state)?,
            canonical_low_term(&subscript.slice, state)?
        )),
        ast::Expr::Slice(slice) => Some(format!(
            "slice:{}:{}:{}",
            canonical_optional_low_term(slice.lower.as_deref(), state)?,
            canonical_optional_low_term(slice.upper.as_deref(), state)?,
            canonical_optional_low_term(slice.step.as_deref(), state)?
        )),
        ast::Expr::Call(call)
            if matches!(call.func.as_ref(), ast::Expr::Name(name)
                if BUILTIN_VALUE_CALLS.contains(&name.id.as_str())
                    && state.canonical_calls.contains(name.id.as_str()))
                && call.keywords.is_empty() =>
        {
            let ast::Expr::Name(name) = call.func.as_ref() else {
                return None;
            };
            let arguments = call
                .args
                .iter()
                .map(|argument| canonical_low_term(argument, state))
                .collect::<Option<Vec<_>>>()?;
            Some(format!("call:{}:[{}]", name.id, arguments.join(",")))
        }
        ast::Expr::Call(call) => {
            let summary = source_call_summary(call, state)?;
            source_summary_canonical_low_term(&summary.result, &call.args, state)
        }
        // Attribute equality is not recovered from source spelling: aliases can invalidate it.
        _ => None,
    }
}

fn canonical_collection_term(
    kind: &str,
    values: &[ast::Expr],
    state: &LabelState,
) -> Option<String> {
    let values = values
        .iter()
        .map(|value| canonical_low_term(value, state))
        .collect::<Option<Vec<_>>>()?;
    Some(format!("{kind}:[{}]", values.join(",")))
}

fn canonical_optional_low_term(
    expression: Option<&ast::Expr>,
    state: &LabelState,
) -> Option<String> {
    expression.map_or_else(
        || Some("none".to_owned()),
        |expression| canonical_low_term(expression, state),
    )
}

fn restore_if_fallthrough_labels(paths: &mut [LabelState], outer: &LabelState, guard_low: bool) {
    let normal_indices = paths
        .iter()
        .enumerate()
        .filter_map(|(index, state)| (state.exit == FlowExit::Normal).then_some(index))
        .collect::<Vec<_>>();
    if normal_indices.is_empty() {
        return;
    }
    if guard_low {
        for index in normal_indices {
            paths[index].pc_low = outer.pc_low;
        }
        return;
    }

    let mut names = outer.locals.keys().cloned().collect::<BTreeSet<_>>();
    for index in &normal_indices {
        names.extend(paths[*index].locals.keys().cloned());
    }
    let written = names
        .into_iter()
        .filter(|name| {
            normal_indices.iter().any(|index| {
                paths[*index].locals.get(name) != outer.locals.get(name)
                    || paths[*index].canonical_low_terms.get(name)
                        != outer.canonical_low_terms.get(name)
            })
        })
        .collect::<Vec<_>>();

    for name in written {
        let agreed = normal_indices
            .first()
            .and_then(|index| paths[*index].canonical_low_terms.get(&name))
            .filter(|term| {
                normal_indices.iter().all(|index| {
                    paths[*index].locals.contains_key(&name)
                        && paths[*index].canonical_low_terms.get(&name) == Some(*term)
                })
            })
            .cloned();
        for index in &normal_indices {
            let path = &mut paths[*index];
            if let Some(term) = &agreed {
                path.locals.insert(name.clone(), true);
                path.canonical_low_terms.insert(name.clone(), term.clone());
            } else if path.locals.contains_key(&name) {
                path.locals.insert(name.clone(), false);
                path.canonical_low_terms.remove(&name);
            }
        }
    }
    for index in normal_indices {
        paths[index].pc_low = outer.pc_low;
    }
}

fn expression_is_low(expression: &ast::Expr, state: &LabelState) -> Result<bool, ContractFailure> {
    // Exact precondition facts cover only the deliberately small canonical key algebra.  A
    // missing exact key does not make the expression unsupported by itself: tuples, slices, and
    // canonical calls are handled compositionally below.  Propagating the key-construction error
    // here previously made those branches unreachable and was then masked as `false` by the
    // caller, which was unsound in negative logical positions.
    if expression_key(expression)
        .ok()
        .is_some_and(|key| state.exact_low_facts.contains(&key))
    {
        return Ok(true);
    }
    match expression {
        ast::Expr::Constant(_) => Ok(true),
        ast::Expr::Name(name) => Ok(state.locals.get(name.id.as_str()).copied().unwrap_or(false)),
        ast::Expr::Attribute(_) => Ok(field_key(expression)
            .and_then(|key| state.fields.get(&key).copied())
            .unwrap_or(false)),
        ast::Expr::UnaryOp(unary) => expression_is_low(&unary.operand, state),
        ast::Expr::BinOp(binary) => {
            Ok(expression_is_low(&binary.left, state)? && expression_is_low(&binary.right, state)?)
        }
        ast::Expr::BoolOp(boolean) => all_low(&boolean.values, state),
        ast::Expr::Compare(compare) => {
            Ok(expression_is_low(&compare.left, state)? && all_low(&compare.comparators, state)?)
        }
        ast::Expr::IfExp(conditional) => Ok(expression_is_low(&conditional.test, state)?
            && expression_is_low(&conditional.body, state)?
            && expression_is_low(&conditional.orelse, state)?),
        ast::Expr::Tuple(tuple) => all_low(&tuple.elts, state),
        ast::Expr::List(list) => all_low(&list.elts, state),
        ast::Expr::Set(set) => all_low(&set.elts, state),
        ast::Expr::Dict(dict) => {
            let keys_low = dict
                .keys
                .iter()
                .flatten()
                .map(|key| expression_is_low(key, state))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .all(|low| low);
            Ok(keys_low && all_low(&dict.values, state)?)
        }
        ast::Expr::Subscript(subscript) => Ok(expression_is_low(&subscript.value, state)?
            && expression_is_low(&subscript.slice, state)?),
        ast::Expr::Slice(slice) => {
            for bound in [
                slice.lower.as_deref(),
                slice.upper.as_deref(),
                slice.step.as_deref(),
            ]
            .into_iter()
            .flatten()
            {
                if !expression_is_low(bound, state)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        ast::Expr::Call(call)
            if matches!(call.func.as_ref(), ast::Expr::Name(name)
                if BUILTIN_VALUE_CALLS.contains(&name.id.as_str())
                    && state.canonical_calls.contains(name.id.as_str())) =>
        {
            if !call.keywords.is_empty() {
                return unsupported("Low expression builtin calls do not accept keyword effects");
            }
            all_low(&call.args, state)
        }
        ast::Expr::Call(call)
            if matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Result")
                && state.canonical_calls.contains("Result")
                && call.args.is_empty()
                && call.keywords.is_empty() =>
        {
            match state.exit {
                FlowExit::Return { low } => Ok(low),
                _ => Ok(false),
            }
        }
        ast::Expr::Call(call) => {
            let Some(summary) = source_call_summary(call, state) else {
                return unsupported("call is outside the closed source Low summary catalog");
            };
            source_summary_expression_is_low(&summary.result, &call.args, state)
        }
        _ => unsupported("expression is outside the closed Low label algebra"),
    }
}

fn all_low(expressions: &[ast::Expr], state: &LabelState) -> Result<bool, ContractFailure> {
    for expression in expressions {
        if !expression_is_low(expression, state)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn field_key(expression: &ast::Expr) -> Option<String> {
    match expression {
        ast::Expr::Name(name) => Some(format!("name:{}", name.id)),
        ast::Expr::Attribute(attribute) => Some(format!(
            "{}.field:{}",
            field_key(&attribute.value)?,
            attribute.attr
        )),
        _ => None,
    }
}

fn expression_key(expression: &ast::Expr) -> Result<String, ContractFailure> {
    match expression {
        ast::Expr::Name(name) => Ok(format!("name:{}", name.id)),
        ast::Expr::Constant(constant) => Ok(format!("constant:{:?}", constant.value)),
        ast::Expr::Attribute(_) => field_key(expression).ok_or_else(|| ContractFailure {
            code: LOW_UNSUPPORTED,
            message: "Low expression field key is not source-stable".to_owned(),
        }),
        ast::Expr::UnaryOp(unary) => Ok(format!(
            "unary:{:?}:{}",
            unary.op,
            expression_key(&unary.operand)?
        )),
        ast::Expr::BinOp(binary) => Ok(format!(
            "binary:{:?}:{}:{}",
            binary.op,
            expression_key(&binary.left)?,
            expression_key(&binary.right)?
        )),
        ast::Expr::Compare(compare) => {
            let mut key = format!("compare:{}", expression_key(&compare.left)?);
            for (operator, value) in compare.ops.iter().zip(&compare.comparators) {
                key.push_str(&format!(":{operator:?}:{}", expression_key(value)?));
            }
            Ok(key)
        }
        _ => unsupported("compound Low assumptions require a supported canonical expression"),
    }
}

fn statement_name(statement: &ast::Stmt) -> &'static str {
    match statement {
        ast::Stmt::FunctionDef(_) => "function definition",
        ast::Stmt::ClassDef(_) => "class definition",
        ast::Stmt::For(_) => "for",
        ast::Stmt::While(_) => "while",
        ast::Stmt::With(_) => "with",
        ast::Stmt::Match(_) => "match",
        ast::Stmt::Delete(_) => "delete",
        ast::Stmt::Import(_) | ast::Stmt::ImportFrom(_) => "import",
        _ => "unsupported statement",
    }
}

fn unsupported<T>(message: impl Into<String>) -> Result<T, ContractFailure> {
    Err(ContractFailure {
        code: LOW_UNSUPPORTED,
        message: message.into(),
    })
}

#[cfg(test)]
mod tests {
    use rustpython_parser::{Parse, ast};

    use super::*;

    fn lower(source: &str) -> Result<Vec<ast::Stmt>, ContractFailure> {
        let suite = ast::Suite::parse(source, "sif.py").expect("valid Python");
        lower_canonical_low_contracts(
            suite,
            InformationFlowVerificationProfile::SecureInformationFlow,
        )
    }

    #[test]
    fn a_low_guard_and_low_rhs_make_each_field_write_low() {
        lower(
            "from nagini_contracts.contracts import *\nclass E(Exception): pass\nclass Box:\n    value: int\ndef f(i: int, box: Box) -> None:\n    Requires(Low(i))\n    Ensures(Low(box.value))\n    try:\n        if i < 0:\n            raise E()\n        box.value = 0\n    except E:\n        box.value = -1\n",
        )
        .expect("the Low postcondition follows from every low-controlled path");
    }

    #[test]
    fn a_high_guard_taints_a_constant_field_write() {
        let lowered = lower(
            "from nagini_contracts.contracts import *\nclass Box:\n    value: int\ndef f(secret: bool, box: Box) -> None:\n    Ensures(Low(box.value))\n    if secret:\n        box.value = 0\n    else:\n        box.value = 1\n",
        )
        .expect("a security violation is a false VC, not a frontend crash");
        let function = lowered
            .iter()
            .find_map(|statement| match statement {
                ast::Stmt::FunctionDef(function) => Some(function),
                _ => None,
            })
            .expect("function remains present");
        let Some(("Ensures", ast::Expr::Constant(constant))) =
            function.body.first().and_then(direct_contract)
        else {
            panic!("Low postcondition was not elaborated into a boolean VC")
        };
        assert_eq!(constant.value, ast::Constant::Bool(false));
    }

    #[test]
    fn a_total_field_reader_substitutes_the_callers_field_label() {
        let lowered = lower(
            "from nagini_contracts.contracts import *\nclass Box:\n    value: int\ndef read(box: Box) -> int:\n    return box.value\ndef positive(box: Box) -> int:\n    Requires(Low(box.value))\n    Ensures(Low(Result()))\n    return read(box)\ndef negative(box: Box) -> int:\n    Ensures(Low(Result()))\n    return read(box)\n",
        )
        .expect("the closed field-reader source call must lower");

        let postcondition = |owner: &str| {
            lowered.iter().find_map(|statement| {
                let ast::Stmt::FunctionDef(function) = statement else {
                    return None;
                };
                if function.name.as_str() != owner {
                    return None;
                }
                function.body.iter().find_map(|statement| {
                    let Some(("Ensures", ast::Expr::Constant(constant))) =
                        direct_contract(statement)
                    else {
                        return None;
                    };
                    let ast::Constant::Bool(value) = constant.value else {
                        return None;
                    };
                    Some(value)
                })
            })
        };

        assert_eq!(postcondition("positive"), Some(true));
        assert_eq!(postcondition("negative"), Some(false));
    }

    #[test]
    fn a_conditional_result_substitutes_every_controlling_argument_label() {
        let lowered = lower(
            "from nagini_contracts.contracts import *\ndef choose(flag: bool, left: int, right: int) -> int:\n    if flag:\n        return left\n    return right\ndef positive(flag: bool, left: int, right: int) -> int:\n    Requires(Low(flag) and Low(left) and Low(right))\n    Ensures(Low(Result()))\n    return choose(flag, left, right)\ndef negative(secret: bool, left: int, right: int) -> int:\n    Requires(Low(left) and Low(right))\n    Ensures(Low(Result()))\n    return choose(secret, left, right)\n",
        )
        .expect("the closed conditional-result source call must lower");

        let postcondition = |owner: &str| {
            lowered.iter().find_map(|statement| {
                let ast::Stmt::FunctionDef(function) = statement else {
                    return None;
                };
                if function.name.as_str() != owner {
                    return None;
                }
                function.body.iter().find_map(|statement| {
                    let Some(("Ensures", ast::Expr::Constant(constant))) =
                        direct_contract(statement)
                    else {
                        return None;
                    };
                    let ast::Constant::Bool(value) = constant.value else {
                        return None;
                    };
                    Some(value)
                })
            })
        };

        assert_eq!(postcondition("positive"), Some(true));
        assert_eq!(postcondition("negative"), Some(false));
    }

    #[test]
    fn lexical_shadowing_never_acquires_canonical_low_semantics() {
        let lowered = lower(
            "from nagini_contracts.contracts import *\ndef f(Low: object, x: int) -> None:\n    Ensures(Low(x))\n",
        )
        .expect("shadowed Low remains an ordinary call for the main frontend");
        let function = lowered
            .iter()
            .find_map(|statement| match statement {
                ast::Stmt::FunctionDef(function) => Some(function),
                _ => None,
            })
            .expect("function remains present");
        let Some(("Ensures", ast::Expr::Call(call))) =
            function.body.first().and_then(direct_contract)
        else {
            panic!("shadowed Low call was incorrectly elaborated")
        };
        assert!(matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "Low"));
    }

    #[test]
    fn declassified_termination_condition_is_low_but_secret_condition_is_not() {
        let suite = ast::Suite::parse(
            "from nagini_contracts.contracts import *\ndef bad(secret: int) -> None:\n    Requires(LowEvent())\n    while secret != 0:\n        Invariant(TerminatesSif(secret >= 0, secret))\n        secret -= 1\ndef good(secret: int) -> None:\n    Requires(LowEvent())\n    Declassify(secret > 0)\n    while secret != 0:\n        Invariant(TerminatesSif(secret <= 0, secret))\n        secret -= 1\n",
            "termination.py",
        )
        .unwrap();
        let analysis = analyze_termination_channels(
            &suite,
            InformationFlowVerificationProfile::SecureInformationFlow,
        )
        .unwrap()
        .unwrap();
        assert_eq!(analysis.failures.len(), 1, "{analysis:#?}");
        assert_eq!(analysis.failures[0].owner, "bad");
        assert_eq!(
            analysis.failures[0].kind,
            SifTerminationFailureKind::ConditionNotLow
        );
    }

    #[test]
    fn exact_joana_fixed_function_declassifies_its_termination_condition() {
        let source = include_str!(
            "../.upstream/nagini/tests/sif-true/verification/examples/joana-fig3-tr.py"
        );
        let suite = ast::Suite::parse(source, "joana-fig3-tr.py").unwrap();
        let canonical = canonical_termination_bindings(&suite);
        assert!(canonical.contains("Declassify"), "{canonical:#?}");
        let fixed = suite
            .iter()
            .find_map(|statement| match statement {
                ast::Stmt::FunctionDef(function) if function.name.as_str() == "main_fixed" => {
                    Some(function)
                }
                _ => None,
            })
            .unwrap();
        let loop_index = fixed
            .body
            .iter()
            .position(|statement| matches!(statement, ast::Stmt::While(_)))
            .unwrap();
        let mut state =
            LabelState::normal(function_parameter_names(fixed).into_iter(), BTreeSet::new());
        analyze_termination_statements(
            &fixed.body[..loop_index],
            "main_fixed",
            &canonical,
            true,
            &mut state,
            &mut Vec::new(),
            false,
        )
        .unwrap();
        let ast::Stmt::While(loop_) = &fixed.body[loop_index] else {
            unreachable!()
        };
        let (condition, _, _) = loop_
            .body
            .iter()
            .find_map(|statement| termination_contract(statement, &canonical))
            .unwrap();
        assert!(
            channel_expression_is_low(condition, &state).unwrap(),
            "{state:#?}"
        );
        let analysis = analyze_termination_channels(
            &suite,
            InformationFlowVerificationProfile::SecureInformationFlow,
        )
        .unwrap()
        .unwrap();
        assert_eq!(analysis.failures.len(), 1, "{analysis:#?}");
        assert_eq!(analysis.failures[0].owner, "main");
    }

    #[test]
    fn exact_termination_channel_suite_derives_each_channel_failure() {
        let source = include_str!(
            "../.upstream/nagini/tests/sif-true/verification/test_termination_channels.py"
        );
        let suite = ast::Suite::parse(source, "test_termination_channels.py").unwrap();
        let analysis = analyze_termination_channels(
            &suite,
            InformationFlowVerificationProfile::SecureInformationFlow,
        )
        .unwrap()
        .unwrap();
        let failures = analysis
            .failures
            .iter()
            .map(|failure| (failure.owner.as_str(), failure.kind))
            .collect::<Vec<_>>();
        assert_eq!(
            failures,
            vec![
                ("loop_no_lowevent", SifTerminationFailureKind::NotLowEvent),
                (
                    "loop_termcond_high",
                    SifTerminationFailureKind::ConditionNotLow
                ),
                (
                    "loop_termcond_not_tight",
                    SifTerminationFailureKind::ConditionNotTight
                ),
                (
                    "continue_infinite",
                    SifTerminationFailureKind::LoopPromiseNotKept
                ),
                ("nested", SifTerminationFailureKind::ConditionNotLow),
                ("recursion", SifTerminationFailureKind::CallerUnsatisfied),
                (
                    "test_recursion",
                    SifTerminationFailureKind::CallConditionNotLow
                ),
                ("cycle_1", SifTerminationFailureKind::CallerUnsatisfied),
                ("cycle_2", SifTerminationFailureKind::CallerUnsatisfied),
            ]
        );
    }

    #[test]
    fn unrelated_declassification_cannot_make_a_secret_termination_condition_low() {
        let source = "from nagini_contracts.contracts import *\ndef reveal(secret: int, public: int) -> None:\n    Requires(LowEvent())\n    Declassify(public >= 0)\n    while secret != 0:\n        Invariant(TerminatesSif(secret >= 0, secret))\n        secret -= 1\n";
        let suite = ast::Suite::parse(source, "unrelated_declassify.py").unwrap();
        let analysis = analyze_termination_channels(
            &suite,
            InformationFlowVerificationProfile::SecureInformationFlow,
        )
        .unwrap()
        .unwrap();
        assert_eq!(analysis.failures.len(), 1, "{analysis:#?}");
        assert_eq!(
            analysis.failures[0].kind,
            SifTerminationFailureKind::ConditionNotLow
        );
    }

    #[test]
    fn constant_termination_condition_does_not_manufacture_a_whole_module_proof() {
        let source = "from nagini_contracts.contracts import *\ndef bounded() -> None:\n    i = 2\n    while i != 0:\n        Invariant(TerminatesSif(True, i))\n        i -= 1\n";
        let suite = ast::Suite::parse(source, "bounded.py").unwrap();
        assert!(
            analyze_termination_channels(
                &suite,
                InformationFlowVerificationProfile::SecureInformationFlow,
            )
            .unwrap()
            .is_none(),
            "a passing channel check must fall through to the complete heap verifier"
        );
    }

    #[test]
    fn rebinding_a_declassified_dependency_invalidates_the_predicate() {
        let source = "from nagini_contracts.contracts import *\ndef reveal(secret: int, replacement: int) -> None:\n    Requires(LowEvent())\n    Declassify(secret >= 0)\n    secret = replacement\n    while secret != 0:\n        Invariant(TerminatesSif(secret >= 0, secret))\n        secret -= 1\n";
        let suite = ast::Suite::parse(source, "rebound_declassify.py").unwrap();
        let analysis = analyze_termination_channels(
            &suite,
            InformationFlowVerificationProfile::SecureInformationFlow,
        )
        .unwrap()
        .unwrap();
        assert_eq!(analysis.failures.len(), 1, "{analysis:#?}");
        assert_eq!(
            analysis.failures[0].kind,
            SifTerminationFailureKind::ConditionNotLow
        );
    }

    #[test]
    fn an_unknown_branch_without_a_decrease_refutes_the_loop_promise() {
        let source = "from nagini_contracts.contracts import *\ndef maybe_decrease(flag: bool) -> None:\n    x = 2\n    while x != 0:\n        Invariant(TerminatesSif(True, x))\n        if flag:\n            x -= 1\n";
        let suite = ast::Suite::parse(source, "conditional_decrease.py").unwrap();
        let analysis = analyze_termination_channels(
            &suite,
            InformationFlowVerificationProfile::SecureInformationFlow,
        )
        .unwrap()
        .unwrap();
        assert_eq!(analysis.failures.len(), 1, "{analysis:#?}");
        assert_eq!(
            analysis.failures[0].kind,
            SifTerminationFailureKind::LoopPromiseNotKept
        );
    }

    #[test]
    fn shadowed_termination_primitive_refuses_instead_of_acquiring_contract_semantics() {
        let source = "from nagini_contracts.contracts import *\ndef fake(TerminatesSif: object, secret: int) -> None:\n    while secret != 0:\n        Invariant(TerminatesSif(secret >= 0, secret))\n        secret -= 1\n";
        let suite = ast::Suite::parse(source, "shadowed_termination.py").unwrap();
        let failure = analyze_termination_channels(
            &suite,
            InformationFlowVerificationProfile::SecureInformationFlow,
        )
        .expect_err("shadowed termination primitive must fail closed");
        assert_eq!(failure.code, LOW_UNSUPPORTED);
    }
}
