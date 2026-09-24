//! Path-sensitive leak checking for Nagini invocation and lock-release obligations.
//!
//! This pass is intentionally separate from scalar values and heap permissions. Obligations are
//! linear liveness resources: aliases preserve their object identity, calls transfer resources
//! through declared pre/postconditions, and every control-flow exit must either consume or return
//! the resources it owns.

use std::collections::{BTreeMap, BTreeSet};

use rustpython_parser::ast::Ranged;
use rustpython_parser::{Parse, ast};

use crate::obligation_kernel::{
    CloseDecision, ConsumeDecision, ConsumePolicy, Measure, ProduceDecision, decide_close,
    decide_consume, decide_produce, preserves_loop_invariant,
};
use crate::python_contracts::ContractFailure;
use crate::python_heap_contracts::HeapContractVerification;
use crate::python_obligation_levels::{
    LevelIdentity, LevelIntrinsicEventKind, LevelRequirementContext, LevelRequirementDecision,
    LevelState, ResolvedLevelIntrinsicBindings,
};
use crate::python_verifier_intrinsics::CANONICAL_OBLIGATIONS_MODULE;
use crate::solver::discharge;
use crate::vc::{Obligation, ObligationExpectation, ObligationResult, Term};

const SCHEMA: &str = "maledictus-python-obligation-leaks/v1";

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ObligationKind {
    Invoke,
    Release,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ObligationKey {
    kind: ObligationKind,
    identity: String,
}

#[derive(Clone, Debug)]
struct ObligationSpec {
    kind: ObligationKind,
    root: String,
    fields: Vec<String>,
    measure: Measure,
    conditional: bool,
    bounded: bool,
    offset: u32,
}

#[derive(Clone, Debug)]
struct LevelSpec {
    root: String,
    fields: Vec<String>,
    offset: u32,
}

#[derive(Clone, Debug, Default)]
struct FunctionSummary {
    parameters: Vec<String>,
    lock_parameters: BTreeSet<String>,
    required: Vec<ObligationSpec>,
    returned: Vec<ObligationSpec>,
    required_levels: Vec<LevelSpec>,
    returned_levels: Vec<LevelSpec>,
    terminates: bool,
    termination_measure: Option<Measure>,
    io_token_transform: bool,
    level_intrinsics: ResolvedLevelIntrinsicBindings,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Flow {
    Normal,
    Return,
    Raise(String),
    Break,
    Continue,
    Unreachable,
}

#[derive(Clone, Debug)]
struct LedgerState {
    aliases: BTreeMap<String, String>,
    pending: BTreeMap<ObligationKey, Measure>,
    bounded_identities: BTreeSet<String>,
    lock_identities: BTreeSet<String>,
    flow: Flow,
    termination_required: bool,
    boundary_leak_reported: bool,
    levels: LevelState,
}

impl LedgerState {
    fn add_pending(&mut self, key: ObligationKey, measure: Measure) -> Result<(), ContractFailure> {
        if decide_produce(self.pending.contains_key(&key)) == ProduceDecision::Collision {
            return obligation_failure(
                "frontend.python.obligations.linear-obligation-collision-unsupported",
                "two distinct linear obligations cannot occupy the same kind and object identity",
            );
        }
        self.pending.insert(key, measure);
        Ok(())
    }

    fn identity_of(&self, expression: &ast::Expr) -> Option<String> {
        match expression {
            ast::Expr::Name(name) => self.aliases.get(name.id.as_str()).cloned(),
            ast::Expr::Attribute(attribute) => {
                let mut identity = self.identity_of(&attribute.value)?;
                identity.push('.');
                identity.push_str(attribute.attr.as_str());
                Some(identity)
            }
            _ => None,
        }
    }

    fn unify_names(&mut self, left: &str, right: &str) -> Result<(), ContractFailure> {
        let Some(left_identity) = self.aliases.get(left).cloned() else {
            return Ok(());
        };
        let Some(right_identity) = self.aliases.get(right).cloned() else {
            return Ok(());
        };
        if left_identity == right_identity {
            return Ok(());
        }
        for identity in self.aliases.values_mut() {
            if *identity == right_identity {
                *identity = left_identity.clone();
            }
        }
        if self.bounded_identities.remove(&right_identity) {
            self.bounded_identities.insert(left_identity.clone());
        }
        if self.lock_identities.remove(&right_identity) {
            self.lock_identities.insert(left_identity.clone());
        }
        let moved = self
            .pending
            .iter()
            .filter(|(key, _)| key.identity == right_identity)
            .map(|(key, measure)| (key.clone(), measure.clone()))
            .collect::<Vec<_>>();
        for (old_key, measure) in moved {
            self.pending.remove(&old_key);
            let new_key = ObligationKey {
                kind: old_key.kind,
                identity: left_identity.clone(),
            };
            if self.pending.contains_key(&new_key) {
                self.flow = Flow::Unreachable;
                return Ok(());
            }
            self.pending.insert(new_key, measure);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum DiagnosticKind {
    Caller,
    MethodBody,
    LoopContext,
    LoopBody,
    CallPermission,
    InvariantPermission,
    PostconditionPermission,
    CallLevelOrder,
    InvariantLevelOrder,
    PostconditionLevelOrder,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct PendingDiagnostic {
    kind: DiagnosticKind,
    offset: u32,
    owner: String,
}

struct Analyzer {
    summaries: BTreeMap<String, FunctionSummary>,
    bindings: CanonicalBindings,
    diagnostics: BTreeSet<PendingDiagnostic>,
}

#[derive(Clone, Debug, Default)]
struct CanonicalBindings {
    primitives: BTreeSet<String>,
    lock_classes: BTreeSet<String>,
    lock_fields: BTreeMap<String, BTreeSet<String>>,
    level_intrinsics: ResolvedLevelIntrinsicBindings,
}

#[cfg(test)]
pub(crate) fn verify_obligation_module(
    source: &str,
    path: &str,
) -> Result<Option<HeapContractVerification>, ContractFailure> {
    verify_obligation_module_with_intrinsics(
        source,
        path,
        &ResolvedLevelIntrinsicBindings::default(),
    )
}

pub(crate) fn verify_obligation_module_with_intrinsics(
    source: &str,
    path: &str,
    level_intrinsics: &ResolvedLevelIntrinsicBindings,
) -> Result<Option<HeapContractVerification>, ContractFailure> {
    let suite = ast::Suite::parse(source, path).map_err(|error| ContractFailure {
        code: "frontend.python.parse-error",
        message: error.to_string(),
    })?;
    let mut bindings = canonical_bindings(&suite);
    bindings.level_intrinsics = level_intrinsics.clone();
    invalidate_rebound_level_intrinsics(&suite, &mut bindings.level_intrinsics);
    if bindings.primitives.is_empty() && bindings.level_intrinsics.is_empty() {
        return Ok(None);
    }
    let summaries = collect_function_summaries(&suite, &bindings)?;
    if !summaries.values().any(|summary| {
        !summary.required.is_empty()
            || !summary.returned.is_empty()
            || !summary.required_levels.is_empty()
            || !summary.returned_levels.is_empty()
    }) && !suite_contains_proven_lock_operation(&suite, &summaries, &bindings)
    {
        return Ok(None);
    }

    let mut analyzer = Analyzer {
        summaries,
        bindings,
        diagnostics: BTreeSet::new(),
    };
    analyzer.analyze_overrides(&suite)?;
    let mut methods = Vec::new();
    for statement in &suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                analyzer.analyze_function(function, function.name.as_str())?;
                methods.push(function.name.to_string());
            }
            ast::Stmt::ClassDef(class) => {
                for statement in &class.body {
                    if let ast::Stmt::FunctionDef(function) = statement {
                        // Predicate/passive methods do not own obligations, but keeping them in
                        // the analyzed method list makes the closed source boundary explicit.
                        let owner = format!("{}.{}", class.name, function.name);
                        analyzer.analyze_function(function, &owner)?;
                        methods.push(owner);
                    }
                }
            }
            ast::Stmt::Import(_) | ast::Stmt::ImportFrom(_) => {}
            _ => {}
        }
    }

    let mut obligations = analyzer
        .diagnostics
        .into_iter()
        .map(|diagnostic| {
            let marker = match diagnostic.kind {
                DiagnosticKind::Caller => "obligation-leak:caller",
                DiagnosticKind::MethodBody => "obligation-leak:method-body",
                DiagnosticKind::LoopContext => "obligation-leak:loop-context",
                DiagnosticKind::LoopBody => "obligation-leak:loop-body",
                DiagnosticKind::CallPermission => "obligation-release-precondition",
                DiagnosticKind::InvariantPermission => {
                    "obligation-invariant-preservation-permission"
                }
                DiagnosticKind::PostconditionPermission => "obligation-postcondition-permission",
                DiagnosticKind::CallLevelOrder => "call-precondition",
                DiagnosticKind::InvariantLevelOrder => "obligation-level-invariant",
                DiagnosticKind::PostconditionLevelOrder => "obligation-level-postcondition",
            };
            make_obligation(
                format!("{}:{marker}:{}", diagnostic.owner, diagnostic.offset),
                false,
                source,
                path,
                diagnostic.offset,
            )
        })
        .collect::<Vec<_>>();
    obligations.extend(methods.iter().map(|method| {
        make_obligation(
            format!("{method}:obligation-ledger-closed"),
            true,
            source,
            path,
            0,
        )
    }));
    let obligations = obligations
        .iter()
        .map(|obligation| {
            discharge(obligation).map_err(|message| ContractFailure {
                code: "solver.translation-failed",
                message,
            })
        })
        .collect::<Result<Vec<ObligationResult>, _>>()?;
    let passed = obligations.iter().all(ObligationResult::satisfied);
    Ok(Some(HeapContractVerification {
        schema: SCHEMA.to_owned(),
        path: path.to_owned(),
        methods,
        obligations,
        passed,
    }))
}

fn invalidate_rebound_level_intrinsics(
    suite: &[ast::Stmt],
    bindings: &mut ResolvedLevelIntrinsicBindings,
) {
    let local_names = suite
        .iter()
        .flat_map(top_level_bound_names)
        .collect::<BTreeSet<_>>();
    for local_name in local_names {
        let last_import = suite
            .iter()
            .enumerate()
            .filter_map(|(index, statement)| {
                let ast::Stmt::ImportFrom(import) = statement else {
                    return None;
                };
                if import.level.is_some_and(|level| level != 0_u32)
                    || import
                        .module
                        .as_ref()
                        .is_none_or(|module| module.as_str() != CANONICAL_OBLIGATIONS_MODULE)
                {
                    return None;
                }
                import
                    .names
                    .iter()
                    .any(|alias| {
                        alias.name.as_str() == "*"
                            || alias
                                .asname
                                .as_ref()
                                .map_or(alias.name.as_str(), |name| name.as_str())
                                == local_name
                    })
                    .then_some(index)
            })
            .max();
        let last_rebind = suite
            .iter()
            .enumerate()
            .filter(|(_, statement)| {
                !matches!(statement, ast::Stmt::ImportFrom(_))
                    && top_level_bound_names(statement).contains(&local_name)
            })
            .map(|(index, _)| index)
            .max();
        if last_rebind.is_some_and(|rebind| last_import.is_none_or(|import| rebind > import)) {
            bindings.remove_local_binding(&local_name);
        }
    }
}

impl Analyzer {
    fn analyze_overrides(&mut self, suite: &[ast::Stmt]) -> Result<(), ContractFailure> {
        for statement in suite {
            let ast::Stmt::ClassDef(class) = statement else {
                continue;
            };
            let Some(base) = class.bases.first().and_then(|base| match base {
                ast::Expr::Name(name) => Some(name.id.as_str()),
                _ => None,
            }) else {
                continue;
            };
            for statement in &class.body {
                let ast::Stmt::FunctionDef(function) = statement else {
                    continue;
                };
                let Some(parent) = self
                    .summaries
                    .get(&format!("{base}.{}", function.name))
                    .cloned()
                else {
                    continue;
                };
                let Some(child) = self
                    .summaries
                    .get(&format!("{}.{}", class.name, function.name))
                    .cloned()
                else {
                    continue;
                };
                let offset = u32::from(function.range.start());
                if measure_is_stronger(
                    child.termination_measure.as_ref(),
                    parent.termination_measure.as_ref(),
                )? {
                    self.record(
                        DiagnosticKind::Caller,
                        offset,
                        &format!("{}.{}", class.name, function.name),
                    );
                }
                if release_precondition_is_stronger(&child, &parent)? {
                    self.record(
                        DiagnosticKind::CallPermission,
                        offset,
                        &format!("{}.{}", class.name, function.name),
                    );
                }
            }
        }
        Ok(())
    }

    fn analyze_function(
        &mut self,
        function: &ast::StmtFunctionDef,
        owner: &str,
    ) -> Result<(), ContractFailure> {
        let Some(summary) = self.summaries.get(owner).cloned() else {
            return Ok(());
        };
        let mut aliases = BTreeMap::new();
        let mut lock_identities = BTreeSet::new();
        for parameter in &summary.parameters {
            let identity = format!("{owner}::{parameter}");
            if summary.lock_parameters.contains(parameter) {
                lock_identities.insert(identity.clone());
            }
            aliases.insert(parameter.clone(), identity);
        }
        if let Some((class, _)) = owner.split_once('.')
            && let Some(self_identity) = aliases.get("self")
            && let Some(fields) = self.bindings.lock_fields.get(class)
        {
            lock_identities.extend(
                fields
                    .iter()
                    .map(|field| format!("{self_identity}.{field}")),
            );
        }
        let mut state = LedgerState {
            aliases,
            pending: BTreeMap::new(),
            bounded_identities: BTreeSet::new(),
            lock_identities,
            flow: Flow::Normal,
            termination_required: summary.terminates,
            boundary_leak_reported: false,
            levels: LevelState::default(),
        };
        apply_required_equalities(function, &mut state)?;
        for required in &summary.required {
            if required.conditional {
                continue;
            }
            let Some(identity) = instantiate_spec_identity(required, &summary, &[], &state) else {
                continue;
            };
            let key = ObligationKey {
                kind: required.kind.clone(),
                identity,
            };
            if state.pending.contains_key(&key) {
                state.flow = Flow::Unreachable;
                break;
            }
            state.pending.insert(key, required.measure.clone());
        }
        for required in &summary.required_levels {
            if let Some(identity) = instantiate_level_identity(required, &summary, &[], &state) {
                state.levels.assert_current_below(identity);
            }
        }
        let executable = function
            .body
            .iter()
            .filter(|statement| !is_contract_statement(statement))
            .cloned()
            .collect::<Vec<_>>();
        let states = self.execute_block(vec![state], &executable, owner)?;
        let method_offset = u32::from(function.range.start());
        for mut state in states {
            if state.flow == Flow::Unreachable {
                continue;
            }
            for returned in &summary.returned {
                if returned.conditional {
                    continue;
                }
                if let Some(identity) = instantiate_spec_identity(returned, &summary, &[], &state) {
                    let key = ObligationKey {
                        kind: returned.kind.clone(),
                        identity: identity.clone(),
                    };
                    let decision = decide_consume(
                        state.pending.get(&key),
                        &returned.measure,
                        state.bounded_identities.contains(&identity),
                        ConsumePolicy::UnboundedRequiresUnboundedOwner,
                    );
                    if decision == ConsumeDecision::Consume {
                        state.pending.remove(&key);
                    } else {
                        self.record(
                            DiagnosticKind::PostconditionPermission,
                            returned.offset,
                            owner,
                        );
                        state.boundary_leak_reported = true;
                    }
                }
            }
            for returned in &summary.returned_levels {
                let satisfied = instantiate_level_identity(returned, &summary, &[], &state)
                    .is_some_and(|identity| {
                        state.levels.require_current_below(
                            &identity,
                            LevelRequirementContext::FunctionPostcondition,
                        ) == LevelRequirementDecision::Satisfied
                    });
                if !satisfied {
                    self.record(
                        DiagnosticKind::PostconditionLevelOrder,
                        returned.offset,
                        owner,
                    );
                }
            }
            if decide_close(!state.pending.is_empty(), state.boundary_leak_reported)
                == CloseDecision::ReportLeak
            {
                self.record(DiagnosticKind::MethodBody, method_offset, owner);
            }
        }
        Ok(())
    }

    fn execute_block(
        &mut self,
        mut states: Vec<LedgerState>,
        statements: &[ast::Stmt],
        owner: &str,
    ) -> Result<Vec<LedgerState>, ContractFailure> {
        for statement in statements {
            let mut next = Vec::new();
            for state in states {
                if state.flow != Flow::Normal {
                    next.push(state);
                    continue;
                }
                next.extend(self.execute_statement(state, statement, owner)?);
            }
            states = next;
        }
        Ok(states)
    }

    fn execute_statement(
        &mut self,
        mut state: LedgerState,
        statement: &ast::Stmt,
        owner: &str,
    ) -> Result<Vec<LedgerState>, ContractFailure> {
        match statement {
            ast::Stmt::Pass(_) | ast::Stmt::Import(_) | ast::Stmt::ImportFrom(_) => Ok(vec![state]),
            ast::Stmt::Assign(assignment) => {
                if let ast::Expr::Call(call) = assignment.value.as_ref()
                    && direct_call_name(call)
                        .is_none_or(|name| !is_constructor_name(name) && name != "object")
                {
                    self.apply_call(
                        &mut state,
                        call,
                        owner,
                        u32::from(statement.range().start()),
                    )?;
                }
                let assigns_canonical_lock = matches!(assignment.value.as_ref(), ast::Expr::Call(call)
                        if direct_call_name(call)
                            .is_some_and(|name| self.bindings.lock_classes.contains(name)));
                for target in &assignment.targets {
                    if let ast::Expr::Attribute(_) = target
                        && let Some(identity) = state.identity_of(target)
                    {
                        let level_identity = LevelState::certify_resolved_object(identity.clone());
                        if assigns_canonical_lock {
                            state.lock_identities.insert(identity);
                            state.levels.assert_current_below(level_identity);
                        } else {
                            state.lock_identities.remove(&identity);
                            state.levels.forget_identity(&level_identity);
                        }
                    }
                }
                if let [ast::Expr::Name(target)] = assignment.targets.as_slice() {
                    if let Some(identity) = state.identity_of(&assignment.value) {
                        state.aliases.insert(target.id.to_string(), identity);
                    } else if matches!(assignment.value.as_ref(), ast::Expr::Call(call)
                        if direct_call_name(call).is_some_and(is_constructor_name))
                    {
                        let identity = format!(
                            "{owner}::{}@{}",
                            target.id,
                            u32::from(statement.range().start())
                        );
                        if matches!(assignment.value.as_ref(), ast::Expr::Call(call)
                            if direct_call_name(call).is_some_and(|name| self.bindings.lock_classes.contains(name)))
                        {
                            state.lock_identities.insert(identity.clone());
                            state
                                .levels
                                .assert_current_below(LevelState::certify_resolved_object(
                                    identity.clone(),
                                ));
                        }
                        state.aliases.insert(target.id.to_string(), identity);
                    } else {
                        if let Some(identity) = state.aliases.remove(target.id.as_str()) {
                            state.lock_identities.remove(&identity);
                            state
                                .levels
                                .forget_identity(&LevelState::certify_resolved_object(identity));
                        }
                    }
                } else if !assignment.targets.iter().all(|target| {
                    matches!(target, ast::Expr::Attribute(_) | ast::Expr::Subscript(_))
                }) {
                    return unsupported_dynamic_identity(statement);
                }
                Ok(vec![state])
            }
            ast::Stmt::AnnAssign(assignment) => {
                if let ast::Expr::Name(target) = assignment.target.as_ref()
                    && let Some(value) = assignment.value.as_deref()
                {
                    if let ast::Expr::Call(call) = value {
                        self.apply_call(
                            &mut state,
                            call,
                            owner,
                            u32::from(statement.range().start()),
                        )?;
                    }
                    if let Some(identity) = state.identity_of(value) {
                        state.aliases.insert(target.id.to_string(), identity);
                    }
                }
                Ok(vec![state])
            }
            ast::Stmt::AugAssign(_) => Ok(vec![state]),
            ast::Stmt::Expr(expression) => {
                if is_contract_statement(statement) {
                    return Ok(vec![state]);
                }
                let ast::Expr::Call(call) = expression.value.as_ref() else {
                    return Ok(vec![state]);
                };
                if direct_call_name(call).is_some_and(|name| name == "Assert")
                    && matches!(call.args.as_slice(), [ast::Expr::Constant(constant)]
                        if constant.value == ast::Constant::Bool(false))
                {
                    state.flow = Flow::Unreachable;
                    return Ok(vec![state]);
                }
                self.apply_call(
                    &mut state,
                    call,
                    owner,
                    u32::from(statement.range().start()),
                )?;
                Ok(vec![state])
            }
            ast::Stmt::If(branch) => {
                if matches!(branch.test.as_ref(), ast::Expr::Constant(constant)
                    if constant.value == ast::Constant::Bool(true))
                {
                    return self.execute_block(vec![state], &branch.body, owner);
                }
                if matches!(branch.test.as_ref(), ast::Expr::Constant(constant)
                    if constant.value == ast::Constant::Bool(false))
                {
                    return self.execute_block(vec![state], &branch.orelse, owner);
                }
                let mut truthy = state.clone();
                refine_identity_condition(&branch.test, true, &mut truthy)?;
                let mut falsy = state;
                refine_identity_condition(&branch.test, false, &mut falsy)?;
                let mut paths = self.execute_block(vec![truthy], &branch.body, owner)?;
                paths.extend(self.execute_block(vec![falsy], &branch.orelse, owner)?);
                Ok(paths)
            }
            ast::Stmt::While(loop_) => self.execute_loop(
                state,
                Some(&loop_.test),
                &loop_.body,
                u32::from(statement.range().start()),
                owner,
            ),
            ast::Stmt::For(loop_) => self.execute_loop(
                state,
                None,
                &loop_.body,
                u32::from(statement.range().start()),
                owner,
            ),
            ast::Stmt::Return(_) => {
                state.flow = Flow::Return;
                Ok(vec![state])
            }
            ast::Stmt::Raise(raised) => {
                state.flow = Flow::Raise(
                    raised
                        .exc
                        .as_deref()
                        .and_then(exception_name)
                        .unwrap_or("BaseException")
                        .to_owned(),
                );
                Ok(vec![state])
            }
            ast::Stmt::Break(_) => {
                state.flow = Flow::Break;
                Ok(vec![state])
            }
            ast::Stmt::Continue(_) => {
                state.flow = Flow::Continue;
                Ok(vec![state])
            }
            ast::Stmt::Try(try_) => self.execute_try(state, try_, owner),
            ast::Stmt::Assert(assertion) => {
                if matches!(assertion.test.as_ref(), ast::Expr::Constant(constant)
                    if constant.value == ast::Constant::Bool(false))
                {
                    state.flow = Flow::Unreachable;
                }
                Ok(vec![state])
            }
            _ if state.pending.is_empty() => Ok(vec![state]),
            _ => unsupported_dynamic_identity(statement),
        }
    }

    fn execute_loop(
        &mut self,
        mut state: LedgerState,
        test: Option<&ast::Expr>,
        body: &[ast::Stmt],
        loop_offset: u32,
        owner: &str,
    ) -> Result<Vec<LedgerState>, ContractFailure> {
        let invariant_count = body
            .iter()
            .take_while(|item| invariant_argument(item).is_some())
            .count();
        let invariants = &body[..invariant_count];
        let executable = &body[invariant_count..];
        let has_termination_invariant = invariants.iter().any(|invariant| {
            self.bindings.primitives.contains("MustTerminate")
                && invariant_argument(invariant)
                    .is_some_and(|argument| expression_contains_call(argument, "MustTerminate"))
        });
        let mut has_conditional_obligation_invariant = false;
        let mut has_any_obligation_invariant = false;
        let loop_is_unreachable = test.is_some_and(expression_is_statically_false);
        let recreates_obligation = block_recreates_obligation(executable, owner, &self.summaries);
        let mut conditional_exit_keys = Vec::new();
        let mut release_invariants = Vec::new();
        let mut level_invariants = Vec::new();
        let owner_summary = self.summaries.get(owner).cloned().unwrap_or_default();
        for invariant in invariants {
            let argument = invariant_argument(invariant).expect("invariant prefix");
            for level in collect_level_specs(argument, &owner_summary.level_intrinsics)? {
                let offset = u32::from(invariant.range().start());
                let Some(identity) =
                    instantiate_level_identity(&level, &owner_summary, &[], &state)
                else {
                    self.record(DiagnosticKind::InvariantLevelOrder, offset, owner);
                    continue;
                };
                if state
                    .levels
                    .require_current_below(&identity, LevelRequirementContext::LoopInvariantEntry)
                    != LevelRequirementDecision::Satisfied
                {
                    self.record(DiagnosticKind::InvariantLevelOrder, offset, owner);
                }
                state.levels.assert_current_below(identity);
                level_invariants.push((level, offset));
            }
            let clauses = collect_obligation_specs(argument, true, &self.bindings.primitives)?;
            has_any_obligation_invariant |= !clauses.is_empty();
            let progresses = obligation_measure_progresses(argument, executable);
            for clause in &clauses {
                if let Some(identity) = instantiate_state_spec_identity(clause, &state) {
                    if clause.bounded {
                        state.bounded_identities.insert(identity.clone());
                    }
                    if !clause.conditional && !progresses {
                        let key = ObligationKey {
                            kind: clause.kind.clone(),
                            identity: identity.clone(),
                        };
                        if state.pending.contains_key(&key) {
                            state.pending.insert(key, clause.measure.clone());
                        }
                    }
                    if clause.conditional {
                        conditional_exit_keys.push(ObligationKey {
                            kind: clause.kind.clone(),
                            identity,
                        });
                    }
                }
                if clause.kind == ObligationKind::Release && !clause.conditional {
                    release_invariants.push((
                        clause.clone(),
                        u32::from(invariant.range().start()),
                        progresses,
                    ));
                }
            }
            if clauses.iter().any(|clause| clause.conditional) && !progresses {
                has_conditional_obligation_invariant = true;
            }
            if !clauses.is_empty()
                && !has_termination_invariant
                && !loop_is_unreachable
                && !progresses
                && !recreates_obligation
            {
                self.record(
                    DiagnosticKind::InvariantPermission,
                    u32::from(invariant.range().start()),
                    owner,
                );
                state.boundary_leak_reported = true;
            }
        }
        if !state.pending.is_empty() && !has_termination_invariant && !has_any_obligation_invariant
        {
            self.record(DiagnosticKind::LoopContext, loop_offset, owner);
            state.boundary_leak_reported = true;
        }
        if !state.pending.is_empty() && has_conditional_obligation_invariant {
            self.record(DiagnosticKind::LoopBody, loop_offset, owner);
            state.boundary_leak_reported = true;
        }

        let body_paths = self.execute_block(vec![state.clone()], executable, owner)?;
        for (invariant, offset) in &level_invariants {
            let is_not_preserved = body_paths
                .iter()
                .filter(|path| matches!(path.flow, Flow::Normal | Flow::Continue))
                .any(|path| {
                    instantiate_level_identity(invariant, &owner_summary, &[], path).is_none_or(
                        |identity| {
                            path.levels.require_current_below(
                                &identity,
                                LevelRequirementContext::LoopInvariantPreservation,
                            ) != LevelRequirementDecision::Satisfied
                        },
                    )
                });
            if is_not_preserved && !loop_is_unreachable {
                self.record(DiagnosticKind::InvariantLevelOrder, *offset, owner);
            }
        }
        for (invariant, offset, progresses) in &release_invariants {
            if !recreates_obligation || *progresses {
                continue;
            }
            let Some(identity) = instantiate_state_spec_identity(invariant, &state) else {
                continue;
            };
            let key = ObligationKey {
                kind: invariant.kind.clone(),
                identity: identity.clone(),
            };
            let is_not_preserved = body_paths
                .iter()
                .filter(|path| matches!(path.flow, Flow::Normal | Flow::Continue))
                .any(|path| !preserves_loop_invariant(path.pending.get(&key), &invariant.measure));
            if is_not_preserved && !loop_is_unreachable {
                self.record(DiagnosticKind::InvariantPermission, *offset, owner);
            }
        }
        let mut exit_state = state;
        for key in conditional_exit_keys {
            exit_state.pending.remove(&key);
            exit_state.bounded_identities.remove(&key.identity);
        }
        // A statically true `while` has no ordinary zero-iteration or condition-false exit.
        // Abrupt paths from its body are still retained below.
        let mut results = if test.is_some_and(expression_is_statically_true) {
            Vec::new()
        } else {
            vec![exit_state]
        };
        for mut path in body_paths {
            match path.flow {
                Flow::Break => {
                    path.flow = Flow::Normal;
                    results.push(path);
                }
                Flow::Return | Flow::Raise(_) | Flow::Unreachable => results.push(path),
                Flow::Normal | Flow::Continue => {}
            }
        }
        Ok(results)
    }

    fn execute_try(
        &mut self,
        state: LedgerState,
        try_: &ast::StmtTry,
        owner: &str,
    ) -> Result<Vec<LedgerState>, ContractFailure> {
        let body_paths = self.execute_block(vec![state], &try_.body, owner)?;
        let mut handled = Vec::new();
        for mut path in body_paths {
            match &path.flow {
                Flow::Normal => {
                    handled.extend(self.execute_block(vec![path], &try_.orelse, owner)?);
                }
                Flow::Raise(exception) => {
                    let handler = try_.handlers.iter().find(|handler| {
                        let ast::ExceptHandler::ExceptHandler(handler) = handler;
                        handler.type_.as_deref().is_none_or(|type_| {
                            exception_name(type_).is_some_and(|caught| {
                                caught == exception
                                    || caught == "Exception"
                                    || caught == "BaseException"
                            })
                        })
                    });
                    if let Some(ast::ExceptHandler::ExceptHandler(handler)) = handler {
                        path.flow = Flow::Normal;
                        handled.extend(self.execute_block(vec![path], &handler.body, owner)?);
                    } else {
                        handled.push(path);
                    }
                }
                _ => handled.push(path),
            }
        }
        if try_.finalbody.is_empty() {
            return Ok(handled);
        }
        let mut finalized = Vec::new();
        for mut path in handled {
            let prior_flow = path.flow.clone();
            path.flow = Flow::Normal;
            for mut final_path in self.execute_block(vec![path], &try_.finalbody, owner)? {
                if final_path.flow == Flow::Normal {
                    final_path.flow = prior_flow.clone();
                }
                finalized.push(final_path);
            }
        }
        Ok(finalized)
    }

    fn apply_call(
        &mut self,
        state: &mut LedgerState,
        call: &ast::ExprCall,
        owner: &str,
        offset: u32,
    ) -> Result<(), ContractFailure> {
        if let ast::Expr::Attribute(attribute) = call.func.as_ref()
            && matches!(attribute.attr.as_str(), "release" | "acquire")
            && let Some(identity) = state.identity_of(&attribute.value)
            && state.lock_identities.contains(&identity)
        {
            let level_identity = LevelState::certify_resolved_object(identity.clone());
            if attribute.attr.as_str() == "acquire" {
                if state.levels.acquire(&level_identity) != LevelRequirementDecision::Satisfied {
                    self.record(DiagnosticKind::CallLevelOrder, offset, owner);
                }
                state.add_pending(
                    ObligationKey {
                        kind: ObligationKind::Release,
                        identity,
                    },
                    Measure::Unbounded,
                )?;
                return Ok(());
            }
            let key = ObligationKey {
                kind: ObligationKind::Release,
                identity: identity.clone(),
            };
            if decide_consume(
                state.pending.get(&key),
                &Measure::Known(1),
                state.bounded_identities.contains(&identity),
                ConsumePolicy::AnySufficient,
            ) == ConsumeDecision::Consume
            {
                state.pending.remove(&key);
                state.bounded_identities.remove(&identity);
            } else {
                self.record(DiagnosticKind::CallPermission, offset, owner);
                if state
                    .pending
                    .keys()
                    .any(|pending| pending.identity == identity)
                {
                    state.boundary_leak_reported = true;
                }
            }
            return Ok(());
        }
        let Some(called) = resolved_call_name(call, owner, &self.summaries) else {
            if state.pending.is_empty() {
                return Ok(());
            }
            return dynamic_call_identity("indirect callable");
        };
        if is_runtime_contract_name(&called, &self.bindings.primitives) {
            return Ok(());
        }
        let Some(summary) = self.summaries.get(&called).cloned() else {
            if !state.pending.is_empty() || state.levels.has_order_evidence() {
                self.record(DiagnosticKind::Caller, offset, owner);
                state.boundary_leak_reported = true;
            }
            return Ok(());
        };

        // A source-declared ContractOnly IO operation transfers the invocation token to its
        // returned place. The loop proof only needs the linear-token conservation fact here; the
        // IO frontend owns the predicate opening and result-place equality proof.
        if summary.io_token_transform {
            return Ok(());
        }

        for required in &summary.required_levels {
            let satisfied = instantiate_call_level_identity(required, &summary, call, state)
                .is_some_and(|identity| {
                    state
                        .levels
                        .require_current_below(&identity, LevelRequirementContext::CallPrecondition)
                        == LevelRequirementDecision::Satisfied
                });
            if !satisfied {
                self.record(DiagnosticKind::CallLevelOrder, offset, owner);
            }
        }
        for required in &summary.required {
            if required.conditional {
                continue;
            }
            let Some(identity) = instantiate_call_spec_identity(required, &summary, call, state)
            else {
                return dynamic_call_identity(&called);
            };
            let key = ObligationKey {
                kind: required.kind.clone(),
                identity: identity.clone(),
            };
            if decide_consume(
                state.pending.get(&key),
                &required.measure,
                state.bounded_identities.contains(&identity),
                ConsumePolicy::PositiveCountdownTransfer,
            ) == ConsumeDecision::Consume
            {
                state.pending.remove(&key);
                state.bounded_identities.remove(&identity);
            } else {
                self.record(DiagnosticKind::CallPermission, offset, owner);
                if state
                    .pending
                    .keys()
                    .any(|pending| pending.identity == identity)
                {
                    state.boundary_leak_reported = true;
                }
            }
        }
        if (!state.pending.is_empty() || state.termination_required) && !summary.terminates {
            self.record(DiagnosticKind::Caller, offset, owner);
            state.boundary_leak_reported = true;
        }
        for returned in &summary.returned {
            if returned.conditional {
                continue;
            }
            if let Some(identity) = instantiate_call_spec_identity(returned, &summary, call, state)
            {
                state.add_pending(
                    ObligationKey {
                        kind: returned.kind.clone(),
                        identity: identity.clone(),
                    },
                    returned.measure.clone(),
                )?;
                if returned.bounded {
                    state.bounded_identities.insert(identity);
                }
            }
        }
        for returned in &summary.returned_levels {
            if let Some(identity) = instantiate_call_level_identity(returned, &summary, call, state)
            {
                state.levels.assert_current_below(identity);
            }
        }
        Ok(())
    }

    fn record(&mut self, kind: DiagnosticKind, offset: u32, owner: &str) {
        self.diagnostics.insert(PendingDiagnostic {
            kind,
            offset,
            owner: owner.to_owned(),
        });
    }
}

fn canonical_bindings(suite: &[ast::Stmt]) -> CanonicalBindings {
    let mut bindings = CanonicalBindings::default();
    for statement in suite {
        if let ast::Stmt::ImportFrom(import) = statement
            && import.level.is_none_or(|level| level == 0_u32)
            && let Some(module) = import.module.as_ref()
        {
            let exported: &[&str] = match module.as_str() {
                "nagini_contracts.obligations" => &["MustRelease", "MustTerminate"],
                "nagini_contracts.io_contracts" => &["token", "Open"],
                "nagini_contracts.lock" => &["Lock"],
                _ => &[],
            };
            for alias in &import.names {
                if alias.name.as_str() == "*" {
                    for name in exported {
                        if *name == "Lock" {
                            bindings.lock_classes.insert((*name).to_owned());
                        } else {
                            bindings.primitives.insert((*name).to_owned());
                        }
                    }
                } else if alias.asname.is_none() && exported.contains(&alias.name.as_str()) {
                    if alias.name.as_str() == "Lock" {
                        bindings.lock_classes.insert(alias.name.to_string());
                    } else {
                        bindings.primitives.insert(alias.name.to_string());
                    }
                }
            }
            continue;
        }
        for name in top_level_bound_names(statement) {
            bindings.primitives.remove(name.as_str());
            bindings.lock_classes.remove(name.as_str());
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for statement in suite {
            let ast::Stmt::ClassDef(class) = statement else {
                continue;
            };
            if class
                .bases
                .iter()
                .any(|base| annotation_names_lock_class(base, &bindings.lock_classes))
                && bindings.lock_classes.insert(class.name.to_string())
            {
                changed = true;
            }
        }
    }
    for statement in suite {
        let ast::Stmt::ClassDef(class) = statement else {
            continue;
        };
        let fields = class_lock_fields(class, &bindings.lock_classes);
        if !fields.is_empty() {
            bindings.lock_fields.insert(class.name.to_string(), fields);
        }
    }
    bindings
}

fn top_level_bound_names(statement: &ast::Stmt) -> Vec<String> {
    match statement {
        ast::Stmt::FunctionDef(function) => vec![function.name.to_string()],
        ast::Stmt::ClassDef(class) => vec![class.name.to_string()],
        ast::Stmt::Assign(assignment) => assignment
            .targets
            .iter()
            .filter_map(|target| match target {
                ast::Expr::Name(name) => Some(name.id.to_string()),
                _ => None,
            })
            .collect(),
        ast::Stmt::AnnAssign(assignment) => match assignment.target.as_ref() {
            ast::Expr::Name(name) => vec![name.id.to_string()],
            _ => Vec::new(),
        },
        ast::Stmt::AugAssign(assignment) => match assignment.target.as_ref() {
            ast::Expr::Name(name) => vec![name.id.to_string()],
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

fn annotation_names_lock_class(annotation: &ast::Expr, lock_classes: &BTreeSet<String>) -> bool {
    match annotation {
        ast::Expr::Name(name) => lock_classes.contains(name.id.as_str()),
        ast::Expr::Subscript(subscript) => {
            annotation_names_lock_class(&subscript.value, lock_classes)
                || annotation_names_lock_class(&subscript.slice, lock_classes)
        }
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Str(value) => type_text_names_lock_class(value, lock_classes),
            _ => false,
        },
        _ => false,
    }
}

fn type_text_names_lock_class(text: &str, lock_classes: &BTreeSet<String>) -> bool {
    let text = text.trim();
    if lock_classes.contains(text) {
        return true;
    }
    for wrapper in ["Optional", "Union"] {
        if let Some(inner) = text
            .strip_prefix(wrapper)
            .and_then(|rest| rest.strip_prefix('['))
            .and_then(|rest| rest.strip_suffix(']'))
            && inner
                .split(',')
                .any(|part| type_text_names_lock_class(part, lock_classes))
        {
            return true;
        }
    }
    false
}

fn class_lock_fields(
    class: &ast::StmtClassDef,
    lock_classes: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut fields = BTreeSet::new();
    for statement in &class.body {
        match statement {
            ast::Stmt::AnnAssign(assignment) => {
                if let ast::Expr::Name(name) = assignment.target.as_ref()
                    && annotation_names_lock_class(&assignment.annotation, lock_classes)
                {
                    fields.insert(name.id.to_string());
                }
            }
            ast::Stmt::FunctionDef(function) if function.name.as_str() == "__init__" => {
                for statement in &function.body {
                    match statement {
                        ast::Stmt::AnnAssign(assignment)
                            if annotation_names_lock_class(
                                &assignment.annotation,
                                lock_classes,
                            ) =>
                        {
                            if let ast::Expr::Attribute(attribute) = assignment.target.as_ref()
                                && matches!(attribute.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "self")
                            {
                                fields.insert(attribute.attr.to_string());
                            }
                        }
                        ast::Stmt::Assign(assignment)
                            if assignment.type_comment.as_deref().is_some_and(|comment| {
                                type_text_names_lock_class(comment, lock_classes)
                            }) =>
                        {
                            for target in &assignment.targets {
                                if let ast::Expr::Attribute(attribute) = target
                                    && matches!(attribute.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "self")
                                {
                                    fields.insert(attribute.attr.to_string());
                                }
                            }
                        }
                        ast::Stmt::Assign(assignment) => {
                            let assigns_canonical_lock = matches!(assignment.value.as_ref(), ast::Expr::Call(call)
                                    if direct_call_name(call)
                                        .is_some_and(|name| lock_classes.contains(name)));
                            for target in &assignment.targets {
                                if let ast::Expr::Attribute(attribute) = target
                                    && matches!(attribute.value.as_ref(), ast::Expr::Name(name)
                                        if name.id.as_str() == "self")
                                {
                                    if assigns_canonical_lock {
                                        fields.insert(attribute.attr.to_string());
                                    } else {
                                        fields.remove(attribute.attr.as_str());
                                    }
                                }
                            }
                        }
                        ast::Stmt::AugAssign(assignment) => {
                            if let ast::Expr::Attribute(attribute) = assignment.target.as_ref()
                                && matches!(attribute.value.as_ref(), ast::Expr::Name(name)
                                    if name.id.as_str() == "self")
                            {
                                fields.remove(attribute.attr.as_str());
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    fields
}

fn function_local_bound_names(function: &ast::StmtFunctionDef) -> BTreeSet<String> {
    let mut names = function
        .args
        .posonlyargs
        .iter()
        .chain(&function.args.args)
        .chain(&function.args.kwonlyargs)
        .map(|argument| argument.def.arg.to_string())
        .collect::<BTreeSet<_>>();
    fn collect(statements: &[ast::Stmt], names: &mut BTreeSet<String>) {
        for statement in statements {
            match statement {
                ast::Stmt::Assign(assignment) => {
                    for target in &assignment.targets {
                        if let ast::Expr::Name(name) = target {
                            names.insert(name.id.to_string());
                        }
                    }
                }
                ast::Stmt::AnnAssign(assignment) => {
                    if let ast::Expr::Name(name) = assignment.target.as_ref() {
                        names.insert(name.id.to_string());
                    }
                }
                ast::Stmt::If(branch) => {
                    collect(&branch.body, names);
                    collect(&branch.orelse, names);
                }
                ast::Stmt::While(loop_) => {
                    collect(&loop_.body, names);
                    collect(&loop_.orelse, names);
                }
                ast::Stmt::For(loop_) => {
                    collect(&loop_.body, names);
                    collect(&loop_.orelse, names);
                }
                ast::Stmt::Try(try_) => {
                    collect(&try_.body, names);
                    collect(&try_.orelse, names);
                    collect(&try_.finalbody, names);
                }
                _ => {}
            }
        }
    }
    collect(&function.body, &mut names);
    names
}

fn collect_function_summaries(
    suite: &[ast::Stmt],
    bindings: &CanonicalBindings,
) -> Result<BTreeMap<String, FunctionSummary>, ContractFailure> {
    let mut summaries = BTreeMap::new();
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                summaries.insert(
                    function.name.to_string(),
                    summarize_function(function, bindings)?,
                );
            }
            ast::Stmt::ClassDef(class) => {
                for statement in &class.body {
                    if let ast::Stmt::FunctionDef(function) = statement {
                        summaries.insert(
                            format!("{}.{}", class.name, function.name),
                            summarize_function(function, bindings)?,
                        );
                    }
                }
            }
            _ => {}
        }
    }
    Ok(summaries)
}

fn summarize_function(
    function: &ast::StmtFunctionDef,
    bindings: &CanonicalBindings,
) -> Result<FunctionSummary, ContractFailure> {
    let parameters = function
        .args
        .posonlyargs
        .iter()
        .chain(&function.args.args)
        .chain(&function.args.kwonlyargs)
        .map(|argument| argument.def.arg.to_string())
        .collect::<Vec<_>>();
    let mut summary = FunctionSummary {
        parameters,
        lock_parameters: function
            .args
            .posonlyargs
            .iter()
            .chain(&function.args.args)
            .chain(&function.args.kwonlyargs)
            .filter(|argument| {
                argument
                    .def
                    .annotation
                    .as_deref()
                    .is_some_and(|annotation| {
                        annotation_names_lock_class(annotation, &bindings.lock_classes)
                    })
            })
            .map(|argument| argument.def.arg.to_string())
            .collect(),
        ..FunctionSummary::default()
    };
    summary.io_token_transform = function.body.iter().any(|statement| {
        let ast::Stmt::Expr(expression) = statement else {
            return false;
        };
        let value = expression.value.as_ref();
        expression_contains_call(value, "IOExists1")
            && expression_contains_call(value, "Requires")
            && expression_contains_call(value, "Ensures")
            && expression_contains_call(value, "token")
            && expression_contains_call(value, "Result")
    });
    let mut primitives = bindings.primitives.clone();
    let mut level_intrinsics = bindings.level_intrinsics.clone();
    for local in function_local_bound_names(function) {
        primitives.remove(local.as_str());
        level_intrinsics.remove_local_binding(local.as_str());
    }
    summary.level_intrinsics = level_intrinsics.clone();
    for statement in &function.body {
        let Some((contract_name, argument)) = contract_statement(statement) else {
            continue;
        };
        match contract_name {
            "Requires" => {
                summary.terminates |= primitives.contains("MustTerminate")
                    && expression_contains_call(argument, "MustTerminate");
                for measure in collect_named_call_measures(argument, "MustTerminate", &primitives) {
                    summary.termination_measure =
                        stronger_measure(summary.termination_measure.take(), Some(measure))?;
                }
                summary
                    .required
                    .extend(collect_obligation_specs(argument, false, &primitives)?);
                summary
                    .required_levels
                    .extend(collect_level_specs(argument, &level_intrinsics)?);
            }
            "Ensures" => {
                summary
                    .returned
                    .extend(collect_obligation_specs(argument, false, &primitives)?);
                summary
                    .returned_levels
                    .extend(collect_level_specs(argument, &level_intrinsics)?);
            }
            _ => {}
        }
    }
    Ok(summary)
}

fn collect_named_call_measures(
    expression: &ast::Expr,
    expected: &str,
    primitives: &BTreeSet<String>,
) -> Vec<Measure> {
    if !primitives.contains(expected) {
        return Vec::new();
    }
    match expression {
        ast::Expr::BoolOp(operation) if operation.op == ast::BoolOp::And => operation
            .values
            .iter()
            .flat_map(|value| collect_named_call_measures(value, expected, primitives))
            .collect(),
        ast::Expr::Call(call) if direct_call_name(call).is_some_and(|name| name == expected) => {
            call.args.first().map(measure_of).into_iter().collect()
        }
        ast::Expr::Call(call) if direct_call_name(call).is_some_and(|name| name == "Implies") => {
            call.args
                .get(1)
                .map(|value| collect_named_call_measures(value, expected, primitives))
                .unwrap_or_default()
        }
        _ => Vec::new(),
    }
}

fn stronger_measure(
    left: Option<Measure>,
    right: Option<Measure>,
) -> Result<Option<Measure>, ContractFailure> {
    match (left, right) {
        (None, right) => Ok(right),
        (left, None) => Ok(left),
        (Some(Measure::Known(left)), Some(Measure::Known(right))) => {
            Ok(Some(Measure::Known(left.max(right))))
        }
        (Some(Measure::Unknown(left)), Some(Measure::Unknown(right))) if left == right => {
            Ok(Some(Measure::Unknown(left)))
        }
        _ => obligation_failure(
            "frontend.python.obligations.dynamic-measure-order-unsupported",
            "obligation precondition ordering requires statically comparable measures",
        ),
    }
}

fn measure_is_stronger(
    child: Option<&Measure>,
    parent: Option<&Measure>,
) -> Result<bool, ContractFailure> {
    match (child, parent) {
        (None, _) => Ok(false),
        (Some(_), None) => Ok(true),
        (Some(Measure::Known(child)), Some(Measure::Known(parent))) => Ok(child > parent),
        (Some(Measure::Unknown(child)), Some(Measure::Unknown(parent))) if child == parent => {
            Ok(false)
        }
        _ => obligation_failure(
            "frontend.python.obligations.dynamic-measure-order-unsupported",
            "obligation override ordering requires statically comparable measures",
        ),
    }
}

fn release_precondition_is_stronger(
    child: &FunctionSummary,
    parent: &FunctionSummary,
) -> Result<bool, ContractFailure> {
    for child_spec in child
        .required
        .iter()
        .filter(|spec| spec.kind == ObligationKind::Release && !spec.conditional)
    {
        let child_parameter = child
            .parameters
            .iter()
            .position(|parameter| parameter == &child_spec.root);
        let parent_measure = parent.required.iter().find(|parent_spec| {
            parent_spec.kind == ObligationKind::Release
                && !parent_spec.conditional
                && parent_spec.fields == child_spec.fields
                && parent
                    .parameters
                    .iter()
                    .position(|parameter| parameter == &parent_spec.root)
                    == child_parameter
        });
        if measure_is_stronger(
            Some(&child_spec.measure),
            parent_measure.map(|spec| &spec.measure),
        )? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn contract_statement(statement: &ast::Stmt) -> Option<(&str, &ast::Expr)> {
    let ast::Stmt::Expr(expression) = statement else {
        return None;
    };
    let ast::Expr::Call(call) = expression.value.as_ref() else {
        return None;
    };
    let name = direct_call_name(call)?;
    if !matches!(name, "Requires" | "Ensures" | "Exsures" | "Invariant") {
        return None;
    }
    call.args.first().map(|argument| (name, argument))
}

fn is_contract_statement(statement: &ast::Stmt) -> bool {
    contract_statement(statement).is_some()
}

fn invariant_argument(statement: &ast::Stmt) -> Option<&ast::Expr> {
    contract_statement(statement)
        .filter(|(name, _)| *name == "Invariant")
        .map(|(_, argument)| argument)
}

fn collect_obligation_specs(
    expression: &ast::Expr,
    inside_invariant: bool,
    primitives: &BTreeSet<String>,
) -> Result<Vec<ObligationSpec>, ContractFailure> {
    let mut result = Vec::new();
    collect_obligation_specs_inner(expression, false, inside_invariant, primitives, &mut result)?;
    Ok(result)
}

fn collect_obligation_specs_inner(
    expression: &ast::Expr,
    conditional: bool,
    inside_invariant: bool,
    primitives: &BTreeSet<String>,
    result: &mut Vec<ObligationSpec>,
) -> Result<(), ContractFailure> {
    if let ast::Expr::BoolOp(operation) = expression
        && operation.op == ast::BoolOp::And
    {
        for value in &operation.values {
            collect_obligation_specs_inner(
                value,
                conditional,
                inside_invariant,
                primitives,
                result,
            )?;
        }
        return Ok(());
    }
    if let ast::Expr::Call(call) = expression
        && direct_call_name(call).is_some_and(|name| name == "Implies")
    {
        let [_, consequence] = call.args.as_slice() else {
            return obligation_failure(
                "frontend.python.obligations.implies-arity",
                "Implies obligation clauses require condition and consequence",
            );
        };
        return collect_obligation_specs_inner(
            consequence,
            true,
            inside_invariant,
            primitives,
            result,
        );
    }
    let ast::Expr::Call(call) = expression else {
        return Ok(());
    };
    let Some(name) = direct_call_name(call) else {
        return Ok(());
    };
    if !primitives.contains(name) {
        return Ok(());
    }
    let kind = match name {
        "MustRelease" => ObligationKind::Release,
        "MustInvoke" | "token" => ObligationKind::Invoke,
        _ => return Ok(()),
    };
    let Some(target) = call.args.first() else {
        return obligation_failure(
            "frontend.python.obligations.target-missing",
            "obligation clauses require an identity target",
        );
    };
    let (root, fields) = identity_path(target).ok_or_else(|| ContractFailure {
        code: "frontend.python.obligations.dynamic-identity-unsupported",
        message: "obligation identity must be a direct parameter/local or attribute path"
            .to_owned(),
    })?;
    let measure = call
        .args
        .get(1)
        .map(measure_of)
        .unwrap_or(Measure::Unbounded);
    result.push(ObligationSpec {
        kind,
        root,
        fields,
        measure,
        conditional: conditional
            || (inside_invariant && expression_is_conditionally_guarded(expression)),
        bounded: call.args.get(1).is_some(),
        offset: u32::from(expression.range().start()),
    });
    Ok(())
}

fn identity_path(expression: &ast::Expr) -> Option<(String, Vec<String>)> {
    match expression {
        ast::Expr::Name(name) => Some((name.id.to_string(), Vec::new())),
        ast::Expr::Attribute(attribute) => {
            let (root, mut fields) = identity_path(&attribute.value)?;
            fields.push(attribute.attr.to_string());
            Some((root, fields))
        }
        _ => None,
    }
}

fn collect_level_specs(
    expression: &ast::Expr,
    bindings: &ResolvedLevelIntrinsicBindings,
) -> Result<Vec<LevelSpec>, ContractFailure> {
    let mut result = Vec::new();
    collect_level_specs_inner(expression, bindings, &mut result)?;
    Ok(result)
}

fn collect_level_specs_inner(
    expression: &ast::Expr,
    bindings: &ResolvedLevelIntrinsicBindings,
    result: &mut Vec<LevelSpec>,
) -> Result<(), ContractFailure> {
    match expression {
        ast::Expr::BoolOp(operation) if operation.op == ast::BoolOp::And => {
            for value in &operation.values {
                collect_level_specs_inner(value, bindings, result)?;
            }
            return Ok(());
        }
        ast::Expr::Call(call) if direct_call_name(call).is_some_and(|name| name == "Implies") => {
            let [_, consequence] = call.args.as_slice() else {
                return obligation_failure(
                    "frontend.python.obligations.level-implies-arity",
                    "level-order Implies clauses require condition and consequence",
                );
            };
            collect_level_specs_inner(consequence, bindings, result)?;
            return Ok(());
        }
        ast::Expr::Compare(comparison)
            if matches!(comparison.ops.as_slice(), [ast::CmpOp::Lt])
                && comparison.comparators.len() == 1 =>
        {
            let ast::Expr::Call(wait_level) = comparison.left.as_ref() else {
                if expression_contains_level_intrinsic(expression, bindings) {
                    return malformed_level_relation();
                }
                return Ok(());
            };
            let Some(wait_name) = direct_call_name(wait_level) else {
                return malformed_level_relation();
            };
            if bindings
                .event(wait_name)
                .is_none_or(|event| event.kind() != LevelIntrinsicEventKind::WaitLevel)
            {
                if expression_contains_level_intrinsic(expression, bindings) {
                    return malformed_level_relation();
                }
                return Ok(());
            }
            if !wait_level.args.is_empty() || !wait_level.keywords.is_empty() {
                return obligation_failure(
                    "frontend.python.obligations.wait-level-arity",
                    "canonical WaitLevel takes no arguments",
                );
            }
            let ast::Expr::Call(level) = &comparison.comparators[0] else {
                return malformed_level_relation();
            };
            let Some(level_name) = direct_call_name(level) else {
                return malformed_level_relation();
            };
            if bindings
                .event(level_name)
                .is_none_or(|event| event.kind() != LevelIntrinsicEventKind::Level)
            {
                return malformed_level_relation();
            }
            let [target] = level.args.as_slice() else {
                return obligation_failure(
                    "frontend.python.obligations.level-arity",
                    "canonical Level requires exactly one runtime object",
                );
            };
            if !level.keywords.is_empty() {
                return obligation_failure(
                    "frontend.python.obligations.level-keywords-unsupported",
                    "canonical Level does not accept keyword arguments",
                );
            }
            let (root, fields) = identity_path(target).ok_or_else(|| ContractFailure {
                code: "frontend.python.obligations.level-dynamic-identity-unsupported",
                message:
                    "Level target must resolve to a stable parameter, local, or attribute path"
                        .to_owned(),
            })?;
            result.push(LevelSpec {
                root,
                fields,
                offset: u32::from(expression.range().start()),
            });
            return Ok(());
        }
        _ => {}
    }
    if expression_contains_level_intrinsic(expression, bindings) {
        return obligation_failure(
            "frontend.python.obligations.level-intrinsic-standalone",
            "Level and WaitLevel are verifier intrinsics and must form WaitLevel() < Level(object)",
        );
    }
    Ok(())
}

fn malformed_level_relation<T>() -> Result<T, ContractFailure> {
    obligation_failure(
        "frontend.python.obligations.level-relation-malformed",
        "level-order predicates must have the exact form WaitLevel() < Level(object)",
    )
}

fn expression_contains_level_intrinsic(
    expression: &ast::Expr,
    bindings: &ResolvedLevelIntrinsicBindings,
) -> bool {
    match expression {
        ast::Expr::Call(call) => {
            direct_call_name(call).is_some_and(|name| bindings.event(name).is_some())
                || expression_contains_level_intrinsic(&call.func, bindings)
                || call
                    .args
                    .iter()
                    .any(|argument| expression_contains_level_intrinsic(argument, bindings))
                || call
                    .keywords
                    .iter()
                    .any(|keyword| expression_contains_level_intrinsic(&keyword.value, bindings))
        }
        ast::Expr::BoolOp(operation) => operation
            .values
            .iter()
            .any(|value| expression_contains_level_intrinsic(value, bindings)),
        ast::Expr::UnaryOp(unary) => expression_contains_level_intrinsic(&unary.operand, bindings),
        ast::Expr::BinOp(operation) => {
            expression_contains_level_intrinsic(&operation.left, bindings)
                || expression_contains_level_intrinsic(&operation.right, bindings)
        }
        ast::Expr::Lambda(lambda) => expression_contains_level_intrinsic(&lambda.body, bindings),
        ast::Expr::Tuple(tuple) => tuple
            .elts
            .iter()
            .any(|value| expression_contains_level_intrinsic(value, bindings)),
        ast::Expr::List(list) => list
            .elts
            .iter()
            .any(|value| expression_contains_level_intrinsic(value, bindings)),
        ast::Expr::Compare(comparison) => {
            expression_contains_level_intrinsic(&comparison.left, bindings)
                || comparison
                    .comparators
                    .iter()
                    .any(|value| expression_contains_level_intrinsic(value, bindings))
        }
        _ => false,
    }
}

fn measure_of(expression: &ast::Expr) -> Measure {
    match expression {
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Int(value) => value
                .to_string()
                .parse::<i64>()
                .map(Measure::Known)
                .unwrap_or_else(|_| Measure::Unknown(format!("{expression:?}"))),
            _ => Measure::Unknown(format!("{expression:?}")),
        },
        ast::Expr::UnaryOp(unary) if unary.op == ast::UnaryOp::USub => {
            match measure_of(&unary.operand) {
                Measure::Known(value) => Measure::Known(-value),
                Measure::Unknown(value) => Measure::Unknown(format!("-({value})")),
                Measure::Unbounded => Measure::Unknown("-(unbounded)".to_owned()),
            }
        }
        _ => Measure::Unknown(format!("{expression:?}")),
    }
}

fn instantiate_spec_identity(
    spec: &ObligationSpec,
    summary: &FunctionSummary,
    arguments: &[ast::Expr],
    state: &LedgerState,
) -> Option<String> {
    let mut identity = if arguments.is_empty() {
        state.aliases.get(&spec.root).cloned()?
    } else {
        let parameter_index = summary
            .parameters
            .iter()
            .position(|parameter| parameter == &spec.root)?;
        state.identity_of(arguments.get(parameter_index)?)?
    };
    for field in &spec.fields {
        identity.push('.');
        identity.push_str(field);
    }
    Some(identity)
}

fn instantiate_state_spec_identity(spec: &ObligationSpec, state: &LedgerState) -> Option<String> {
    let mut identity = state.aliases.get(&spec.root).cloned()?;
    for field in &spec.fields {
        identity.push('.');
        identity.push_str(field);
    }
    Some(identity)
}

fn instantiate_call_spec_identity(
    spec: &ObligationSpec,
    summary: &FunctionSummary,
    call: &ast::ExprCall,
    state: &LedgerState,
) -> Option<String> {
    let parameter_index = summary
        .parameters
        .iter()
        .position(|parameter| parameter == &spec.root)?;
    let argument = match call.func.as_ref() {
        ast::Expr::Attribute(attribute) => {
            if parameter_index == 0 {
                attribute.value.as_ref()
            } else {
                call.args.get(parameter_index - 1)?
            }
        }
        ast::Expr::Name(_) => call.args.get(parameter_index)?,
        _ => return None,
    };
    let mut identity = state.identity_of(argument)?;
    for field in &spec.fields {
        identity.push('.');
        identity.push_str(field);
    }
    Some(identity)
}

fn instantiate_level_identity(
    spec: &LevelSpec,
    summary: &FunctionSummary,
    arguments: &[ast::Expr],
    state: &LedgerState,
) -> Option<LevelIdentity> {
    let mut identity = if arguments.is_empty() {
        state.aliases.get(&spec.root).cloned()?
    } else {
        let parameter_index = summary
            .parameters
            .iter()
            .position(|parameter| parameter == &spec.root)?;
        state.identity_of(arguments.get(parameter_index)?)?
    };
    for field in &spec.fields {
        identity.push('.');
        identity.push_str(field);
    }
    Some(LevelState::certify_resolved_object(identity))
}

fn instantiate_call_level_identity(
    spec: &LevelSpec,
    summary: &FunctionSummary,
    call: &ast::ExprCall,
    state: &LedgerState,
) -> Option<LevelIdentity> {
    let parameter_index = summary
        .parameters
        .iter()
        .position(|parameter| parameter == &spec.root)?;
    let argument = match call.func.as_ref() {
        ast::Expr::Attribute(attribute) => {
            if parameter_index == 0 {
                attribute.value.as_ref()
            } else {
                call.args.get(parameter_index - 1)?
            }
        }
        ast::Expr::Name(_) => call.args.get(parameter_index)?,
        _ => return None,
    };
    let mut identity = state.identity_of(argument)?;
    for field in &spec.fields {
        identity.push('.');
        identity.push_str(field);
    }
    Some(LevelState::certify_resolved_object(identity))
}

fn apply_required_equalities(
    function: &ast::StmtFunctionDef,
    state: &mut LedgerState,
) -> Result<(), ContractFailure> {
    for statement in &function.body {
        let Some(("Requires", argument)) = contract_statement(statement) else {
            continue;
        };
        for conjunct in flatten_and(argument) {
            let ast::Expr::Compare(comparison) = conjunct else {
                continue;
            };
            if !matches!(comparison.ops.as_slice(), [ast::CmpOp::Is]) {
                continue;
            }
            let ast::Expr::Name(left) = comparison.left.as_ref() else {
                continue;
            };
            let [ast::Expr::Name(right)] = comparison.comparators.as_slice() else {
                continue;
            };
            state.unify_names(left.id.as_str(), right.id.as_str())?;
        }
    }
    Ok(())
}

fn refine_identity_condition(
    expression: &ast::Expr,
    truthy: bool,
    state: &mut LedgerState,
) -> Result<(), ContractFailure> {
    let ast::Expr::Compare(comparison) = expression else {
        return Ok(());
    };
    let [operator] = comparison.ops.as_slice() else {
        return Ok(());
    };
    let ast::Expr::Name(left) = comparison.left.as_ref() else {
        return Ok(());
    };
    let [ast::Expr::Name(right)] = comparison.comparators.as_slice() else {
        return Ok(());
    };
    let equal_path = matches!(operator, ast::CmpOp::Is) == truthy;
    if equal_path {
        state.unify_names(left.id.as_str(), right.id.as_str())?;
    }
    Ok(())
}

fn flatten_and(expression: &ast::Expr) -> Vec<&ast::Expr> {
    match expression {
        ast::Expr::BoolOp(operation) if operation.op == ast::BoolOp::And => {
            operation.values.iter().flat_map(flatten_and).collect()
        }
        _ => vec![expression],
    }
}

fn expression_contains_call(expression: &ast::Expr, expected: &str) -> bool {
    match expression {
        ast::Expr::Call(call) => {
            direct_call_name(call).is_some_and(|name| name == expected)
                || expression_contains_call(&call.func, expected)
                || call
                    .args
                    .iter()
                    .any(|argument| expression_contains_call(argument, expected))
                || call
                    .keywords
                    .iter()
                    .any(|keyword| expression_contains_call(&keyword.value, expected))
        }
        ast::Expr::BoolOp(operation) => operation
            .values
            .iter()
            .any(|value| expression_contains_call(value, expected)),
        ast::Expr::UnaryOp(unary) => expression_contains_call(&unary.operand, expected),
        ast::Expr::BinOp(operation) => {
            expression_contains_call(&operation.left, expected)
                || expression_contains_call(&operation.right, expected)
        }
        ast::Expr::Lambda(lambda) => expression_contains_call(&lambda.body, expected),
        ast::Expr::Tuple(tuple) => tuple
            .elts
            .iter()
            .any(|value| expression_contains_call(value, expected)),
        ast::Expr::List(list) => list
            .elts
            .iter()
            .any(|value| expression_contains_call(value, expected)),
        ast::Expr::Compare(comparison) => {
            expression_contains_call(&comparison.left, expected)
                || comparison
                    .comparators
                    .iter()
                    .any(|value| expression_contains_call(value, expected))
        }
        _ => false,
    }
}

fn obligation_measure_progresses(expression: &ast::Expr, body: &[ast::Stmt]) -> bool {
    match expression {
        ast::Expr::BoolOp(operation) if operation.op == ast::BoolOp::And => operation
            .values
            .iter()
            .any(|value| obligation_measure_progresses(value, body)),
        ast::Expr::Call(call) if direct_call_name(call).is_some_and(|name| name == "Implies") => {
            call.args
                .get(1)
                .is_some_and(|value| obligation_measure_progresses(value, body))
        }
        ast::Expr::Call(call)
            if direct_call_name(call)
                .is_some_and(|name| matches!(name, "MustRelease" | "MustInvoke" | "token")) =>
        {
            call.args
                .get(1)
                .is_some_and(|measure| decreasing_measure_variable(measure, body).is_some())
        }
        _ => false,
    }
}

fn decreasing_measure_variable<'a>(
    expression: &'a ast::Expr,
    body: &[ast::Stmt],
) -> Option<&'a str> {
    let ast::Expr::BinOp(operation) = expression else {
        return None;
    };
    if operation.op != ast::Operator::Sub {
        return None;
    }
    let ast::Expr::Name(name) = operation.right.as_ref() else {
        return None;
    };
    block_increments_name(body, name.id.as_str()).then_some(name.id.as_str())
}

fn block_increments_name(body: &[ast::Stmt], expected: &str) -> bool {
    body.iter().any(|statement| match statement {
        ast::Stmt::AugAssign(assignment) => {
            assignment.op == ast::Operator::Add
                && matches!(assignment.target.as_ref(), ast::Expr::Name(name) if name.id.as_str() == expected)
                && eval_int_expression(&assignment.value).is_some_and(|value| value > 0)
        }
        ast::Stmt::If(branch) => {
            block_increments_name(&branch.body, expected)
                || block_increments_name(&branch.orelse, expected)
        }
        _ => false,
    })
}

fn block_recreates_obligation(
    body: &[ast::Stmt],
    owner: &str,
    summaries: &BTreeMap<String, FunctionSummary>,
) -> bool {
    fn contains_method(body: &[ast::Stmt], expected: &str) -> bool {
        body.iter().any(|statement| match statement {
            ast::Stmt::Expr(expression) => {
                matches!(expression.value.as_ref(), ast::Expr::Call(call)
                if matches!(call.func.as_ref(), ast::Expr::Attribute(attribute)
                    if attribute.attr.as_str() == expected))
            }
            ast::Stmt::If(branch) => {
                contains_method(&branch.body, expected) || contains_method(&branch.orelse, expected)
            }
            ast::Stmt::Try(try_) => {
                contains_method(&try_.body, expected)
                    || contains_method(&try_.orelse, expected)
                    || contains_method(&try_.finalbody, expected)
            }
            _ => false,
        })
    }
    fn contains_open(body: &[ast::Stmt]) -> bool {
        body.iter().any(|statement| match statement {
            ast::Stmt::Expr(expression) => {
                matches!(expression.value.as_ref(), ast::Expr::Call(call)
                if direct_call_name(call).is_some_and(|name| name == "Open"))
            }
            ast::Stmt::If(branch) => contains_open(&branch.body) || contains_open(&branch.orelse),
            ast::Stmt::Try(try_) => {
                contains_open(&try_.body)
                    || contains_open(&try_.orelse)
                    || contains_open(&try_.finalbody)
            }
            _ => false,
        })
    }
    fn contains_io_token_transform(
        body: &[ast::Stmt],
        owner: &str,
        summaries: &BTreeMap<String, FunctionSummary>,
    ) -> bool {
        body.iter().any(|statement| match statement {
            ast::Stmt::Assign(assignment) => {
                matches!(assignment.value.as_ref(), ast::Expr::Call(call)
                    if resolved_call_name(call, owner, summaries)
                        .and_then(|called| summaries.get(&called))
                        .is_some_and(|summary| summary.io_token_transform))
            }
            ast::Stmt::AnnAssign(assignment) => assignment.value.as_deref().is_some_and(|value| {
                matches!(value, ast::Expr::Call(call)
                    if resolved_call_name(call, owner, summaries)
                        .and_then(|called| summaries.get(&called))
                        .is_some_and(|summary| summary.io_token_transform))
            }),
            ast::Stmt::If(branch) => {
                contains_io_token_transform(&branch.body, owner, summaries)
                    || contains_io_token_transform(&branch.orelse, owner, summaries)
            }
            ast::Stmt::Try(try_) => {
                contains_io_token_transform(&try_.body, owner, summaries)
                    || contains_io_token_transform(&try_.orelse, owner, summaries)
                    || contains_io_token_transform(&try_.finalbody, owner, summaries)
            }
            _ => false,
        })
    }
    fn contains_release_summary(
        body: &[ast::Stmt],
        owner: &str,
        summaries: &BTreeMap<String, FunctionSummary>,
        returned: bool,
    ) -> bool {
        body.iter().any(|statement| {
            let call = match statement {
                ast::Stmt::Expr(expression) => match expression.value.as_ref() {
                    ast::Expr::Call(call) => Some(call),
                    _ => None,
                },
                ast::Stmt::Assign(assignment) => match assignment.value.as_ref() {
                    ast::Expr::Call(call) => Some(call),
                    _ => None,
                },
                ast::Stmt::AnnAssign(assignment) => match assignment.value.as_deref() {
                    Some(ast::Expr::Call(call)) => Some(call),
                    _ => None,
                },
                _ => None,
            };
            if call
                .and_then(|call| resolved_call_name(call, owner, summaries))
                .and_then(|called| summaries.get(&called))
                .is_some_and(|summary| {
                    let obligations = if returned {
                        &summary.returned
                    } else {
                        &summary.required
                    };
                    obligations
                        .iter()
                        .any(|obligation| obligation.kind == ObligationKind::Release)
                })
            {
                return true;
            }
            match statement {
                ast::Stmt::If(branch) => {
                    contains_release_summary(&branch.body, owner, summaries, returned)
                        || contains_release_summary(&branch.orelse, owner, summaries, returned)
                }
                ast::Stmt::Try(try_) => {
                    contains_release_summary(&try_.body, owner, summaries, returned)
                        || contains_release_summary(&try_.orelse, owner, summaries, returned)
                        || contains_release_summary(&try_.finalbody, owner, summaries, returned)
                }
                _ => false,
            }
        })
    }
    let consumes_release =
        contains_method(body, "release") || contains_release_summary(body, owner, summaries, false);
    let produces_release =
        contains_method(body, "acquire") || contains_release_summary(body, owner, summaries, true);
    (consumes_release && produces_release)
        || (contains_open(body) && contains_io_token_transform(body, owner, summaries))
}

fn expression_is_statically_false(expression: &ast::Expr) -> bool {
    if matches!(expression, ast::Expr::Constant(constant)
        if constant.value == ast::Constant::Bool(false))
    {
        return true;
    }
    let ast::Expr::Compare(comparison) = expression else {
        return false;
    };
    let (Some(left), [operator], [right]) = (
        eval_int_expression(&comparison.left),
        comparison.ops.as_slice(),
        comparison.comparators.as_slice(),
    ) else {
        return false;
    };
    let Some(right) = eval_int_expression(right) else {
        return false;
    };
    !match operator {
        ast::CmpOp::Eq => left == right,
        ast::CmpOp::NotEq => left != right,
        ast::CmpOp::Lt => left < right,
        ast::CmpOp::LtE => left <= right,
        ast::CmpOp::Gt => left > right,
        ast::CmpOp::GtE => left >= right,
        _ => return false,
    }
}

fn expression_is_statically_true(expression: &ast::Expr) -> bool {
    if matches!(expression, ast::Expr::Constant(constant)
        if constant.value == ast::Constant::Bool(true))
    {
        return true;
    }
    let ast::Expr::Compare(comparison) = expression else {
        return false;
    };
    let (Some(left), [operator], [right]) = (
        eval_int_expression(&comparison.left),
        comparison.ops.as_slice(),
        comparison.comparators.as_slice(),
    ) else {
        return false;
    };
    let Some(right) = eval_int_expression(right) else {
        return false;
    };
    match operator {
        ast::CmpOp::Eq => left == right,
        ast::CmpOp::NotEq => left != right,
        ast::CmpOp::Lt => left < right,
        ast::CmpOp::LtE => left <= right,
        ast::CmpOp::Gt => left > right,
        ast::CmpOp::GtE => left >= right,
        _ => false,
    }
}

fn eval_int_expression(expression: &ast::Expr) -> Option<i64> {
    match expression {
        ast::Expr::Constant(constant) => match &constant.value {
            ast::Constant::Int(value) => value.to_string().parse().ok(),
            _ => None,
        },
        ast::Expr::UnaryOp(unary) if unary.op == ast::UnaryOp::USub => {
            eval_int_expression(&unary.operand)?.checked_neg()
        }
        ast::Expr::BinOp(operation) => {
            let left = eval_int_expression(&operation.left)?;
            let right = eval_int_expression(&operation.right)?;
            match operation.op {
                ast::Operator::Add => left.checked_add(right),
                ast::Operator::Sub => left.checked_sub(right),
                ast::Operator::Mult => left.checked_mul(right),
                _ => None,
            }
        }
        _ => None,
    }
}

fn expression_is_conditionally_guarded(_expression: &ast::Expr) -> bool {
    false
}

fn exception_name(expression: &ast::Expr) -> Option<&str> {
    match expression {
        ast::Expr::Name(name) => Some(name.id.as_str()),
        ast::Expr::Call(call) => direct_call_name(call),
        _ => None,
    }
}

fn direct_call_name(call: &ast::ExprCall) -> Option<&str> {
    match call.func.as_ref() {
        ast::Expr::Name(name) => Some(name.id.as_str()),
        _ => None,
    }
}

fn resolved_call_name(
    call: &ast::ExprCall,
    owner: &str,
    summaries: &BTreeMap<String, FunctionSummary>,
) -> Option<String> {
    match call.func.as_ref() {
        ast::Expr::Name(name) => Some(name.id.to_string()),
        ast::Expr::Attribute(attribute) if matches!(attribute.value.as_ref(), ast::Expr::Name(name) if name.id.as_str() == "self") =>
        {
            let (class, _) = owner.split_once('.')?;
            let qualified = format!("{class}.{}", attribute.attr);
            summaries.contains_key(&qualified).then_some(qualified)
        }
        _ => None,
    }
}

fn is_constructor_name(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_uppercase)
}

fn is_runtime_contract_name(name: &str, primitives: &BTreeSet<String>) -> bool {
    matches!(
        name,
        "Requires" | "Ensures" | "Exsures" | "Invariant" | "Assert" | "Acc" | "Implies"
    ) || primitives.contains(name)
}

fn suite_contains_proven_lock_operation(
    suite: &[ast::Stmt],
    summaries: &BTreeMap<String, FunctionSummary>,
    bindings: &CanonicalBindings,
) -> bool {
    fn function_contains(
        function: &ast::StmtFunctionDef,
        owner: &str,
        summary: &FunctionSummary,
        bindings: &CanonicalBindings,
    ) -> bool {
        let mut lock_roots = summary.lock_parameters.clone();
        for statement in &function.body {
            if let ast::Stmt::Assign(assignment) = statement
                && let [ast::Expr::Name(target)] = assignment.targets.as_slice()
                && matches!(assignment.value.as_ref(), ast::Expr::Call(call)
                    if direct_call_name(call).is_some_and(|name| bindings.lock_classes.contains(name)))
            {
                lock_roots.insert(target.id.to_string());
            }
        }
        let class = owner.split_once('.').map(|(class, _)| class);
        fn receiver_is_lock(
            receiver: &ast::Expr,
            lock_roots: &BTreeSet<String>,
            class: Option<&str>,
            bindings: &CanonicalBindings,
        ) -> bool {
            match receiver {
                ast::Expr::Name(name) => lock_roots.contains(name.id.as_str()),
                ast::Expr::Attribute(attribute) => {
                    matches!(attribute.value.as_ref(), ast::Expr::Name(name)
                        if name.id.as_str() == "self"
                            && class.and_then(|class| bindings.lock_fields.get(class))
                                .is_some_and(|fields| fields.contains(attribute.attr.as_str())))
                }
                _ => false,
            }
        }
        fn statements_contain(
            statements: &[ast::Stmt],
            lock_roots: &BTreeSet<String>,
            class: Option<&str>,
            bindings: &CanonicalBindings,
        ) -> bool {
            statements.iter().any(|statement| match statement {
                ast::Stmt::Expr(expression) => {
                    matches!(expression.value.as_ref(), ast::Expr::Call(call)
                    if matches!(call.func.as_ref(), ast::Expr::Attribute(attribute)
                        if matches!(attribute.attr.as_str(), "acquire" | "release")
                            && receiver_is_lock(&attribute.value, lock_roots, class, bindings)))
                }
                ast::Stmt::If(branch) => {
                    statements_contain(&branch.body, lock_roots, class, bindings)
                        || statements_contain(&branch.orelse, lock_roots, class, bindings)
                }
                ast::Stmt::While(loop_) => {
                    statements_contain(&loop_.body, lock_roots, class, bindings)
                        || statements_contain(&loop_.orelse, lock_roots, class, bindings)
                }
                ast::Stmt::For(loop_) => {
                    statements_contain(&loop_.body, lock_roots, class, bindings)
                        || statements_contain(&loop_.orelse, lock_roots, class, bindings)
                }
                ast::Stmt::Try(try_) => {
                    statements_contain(&try_.body, lock_roots, class, bindings)
                        || statements_contain(&try_.orelse, lock_roots, class, bindings)
                        || statements_contain(&try_.finalbody, lock_roots, class, bindings)
                }
                _ => false,
            })
        }
        statements_contain(&function.body, &lock_roots, class, bindings)
    }

    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                if summaries
                    .get(function.name.as_str())
                    .is_some_and(|summary| {
                        function_contains(function, function.name.as_str(), summary, bindings)
                    })
                {
                    return true;
                }
            }
            ast::Stmt::ClassDef(class) => {
                for statement in &class.body {
                    if let ast::Stmt::FunctionDef(function) = statement {
                        let owner = format!("{}.{}", class.name, function.name);
                        if summaries.get(&owner).is_some_and(|summary| {
                            function_contains(function, &owner, summary, bindings)
                        }) {
                            return true;
                        }
                    }
                }
            }
            _ => {}
        }
    }
    false
}

fn make_obligation(
    id: String,
    conclusion: bool,
    source: &str,
    path: &str,
    offset: u32,
) -> Obligation {
    let (line, column) = location(source, offset);
    Obligation {
        id,
        expectation: ObligationExpectation::Prove,
        assumptions: Vec::new(),
        conclusion: Term::Bool { value: conclusion },
        path: path.to_owned(),
        byte_offset: offset,
        line,
        column,
    }
}

fn location(source: &str, offset: u32) -> (u32, u32) {
    let offset = usize::try_from(offset)
        .unwrap_or(source.len())
        .min(source.len());
    let prefix = &source[..offset];
    let line =
        u32::try_from(prefix.bytes().filter(|byte| *byte == b'\n').count() + 1).unwrap_or(u32::MAX);
    let column = u32::try_from(
        prefix
            .rsplit_once('\n')
            .map_or(prefix, |(_, tail)| tail)
            .chars()
            .count()
            + 1,
    )
    .unwrap_or(u32::MAX);
    (line, column)
}

fn unsupported_dynamic_identity<T>(statement: &ast::Stmt) -> Result<T, ContractFailure> {
    obligation_failure(
        "frontend.python.obligations.dynamic-identity-unsupported",
        format!(
            "statement at {:?} changes an obligation identity through unsupported dynamic syntax",
            statement.range()
        ),
    )
}

fn dynamic_call_identity<T>(target: &str) -> Result<T, ContractFailure> {
    obligation_failure(
        "frontend.python.obligations.dynamic-identity-unsupported",
        format!("call target {target:?} has no statically closed obligation identity"),
    )
}

fn obligation_failure<T>(
    code: &'static str,
    message: impl Into<String>,
) -> Result<T, ContractFailure> {
    Err(ContractFailure {
        code,
        message: message.into(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::python_obligation_levels::CertifiedLevelIntrinsics;
    use crate::python_verifier_intrinsics::{
        VerifierIntrinsicKind, validate_canonical_obligations_provider,
    };

    fn resolved_level_bindings(
        level_name: &str,
        wait_level_name: &str,
    ) -> ResolvedLevelIntrinsicBindings {
        let source = include_str!("../.upstream/nagini/src/nagini_contracts/obligations.py");
        let provider = validate_canonical_obligations_provider(source, "obligations.py")
            .expect("canonical provider");
        let certified = CertifiedLevelIntrinsics::from_validated_provider(&provider)
            .expect("certified level intrinsics");
        let mut descriptors = BTreeMap::new();
        for descriptor in provider.functions.values() {
            let local_name = match descriptor.kind {
                VerifierIntrinsicKind::Level => Some(level_name),
                VerifierIntrinsicKind::WaitLevel => Some(wait_level_name),
                _ => None,
            };
            if let Some(local_name) = local_name {
                descriptors.insert(local_name.to_owned(), descriptor.clone());
            }
        }
        ResolvedLevelIntrinsicBindings::from_resolver_descriptors(&certified, &descriptors)
    }

    #[test]
    fn symbolic_measure_does_not_forge_the_primitive_release_precondition() {
        let source = r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import MustRelease

def release(lock: Lock[object], amount: int) -> None:
    Requires(MustRelease(lock, amount))
    lock.release()
"#;
        let verification = verify_obligation_module(source, "symbolic_measure.py")
            .expect("closed symbolic identity should lower")
            .expect("obligation source should be claimed");
        assert!(!verification.passed, "{verification:#?}");
        assert!(verification.obligations.iter().any(|obligation| {
            !obligation.satisfied() && obligation.id.contains(":obligation-release-precondition:")
        }));
    }

    #[test]
    fn alias_refinement_makes_a_two_obligation_collision_unreachable() {
        let source = r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import MustRelease

def collide(left: Lock[object], right: Lock[object]) -> None:
    Requires(MustRelease(left, 1) and MustRelease(right, 1))
    if left is right:
        pass
    else:
        left.release()
        right.release()
"#;
        let verification = verify_obligation_module(source, "alias_collision.py")
            .expect("closed alias refinement should lower")
            .expect("obligation source should be claimed");
        assert!(verification.passed, "{verification:#?}");
    }

    #[test]
    fn dynamic_subscript_identity_fails_closed() {
        let source = r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import MustRelease

def release_dynamic(lock: Lock[object], locks: object, index: int) -> None:
    Requires(MustRelease(lock, 1))
    locks[index].release()
"#;
        let failure = verify_obligation_module(source, "dynamic_identity.py")
            .expect_err("dynamic obligation identity must not be guessed");
        assert_eq!(
            failure.code,
            "frontend.python.obligations.dynamic-identity-unsupported"
        );
    }

    #[test]
    fn import_only_and_ordinary_permission_syntax_do_not_activate_obligations() {
        for (path, source) in [
            (
                "import_only.py",
                "from nagini_contracts.obligations import *\n",
            ),
            (
                "ordinary_acc.py",
                r#"from nagini_contracts.contracts import *
from nagini_contracts.obligations import *

class Item:
    value: int

def read(item: Item) -> None:
    Requires(Acc(item.value, 1 / 2))
"#,
            ),
        ] {
            assert!(
                verify_obligation_module(source, path).unwrap().is_none(),
                "{path} must remain owned by ordinary heap semantics"
            );
        }
    }

    #[test]
    fn arbitrary_acquire_release_spelling_does_not_activate_lock_obligations() {
        let source = r#"from nagini_contracts.obligations import *

class Ordinary:
    def acquire(self) -> None:
        pass
    def release(self) -> None:
        pass

def use(value: Ordinary) -> None:
    value.acquire()
    value.release()
"#;
        assert!(
            verify_obligation_module(source, "ordinary_methods.py")
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn locally_shadowed_primitive_does_not_activate_obligation_specs() {
        let source = r#"from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustRelease

def use(MustRelease: object, value: object) -> None:
    Requires(MustRelease(value, 1))
"#;
        assert!(
            verify_obligation_module(source, "shadowed_primitive.py")
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn canonical_lock_receiver_provenance_activates_acquire_semantics() {
        let source = r#"from nagini_contracts.obligations import *
from nagini_contracts.lock import Lock

def acquire(lock: Lock[object]) -> None:
    lock.acquire()
"#;
        let verification = verify_obligation_module(source, "canonical_lock.py")
            .unwrap()
            .expect("canonical Lock.acquire must activate obligation checking");
        assert!(!verification.passed, "{verification:#?}");
    }

    #[test]
    fn resolver_certified_aliases_discharge_wait_level_acquire_preconditions() {
        let source = r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import Level as L, WaitLevel as W

def acquire_and_release(lock: Lock[object]) -> None:
    Requires(W() < L(lock))
    lock.acquire()
    lock.release()
"#;
        let bindings = resolved_level_bindings("L", "W");
        let verification =
            verify_obligation_module_with_intrinsics(source, "level_alias.py", &bindings)
                .expect("certified aliases should lower")
                .expect("level source should be claimed");
        assert!(verification.passed, "{verification:#?}");
    }

    #[test]
    fn missing_call_order_evidence_is_a_precise_failed_obligation() {
        let source = r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import Level as L, WaitLevel as W

def acquire_and_release(lock: Lock[object]) -> None:
    Requires(W() < L(lock))
    lock.acquire()
    lock.release()

def caller(lock: Lock[object]) -> None:
    acquire_and_release(lock)
"#;
        let bindings = resolved_level_bindings("L", "W");
        let verification =
            verify_obligation_module_with_intrinsics(source, "level_call.py", &bindings)
                .expect("closed level call should lower")
                .expect("level source should be claimed");
        assert!(!verification.passed, "{verification:#?}");
        assert!(verification.obligations.iter().any(|obligation| {
            !obligation.satisfied() && obligation.id.contains(":call-precondition:")
        }));
    }

    #[test]
    fn module_rebinding_removes_the_resolver_certified_intrinsic() {
        let source = r#"from nagini_contracts.contracts import *
from nagini_contracts.obligations import Level as L, WaitLevel as W
W = object()

def ordinary(value: object) -> None:
    Requires(W())
"#;
        let bindings = resolved_level_bindings("L", "W");
        assert!(
            verify_obligation_module_with_intrinsics(source, "level_rebound.py", &bindings)
                .expect("rebound intrinsic should not be interpreted")
                .is_none()
        );
    }

    #[test]
    fn malformed_certified_intrinsic_relation_fails_closed() {
        let source = r#"from nagini_contracts.contracts import *
from nagini_contracts.obligations import Level as L, WaitLevel as W

def malformed(value: object) -> None:
    Requires(L(value) < W())
"#;
        let bindings = resolved_level_bindings("L", "W");
        let failure =
            verify_obligation_module_with_intrinsics(source, "level_malformed.py", &bindings)
                .expect_err("reversed level relation must be refused");
        assert_eq!(
            failure.code,
            "frontend.python.obligations.level-relation-malformed"
        );
    }

    #[test]
    fn constructor_proven_lock_fields_produce_release_obligations_until_rebound() {
        let bindings = resolved_level_bindings("L", "W");
        let leaking = r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import Level as L, WaitLevel as W

class ObjectLock(Lock[object]):
    pass

class Holder:
    def __init__(self) -> None:
        self.lock = ObjectLock(object())
        Ensures(W() < L(self.lock))

    def leak(self) -> None:
        Requires(W() < L(self.lock))
        self.lock.acquire()
"#;
        let verification =
            verify_obligation_module_with_intrinsics(leaking, "inferred_lock_field.py", &bindings)
                .expect("constructor-proven lock field should lower")
                .expect("lock acquire should activate obligation checking");
        assert!(!verification.passed, "{verification:#?}");
        assert!(verification.obligations.iter().any(|obligation| {
            !obligation.satisfied()
                && obligation
                    .id
                    .contains("Holder.leak:obligation-leak:method-body")
        }));
        assert!(verification.obligations.iter().all(|obligation| {
            !obligation
                .id
                .contains("Holder.__init__:obligation-level-postcondition")
        }));

        let rebound = r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import Level as L, WaitLevel as W

class ObjectLock(Lock[object]):
    pass

class Holder:
    def __init__(self) -> None:
        self.lock = ObjectLock(object())
        self.lock = object()

    def ordinary(self) -> None:
        Requires(W() < L(self.lock))
        self.lock.acquire()
"#;
        let verification =
            verify_obligation_module_with_intrinsics(rebound, "rebound_lock_field.py", &bindings)
                .expect("rebound field should remain ordinary")
                .expect("level predicate should activate only level checking");
        assert!(verification.passed, "{verification:#?}");
        assert!(verification.obligations.iter().all(|obligation| {
            !obligation
                .id
                .contains("Holder.ordinary:obligation-leak:method-body")
        }));
    }

    #[test]
    fn failed_acquire_still_transfers_a_release_obligation_to_the_continuation() {
        let source = r#"from nagini_contracts.lock import Lock
from nagini_contracts.obligations import Level as L, WaitLevel as W

def acquire_then_release(lock: Lock[object]) -> None:
    lock.acquire()
    lock.release()

def acquire_without_release(lock: Lock[object]) -> None:
    lock.acquire()
"#;
        let bindings = resolved_level_bindings("L", "W");
        let verification =
            verify_obligation_module_with_intrinsics(source, "failed_acquire.py", &bindings)
                .expect("canonical lock calls should lower")
                .expect("lock calls should activate obligation checking");

        assert!(verification.obligations.iter().any(|obligation| {
            !obligation.satisfied()
                && obligation
                    .id
                    .contains("acquire_then_release:call-precondition")
        }));
        assert!(verification.obligations.iter().all(|obligation| {
            !obligation
                .id
                .contains("acquire_then_release:obligation-release-precondition")
                && !obligation
                    .id
                    .contains("acquire_then_release:obligation-leak:method-body")
        }));
        assert!(verification.obligations.iter().any(|obligation| {
            !obligation.satisfied()
                && obligation
                    .id
                    .contains("acquire_without_release:obligation-leak:method-body")
        }));
    }
}
