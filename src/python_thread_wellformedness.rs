//! Source-bound well-formedness rules for Nagini's thread API.
//!
//! This facade coordinates three focused passes: import/declaration collection, function-body
//! traversal, and validation of thread-specific calls. None inspect fixture comments or classify
//! unrelated methods merely because they happen to be named `start` or `join`.

mod bindings;
mod calls;
mod expressions;
mod sif;
mod traversal;

use std::collections::{BTreeMap, BTreeSet};

use rustpython_parser::ast;

use bindings::{collect_catalog, collect_final_bindings};
use sif::validate_sif_concurrency;
use traversal::validate_function;

use crate::python_contract_positions::InformationFlowVerificationProfile;

pub const INVALID_THREAD_CREATION: &str = "invalid.program:invalid.thread.creation";
pub const INVALID_THREAD_START: &str = "invalid.program:invalid.thread.start";
pub const INVALID_THREAD_JOIN: &str = "invalid.program:invalid.thread.join";
pub const INVALID_GET_METHOD_USE: &str = "invalid.program:invalid.get.method.use";
pub const INVALID_ARG_USE: &str = "invalid.program:invalid.arg.use";
pub const CONCURRENCY_IN_SIF: &str = "invalid.program:concurrency.in.sif";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ThreadWellformednessFailure {
    pub code: &'static str,
    pub message: String,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ThreadSymbol {
    Thread,
    GetMethod,
    GetOld,
    Arg,
}

#[derive(Clone, Default)]
struct Bindings {
    thread_names: BTreeMap<String, ThreadSymbol>,
    thread_modules: BTreeSet<String>,
    pure_names: BTreeSet<String>,
    predicate_names: BTreeSet<String>,
    ensures_names: BTreeSet<String>,
    contract_modules: BTreeSet<String>,
    obligation_names: BTreeSet<String>,
    obligation_modules: BTreeSet<String>,
    contracts_star: bool,
    obligations_star: bool,
}

#[derive(Clone, Debug)]
struct FunctionInfo {
    pure: bool,
    predicate: bool,
    positional_count: usize,
    required_count: usize,
    has_obligation_postcondition: bool,
}

#[derive(Clone, Default)]
struct Catalog {
    functions: BTreeMap<String, FunctionInfo>,
    methods: BTreeMap<String, BTreeMap<String, FunctionInfo>>,
    classes: BTreeSet<String>,
}

#[derive(Clone, Default)]
struct FunctionContext {
    local_names: BTreeSet<String>,
    thread_locals: BTreeSet<String>,
    nominal_locals: BTreeMap<String, String>,
}

#[derive(Clone, Copy)]
struct Candidate {
    code: &'static str,
    message: &'static str,
    byte_offset: u32,
}

pub(crate) fn validate_thread_suite(
    suite: &ast::Suite,
    source: &str,
    information_flow: InformationFlowVerificationProfile,
) -> Result<(), ThreadWellformednessFailure> {
    let bindings = collect_final_bindings(suite);
    let catalog = collect_catalog(suite, &bindings);
    let mut candidates = Vec::new();
    validate_sif_concurrency(suite, information_flow, &mut candidates);
    for statement in suite {
        match statement {
            ast::Stmt::FunctionDef(function) => {
                validate_function(function, &bindings, &catalog, &mut candidates, None)
            }
            ast::Stmt::ClassDef(class) => {
                for item in &class.body {
                    if let ast::Stmt::FunctionDef(function) = item {
                        validate_function(
                            function,
                            &bindings,
                            &catalog,
                            &mut candidates,
                            Some(class.name.as_str()),
                        );
                    }
                }
            }
            _ => {}
        }
    }
    let Some(candidate) = candidates
        .into_iter()
        .min_by_key(|candidate| candidate.byte_offset)
    else {
        return Ok(());
    };
    let offset = usize::try_from(candidate.byte_offset)
        .unwrap_or(source.len())
        .min(source.len());
    let prefix = &source[..offset];
    Err(ThreadWellformednessFailure {
        code: candidate.code,
        message: candidate.message.to_owned(),
        byte_offset: candidate.byte_offset,
        line: u32::try_from(prefix.bytes().filter(|byte| *byte == b'\n').count() + 1)
            .unwrap_or(u32::MAX),
        column: u32::try_from(
            prefix
                .rsplit_once('\n')
                .map_or(prefix.len(), |(_, suffix)| suffix.len())
                + 1,
        )
        .unwrap_or(u32::MAX),
    })
}
