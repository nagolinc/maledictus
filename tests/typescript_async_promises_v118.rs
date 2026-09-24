use std::fs;

use maledictus::typescript::{
    TypeScriptExecution, TypeScriptFailure, TypeScriptOutcomeGraph,
    verify_closed_javascript_module, verify_closed_module,
};

fn verify_typescript(
    source: &str,
    symbols: &[&str],
) -> Result<maledictus::typescript::TypeScriptVerification, TypeScriptFailure> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("async.ts");
    fs::write(&path, source).unwrap();
    verify_closed_module(
        &path,
        &symbols
            .iter()
            .map(|symbol| (*symbol).to_owned())
            .collect::<Vec<_>>(),
    )
}

fn verify_javascript(
    source: &str,
    symbols: &[&str],
) -> Result<maledictus::typescript::TypeScriptVerification, TypeScriptFailure> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("async.js");
    fs::write(&path, source).unwrap();
    verify_closed_javascript_module(
        &path,
        &symbols
            .iter()
            .map(|symbol| (*symbol).to_owned())
            .collect::<Vec<_>>(),
    )
}

#[test]
fn async_returns_are_typed_as_fulfillments_and_direct_source_await_composes() {
    let proof = verify_typescript(
        concat!(
            "async function increment(value: number): Promise<number> { return value + 1; }\n",
            "export async function run(value: number): Promise<number> { const next = await increment(value); return next; }\n",
        ),
        &["run"],
    )
    .unwrap();

    assert_eq!(proof.schema, "maledictus-typescript-closed-verification/v8");
    let increment = proof
        .functions
        .iter()
        .find(|function| function.name == "increment")
        .unwrap();
    assert_eq!(increment.execution, TypeScriptExecution::Asynchronous);
    assert_eq!(increment.return_type, "number");
    let run = proof
        .functions
        .iter()
        .find(|function| function.name == "run")
        .unwrap();
    assert!(graph_contains_await(&run.outcome_graph));
}

#[test]
fn checkjs_async_returns_and_awaits_use_the_same_closed_semantics() {
    let proof = verify_javascript(
        concat!(
            "/** @param {number} value @returns {Promise<number>} */\n",
            "async function increment(value) { return value + 1; }\n",
            "/** @param {number} value @returns {Promise<number>} */\n",
            "export async function run(value) { return await increment(value); }\n",
        ),
        &["run"],
    )
    .unwrap();
    assert_eq!(proof.schema, "maledictus-javascript-closed-verification/v8");
}

#[test]
fn awaited_rejection_is_catchable_but_uncaught_rejection_refuses() {
    verify_typescript(
        concat!(
            "async function maybe(value: number): Promise<number> { if (value < 0) { throw \"negative\"; } return value; }\n",
            "export async function safe(value: number): Promise<number> { try { return await maybe(value); } catch { return 0; } }\n",
        ),
        &["safe"],
    )
    .unwrap();

    let failure = verify_typescript(
        concat!(
            "async function maybe(value: number): Promise<number> { if (value < 0) { throw \"negative\"; } return value; }\n",
            "export async function unsafe(value: number): Promise<number> { return await maybe(value); }\n",
        ),
        &["unsafe"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-rejection");
    assert_eq!(failure.line, Some(2));
}

#[test]
fn returning_a_source_promise_adopts_rejection_without_making_it_catchable() {
    let failure = verify_typescript(
        concat!(
            "async function maybe(value: number): Promise<number> { if (value < 0) { throw \"negative\"; } return value; }\n",
            "export async function run(value: number): Promise<number> { try { return maybe(value); } catch { return 0; } }\n",
        ),
        &["run"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-rejection");
    assert_eq!(failure.line, Some(2));

    let proof = verify_typescript(
        concat!(
            "async function increment(value: number): Promise<number> { return value + 1; }\n",
            "export async function run(value: number): Promise<number> { return increment(value); }\n",
        ),
        &["run"],
    )
    .unwrap();
    let run = proof
        .functions
        .iter()
        .find(|function| function.name == "run")
        .unwrap();
    assert!(graph_contains_adoption(&run.outcome_graph));
}

#[test]
fn awaiting_a_synchronous_source_call_preserves_catchable_throw_semantics() {
    verify_typescript(
        concat!(
            "function maybe(value: number): number { if (value < 0) { throw \"negative\"; } return value; }\n",
            "export async function safe(value: number): Promise<number> { try { return await maybe(value); } catch { return 0; } }\n",
        ),
        &["safe"],
    )
    .unwrap();
}

#[test]
fn async_functions_preserve_the_frozen_terminal_switch_fragment() {
    verify_typescript(
        "export async function route(kind: string): Promise<number> { switch (kind) { case \"x\": return 1; default: return 0; } }\n",
        &["route"],
    )
    .unwrap();
}

#[test]
fn unknown_promises_thenables_combinators_and_floating_async_calls_refuse() {
    for source in [
        "export async function run(value: Promise<number>): Promise<number> { return await value; }\n",
        "export async function run(): Promise<number> { return await Promise.resolve(1); }\n",
        "export async function run(): Promise<number> { const values = await Promise.all([Promise.resolve(1)]); return values[0]; }\n",
        concat!(
            "async function helper(): Promise<number> { return 1; }\n",
            "export async function run(): Promise<number> { helper(); return 0; }\n",
        ),
        "export async function run(): Promise<number> { return new Promise(resolve => resolve(1)); }\n",
    ] {
        assert!(verify_typescript(source, &["run"]).is_err(), "{source}");
    }
}

#[test]
fn async_call_edges_participate_in_cycle_detection() {
    for source in [
        concat!(
            "async function first(value: number): Promise<number> { return await second(value); }\n",
            "async function second(value: number): Promise<number> { return await first(value); }\n",
            "export async function run(value: number): Promise<number> { return await first(value); }\n",
        ),
        concat!(
            "async function first(value: number): Promise<number> { return second(value); }\n",
            "async function second(value: number): Promise<number> { return first(value); }\n",
            "export async function run(value: number): Promise<number> { return first(value); }\n",
        ),
    ] {
        let failure = verify_typescript(source, &["run"]).unwrap_err();
        assert_eq!(failure.code, "frontend.typescript.call-cycle-unsupported");
    }
}

fn graph_contains_await(graph: &TypeScriptOutcomeGraph) -> bool {
    graph_any(graph, &|item| {
        matches!(item, TypeScriptOutcomeGraph::AwaitCall { .. })
    })
}

fn graph_contains_adoption(graph: &TypeScriptOutcomeGraph) -> bool {
    graph_any(graph, &|item| {
        matches!(item, TypeScriptOutcomeGraph::PromiseAdopt { .. })
    })
}

fn graph_any(
    graph: &TypeScriptOutcomeGraph,
    predicate: &impl Fn(&TypeScriptOutcomeGraph) -> bool,
) -> bool {
    if predicate(graph) {
        return true;
    }
    match graph {
        TypeScriptOutcomeGraph::Sequence { items } => {
            items.iter().any(|item| graph_any(item, predicate))
        }
        TypeScriptOutcomeGraph::Branch { branches } => {
            branches.iter().any(|item| graph_any(item, predicate))
        }
        TypeScriptOutcomeGraph::TryCatch {
            try_body,
            catch_body,
        } => graph_any(try_body, predicate) || graph_any(catch_body, predicate),
        TypeScriptOutcomeGraph::TryFinally { body, finally_body } => {
            graph_any(body, predicate) || graph_any(finally_body, predicate)
        }
        TypeScriptOutcomeGraph::TerminalSwitch {
            discriminant,
            cases,
            default_body,
            ..
        } => {
            graph_any(discriminant, predicate)
                || cases.iter().any(|case| graph_any(&case.body, predicate))
                || graph_any(default_body, predicate)
        }
        TypeScriptOutcomeGraph::Fallthrough
        | TypeScriptOutcomeGraph::Return { .. }
        | TypeScriptOutcomeGraph::Raise { .. }
        | TypeScriptOutcomeGraph::Call { .. }
        | TypeScriptOutcomeGraph::AwaitCall { .. }
        | TypeScriptOutcomeGraph::PromiseAdopt { .. }
        | TypeScriptOutcomeGraph::CallbackInvoke { .. } => false,
    }
}
