use std::fs;

use maledictus::typescript::{
    TypeScriptFailure, TypeScriptOutcomeGraph, TypeScriptParameterDescriptor,
    verify_closed_javascript_module, verify_closed_module,
};

fn verify_typescript(
    source: &str,
    symbols: &[&str],
) -> Result<maledictus::typescript::TypeScriptVerification, TypeScriptFailure> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("callbacks.ts");
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
    let path = directory.path().join("callbacks.js");
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
fn typescript_composes_a_same_module_source_callback() {
    let proof = verify_typescript(
        concat!(
            "function increment(value: number): number { return value + 1; }\n",
            "function apply(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            "export function run(value: number): number { return apply(increment, value); }\n",
        ),
        &["run"],
    )
    .unwrap();

    let apply = proof
        .functions
        .iter()
        .find(|function| function.name == "apply")
        .unwrap();
    assert!(matches!(
        apply.parameters[0].descriptor,
        TypeScriptParameterDescriptor::Callback { .. }
    ));
    assert!(graph_contains_callback_invoke(&apply.outcome_graph));
    let run = proof
        .functions
        .iter()
        .find(|function| function.name == "run")
        .unwrap();
    assert_eq!(run.calls, ["apply", "increment"]);
}

#[test]
fn checkjs_composes_a_same_module_source_callback() {
    verify_javascript(
        concat!(
            "/** @param {number} value @returns {number} */\n",
            "function increment(value) { return value + 1; }\n",
            "/** @param {(value: number) => number} callback @param {number} value @returns {number} */\n",
            "function apply(callback, value) { return callback(value); }\n",
            "/** @param {number} value @returns {number} */\n",
            "export function run(value) { return apply(increment, value); }\n",
        ),
        &["run"],
    )
    .unwrap();
}

#[test]
fn callback_raises_are_composed_and_may_be_closed_by_catch() {
    verify_typescript(
        concat!(
            "function maybe(value: number): number { if (value < 0) { throw \"negative\"; } return value; }\n",
            "function apply(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            "export function safe(value: number): number { try { return apply(maybe, value); } catch { return 0; } }\n",
        ),
        &["safe"],
    )
    .unwrap();

    let failure = verify_typescript(
        concat!(
            "function maybe(value: number): number { if (value < 0) { throw \"negative\"; } return value; }\n",
            "function apply(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            "export function unsafe(value: number): number { return apply(maybe, value); }\n",
        ),
        &["unsafe"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-exception");
    assert_eq!(failure.line, Some(3));
}

#[test]
fn repeated_callback_invocation_composes_each_effectful_call() {
    verify_typescript(
        concat!(
            "function increment(value: number): number { return value + 1; }\n",
            "function twice(callback: (value: number) => number, value: number): number { return callback(callback(value)); }\n",
            "export function run(value: number): number { return twice(increment, value); }\n",
        ),
        &["run"],
    )
    .unwrap();
}

#[test]
fn abstract_and_exported_callback_boundaries_remain_refused() {
    for (source, symbols) in [
        (
            "export function apply(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            vec!["apply"],
        ),
        (
            "function apply(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            vec!["apply"],
        ),
    ] {
        let failure = verify_typescript(source, &symbols).unwrap_err();
        assert_eq!(
            failure.code,
            "frontend.typescript.callback-boundary-unsupported"
        );
    }
}

#[test]
fn callback_actual_requires_exact_source_function_provenance() {
    for source in [
        concat!(
            "function apply(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            "export function run(value: number): number { return apply(Math.abs, value); }\n",
        ),
        concat!(
            "function apply(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            "export function run(value: number): number { return apply(item => item + 1, value); }\n",
        ),
        concat!(
            "function second(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            "function first(callback: (value: number) => number, value: number): number { return second(callback, value); }\n",
            "function increment(value: number): number { return value + 1; }\n",
            "export function run(value: number): number { return first(increment, value); }\n",
        ),
    ] {
        let failure = verify_typescript(source, &["run"]).unwrap_err();
        assert_eq!(
            failure.code, "frontend.typescript.callback-argument-provenance",
            "{source}"
        );
    }
}

#[test]
fn callback_values_cannot_escape_be_stored_or_be_reassigned() {
    for source in [
        concat!(
            "function apply(callback: (value: number) => number, value: number): number { const copy = callback; return copy(value); }\n",
            "function increment(value: number): number { return value + 1; }\n",
            "export function run(value: number): number { return apply(increment, value); }\n",
        ),
        concat!(
            "function increment(value: number): number { return value + 1; }\n",
            "function apply(callback: (value: number) => number, value: number): number { callback = increment; return callback(value); }\n",
            "export function run(value: number): number { return apply(increment, value); }\n",
        ),
        concat!(
            "function apply(callback: (value: number) => number, value: number): number { const holder = { callback }; return holder.callback(value); }\n",
            "function increment(value: number): number { return value + 1; }\n",
            "export function run(value: number): number { return apply(increment, value); }\n",
        ),
    ] {
        assert!(verify_typescript(source, &["run"]).is_err(), "{source}");
    }
}

#[test]
fn generic_optional_rest_method_and_async_callbacks_remain_refused() {
    for source in [
        "function invalid(callback: <T>(value: T) => T, value: number): number { return callback(value); }\n",
        "function invalid(callback: (value?: number) => number, value: number): number { return callback(value); }\n",
        "function invalid(callback: (...values: number[]) => number, value: number): number { return callback(value); }\n",
        concat!(
            "function apply(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            "const holder = { increment(value: number): number { return value + 1; } };\n",
            "export function run(value: number): number { return apply(holder.increment, value); }\n",
        ),
        concat!(
            "function apply(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            "async function increment(value: number): Promise<number> { return value + 1; }\n",
            "export function run(value: number): number { return apply(increment, value); }\n",
        ),
    ] {
        assert!(verify_typescript(source, &["run"]).is_err(), "{source}");
    }
}

#[test]
fn callback_edges_participate_in_cycle_detection() {
    let failure = verify_typescript(
        concat!(
            "function apply(callback: (value: number) => number, value: number): number { return callback(value); }\n",
            "function loop(value: number): number { return apply(loop, value); }\n",
            "export function run(value: number): number { return apply(loop, value); }\n",
        ),
        &["run"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.call-cycle-unsupported");
}

fn graph_contains_callback_invoke(graph: &TypeScriptOutcomeGraph) -> bool {
    match graph {
        TypeScriptOutcomeGraph::CallbackInvoke { .. } => true,
        TypeScriptOutcomeGraph::Sequence { items } => {
            items.iter().any(graph_contains_callback_invoke)
        }
        TypeScriptOutcomeGraph::Branch { branches } => {
            branches.iter().any(graph_contains_callback_invoke)
        }
        TypeScriptOutcomeGraph::TryCatch {
            try_body,
            catch_body,
        } => graph_contains_callback_invoke(try_body) || graph_contains_callback_invoke(catch_body),
        TypeScriptOutcomeGraph::TryFinally { body, finally_body } => {
            graph_contains_callback_invoke(body) || graph_contains_callback_invoke(finally_body)
        }
        TypeScriptOutcomeGraph::TerminalSwitch {
            discriminant,
            cases,
            default_body,
            ..
        } => {
            graph_contains_callback_invoke(discriminant)
                || cases
                    .iter()
                    .any(|case| graph_contains_callback_invoke(&case.body))
                || graph_contains_callback_invoke(default_body)
        }
        TypeScriptOutcomeGraph::Fallthrough
        | TypeScriptOutcomeGraph::Return { .. }
        | TypeScriptOutcomeGraph::Raise { .. }
        | TypeScriptOutcomeGraph::Call { .. }
        | TypeScriptOutcomeGraph::AwaitCall { .. }
        | TypeScriptOutcomeGraph::PromiseAdopt { .. } => false,
    }
}
