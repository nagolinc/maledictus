use std::fs;

use maledictus::typescript::{
    TypeScriptFailure, TypeScriptOutcomeGraph, verify_closed_javascript_module,
    verify_closed_module,
};

fn verify_typescript(
    source: &str,
    symbols: &[&str],
) -> Result<maledictus::typescript::TypeScriptVerification, TypeScriptFailure> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("terminal_switch.ts");
    fs::write(&path, source).unwrap();
    verify_closed_module(
        &path,
        &symbols
            .iter()
            .map(|symbol| (*symbol).to_owned())
            .collect::<Vec<_>>(),
    )
}

fn verify_javascript(source: &str, symbols: &[&str]) -> Result<(), TypeScriptFailure> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("terminal_switch.js");
    fs::write(&path, source).unwrap();
    verify_closed_javascript_module(
        &path,
        &symbols
            .iter()
            .map(|symbol| (*symbol).to_owned())
            .collect::<Vec<_>>(),
    )
    .map(|_| ())
}

#[test]
fn typescript_proves_exhaustive_terminal_string_switch() {
    verify_typescript(
        "export function route(kind: string): number {\n  switch (kind) {\n    case \"create\": return 1;\n    case \"delete\": return 2;\n    default: return 0;\n  }\n}\nexport function enabled(flag: boolean): number {\n  switch (flag) {\n    case true: return 1;\n    default: return 0;\n  }\n}\n",
        &["route", "enabled"],
    )
    .unwrap();
}

#[test]
fn typescript_switches_on_a_provenance_bound_record_field() {
    verify_typescript(
        "interface Request { readonly kind: string; readonly value: number; }\nfunction dispatch(request: Request): number {\n  switch (request.kind) {\n    case \"read\": return request.value;\n    default: throw \"unsupported\";\n  }\n}\nexport function safe(kind: string, value: number): number {\n  try { return dispatch({ kind, value } as const satisfies Request); } catch { return 0; }\n}\n",
        &["safe"],
    )
    .unwrap();
}

#[test]
fn check_js_proves_numeric_switch_with_terminal_arm_preludes() {
    verify_javascript(
        "/** @param {number} code @returns {number} */\nfunction dispatch(code) {\n  switch (code) {\n    case 1: { const offset = 2; return code + offset; }\n    default: throw \"unsupported\";\n  }\n}\n/** @param {number} code @returns {number} */\nexport function safe(code) { try { return dispatch(code); } catch { return 0; } }\n",
        &["safe"],
    )
    .unwrap();
}

#[test]
fn source_call_discriminant_is_recorded_once_before_switch_arms() {
    let proof = verify_typescript(
        "function classify(flag: boolean): string { if (!flag) { throw \"disabled\"; } return \"ready\"; }\nexport function safe(flag: boolean): number {\n  try {\n    switch (classify(flag)) {\n      case \"ready\": return 1;\n      default: return 0;\n    }\n  } catch { return -1; }\n}\n",
        &["safe"],
    )
    .unwrap();
    let safe = proof
        .functions
        .iter()
        .find(|function| function.name == "safe")
        .unwrap();
    assert_eq!(safe.calls, ["classify"]);
    let TypeScriptOutcomeGraph::Sequence { items } = &safe.outcome_graph else {
        panic!("function body must retain its source sequence")
    };
    let TypeScriptOutcomeGraph::TryCatch { try_body, .. } = &items[0] else {
        panic!("outer catch must remain explicit")
    };
    let TypeScriptOutcomeGraph::Sequence { items } = try_body.as_ref() else {
        panic!("try block must retain its source sequence")
    };
    let TypeScriptOutcomeGraph::TerminalSwitch { discriminant, .. } = &items[0] else {
        panic!("switch must remain a typed bridge node")
    };
    let TypeScriptOutcomeGraph::Sequence { items } = discriminant.as_ref() else {
        panic!("call expression must preserve argument-before-call sequence")
    };
    assert_eq!(
        items
            .iter()
            .filter(|item| matches!(item, TypeScriptOutcomeGraph::Call { .. }))
            .count(),
        1
    );
}

#[test]
fn terminal_switch_refuses_missing_multiple_or_nonfinal_default() {
    for source in [
        "export function observe(kind: string): void { switch (kind) { case \"x\": return; } }\n",
        "export function observe(kind: string): void { switch (kind) { default: return; case \"x\": return; } }\n",
        "export function observe(kind: string): void { switch (kind) { case \"x\": return; default: return; default: return; } }\n",
    ] {
        assert!(verify_typescript(source, &["observe"]).is_err());
    }
}

#[test]
fn terminal_switch_refuses_empty_fallthrough_break_and_continuation() {
    for source in [
        "export function observe(kind: string): void { switch (kind) { case \"x\": case \"y\": return; default: return; } }\n",
        "export function observe(kind: string): void { switch (kind) { case \"x\": break; default: return; } }\n",
        "export function observe(kind: string): void { switch (kind) { case \"x\": return; default: return; } return; }\n",
    ] {
        assert!(verify_typescript(source, &["observe"]).is_err());
    }
}

#[test]
fn terminal_switch_refuses_dynamic_property_and_effectful_case_labels() {
    for source in [
        "const key = \"x\"; export function route(kind: string): number { switch (kind) { case key: return 1; default: return 0; } }\n",
        "function key(): string { return \"x\"; } export function route(kind: string): number { switch (kind) { case key(): return 1; default: return 0; } }\n",
        "export function route(kind: string): number { const keys = { x: \"x\" }; switch (kind) { case keys.x: return 1; default: return 0; } }\n",
    ] {
        assert!(verify_typescript(source, &["route"]).is_err());
    }
}

#[test]
fn terminal_switch_refuses_duplicate_cross_type_and_nonfinite_labels() {
    for source in [
        "export function route(kind: string): number { switch (kind) { case \"x\": return 1; case \"x\": return 2; default: return 0; } }\n",
        "export function route(kind: string): number { switch (kind) { case 1: return 1; default: return 0; } }\n",
        "export function route(code: number): number { switch (code) { case 1e400: return 1; default: return 0; } }\n",
    ] {
        assert!(verify_typescript(source, &["route"]).is_err());
    }
}

#[test]
fn terminal_switch_refuses_mutation_var_and_cross_arm_binding_escape() {
    for source in [
        "export function route(kind: string): number { let result = 0; switch (kind) { case \"x\": result = 1; return result; default: return result; } }\n",
        "export function route(kind: string): number { switch (kind) { case \"x\": var value = 1; return value; default: return 0; } }\n",
        "export function route(kind: string): number { switch (kind) { case \"x\": { const value = 1; return value; } default: return value; } }\n",
    ] {
        assert!(verify_typescript(source, &["route"]).is_err());
    }
}

#[test]
fn terminal_switch_refuses_nonprimitive_discriminants_and_unmodeled_control_flow() {
    for source in [
        "export function route(values: readonly number[]): number { switch (values) { case values: return 1; default: return 0; } }\n",
        "export function route(kind: string): number { switch (kind) { case \"x\": while (true) { return 1; } default: return 0; } }\n",
    ] {
        assert!(verify_typescript(source, &["route"]).is_err());
    }
}
