use std::fs;

use maledictus::typescript::{
    TypeScriptFailure, verify_closed_javascript_module, verify_closed_module,
};

fn verify_typescript(source: &str, symbols: &[&str]) -> Result<(), TypeScriptFailure> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("outcomes.ts");
    fs::write(&path, source).unwrap();
    verify_closed_module(
        &path,
        &symbols
            .iter()
            .map(|symbol| (*symbol).to_owned())
            .collect::<Vec<_>>(),
    )
    .map(|_| ())
}

fn verify_javascript(source: &str, symbols: &[&str]) -> Result<(), TypeScriptFailure> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("outcomes.js");
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
fn typescript_catches_a_conditional_primitive_throw() {
    verify_typescript(
        "export function safe(flag: boolean, value: number): number {\n  try {\n    if (flag) { throw \"rejected\"; }\n    return value;\n  } catch {\n    return 0;\n  }\n}\n",
        &["safe"],
    )
    .unwrap();

    verify_typescript(
        "export function observe(flag: boolean): void {\n  try {\n    if (flag) { throw 1; }\n  } catch {}\n}\n",
        &["observe"],
    )
    .unwrap();
}

#[test]
fn check_js_catches_a_primitive_throw_with_an_unused_opaque_binding() {
    verify_javascript(
        "/** @param {boolean} flag @param {number} value @returns {number} */\nexport function safe(flag, value) {\n  try {\n    if (flag) { throw false; }\n    return value;\n  } catch (error) {\n    return 0;\n  }\n}\n",
        &["safe"],
    )
    .unwrap();
}

#[test]
fn requested_wrapper_catches_a_throwing_source_helper() {
    verify_typescript(
        "function maybe(flag: boolean): number {\n  if (flag) { throw 7; }\n  return 2;\n}\nexport function safe(flag: boolean): number {\n  try { return maybe(flag); } catch { return 0; }\n}\n",
        &["safe"],
    )
    .unwrap();
}

#[test]
fn outer_catch_closes_nested_acyclic_source_call_outcomes() {
    verify_typescript(
        "function maybe(flag: boolean): number {\n  if (flag) { throw \"bad\"; }\n  return 3;\n}\nfunction forward(flag: boolean): number { return maybe(flag); }\nexport function safe(flag: boolean): number {\n  try { return forward(flag); } catch { return 0; }\n}\n",
        &["safe"],
    )
    .unwrap();
}

#[test]
fn uncaught_direct_throw_refuses_at_the_throw_site() {
    let failure = verify_typescript(
        "export function unsafe(flag: boolean): number {\n  if (flag) { throw \"bad\"; }\n  return 1;\n}\n",
        &["unsafe"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-exception");
    assert_eq!(failure.line, Some(2));
    assert_eq!(failure.column, Some(15));
}

#[test]
fn uncaught_helper_outcome_refuses_at_the_requested_call_site() {
    let failure = verify_typescript(
        "function maybe(flag: boolean): number {\n  if (flag) { throw 4; }\n  return 1;\n}\nexport function unsafe(flag: boolean): number {\n  return maybe(flag);\n}\n",
        &["unsafe"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-exception");
    assert_eq!(failure.line, Some(6));
    assert_eq!(failure.column, Some(10));

    let failure = verify_typescript(
        "function first(): number { throw 1; }\nfunction second(): number { throw 2; }\nfunction consume(left: number, right: number): number { return left + right; }\nexport function unsafe(): number {\n  return consume(first(), second());\n}\n",
        &["unsafe"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-exception");
    assert_eq!(failure.line, Some(5));
    assert_eq!(failure.column, Some(18));
}

#[test]
fn catch_rethrow_remains_an_uncaught_typed_outcome() {
    let failure = verify_typescript(
        "export function unsafe(flag: boolean): number {\n  try {\n    if (flag) { throw \"first\"; }\n    return 1;\n  } catch {\n    throw \"second\";\n  }\n}\n",
        &["unsafe"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-exception");
    assert_eq!(failure.line, Some(6));
}

#[test]
fn finally_fallthrough_preserves_try_and_catch_outcomes() {
    verify_typescript(
        "export function closed(flag: boolean): number { try { if (flag) { throw 1; } return 2; } catch { return 3; } finally {} }\n",
        &["closed"],
    )
    .unwrap();

    let failure = verify_typescript(
        "export function open(flag: boolean): number { try { if (flag) { throw 1; } return 2; } finally {} }\n",
        &["open"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-exception");
    assert_eq!(failure.line, Some(1));
}

#[test]
fn abrupt_finally_overrides_every_protected_outcome() {
    verify_typescript(
        "export function overridesThrow(): number { try { throw 1; } finally { return 4; } }\n",
        &["overridesThrow"],
    )
    .unwrap();

    let failure = verify_typescript(
        "export function overridesReturn(): number { try { return 4; } finally { throw \"final\"; } }\n",
        &["overridesReturn"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-exception");
    assert_eq!(failure.line, Some(1));
}

#[test]
fn javascript_finally_uses_the_same_closed_outcome_composition() {
    verify_javascript(
        "/** @returns {number} */\nexport function closed() { try { throw 1; } finally { return 4; } }\n",
        &["closed"],
    )
    .unwrap();
}

#[test]
fn complex_or_effectful_thrown_values_refuse() {
    for (source, expected) in [
        (
            "function invalid(): number { throw { value: 1 }; }\n",
            "frontend.typescript.expression-unsupported",
        ),
        (
            "function invalid(): number { throw new Error(\"bad\"); }\n",
            "frontend.typescript.expression-unsupported",
        ),
        (
            "function value(): number { return 1; }\nfunction invalid(): number { throw value(); }\n",
            "frontend.typescript.throw-expression-effect-unsupported",
        ),
        (
            "function invalid(value: any): number { throw value; }\n",
            "frontend.typescript.collection-type-unsupported",
        ),
    ] {
        let failure = verify_typescript(source, &[]).unwrap_err();
        assert_eq!(failure.code, expected, "unexpected refusal for {source}");
    }
}

#[test]
fn catch_values_and_callback_effects_are_not_invented_as_typed_or_total() {
    for (source, expected) in [
        (
            "function invalid(flag: boolean): number { try { if (flag) { throw \"bad\"; } return 1; } catch (error) { return error === \"bad\" ? 2 : 3; } }\n",
            "frontend.typescript.catch-binding-use-unsupported",
        ),
        (
            "function invalid(flag: boolean): number { try { if (flag) { throw \"bad\"; } return 1; } catch ([error]) { return 2; } }\n",
            "frontend.typescript.strict-typecheck",
        ),
        (
            "function invalid(callback: (value: number) => number, value: number): number { try { return callback(value); } catch { return 0; } }\n",
            "frontend.typescript.callback-boundary-unsupported",
        ),
    ] {
        let failure = verify_typescript(source, &[]).unwrap_err();
        assert_eq!(failure.code, expected, "unexpected refusal for {source}");
    }
}
