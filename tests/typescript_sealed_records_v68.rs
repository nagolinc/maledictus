use std::fs;

use maledictus::typescript::{
    TypeScriptFailure, verify_closed_javascript_module, verify_closed_module,
};

fn verify_typescript(source: &str, symbols: &[&str]) -> Result<(), TypeScriptFailure> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("records.ts");
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
    let path = directory.path().join("records.js");
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
fn typescript_proves_inferred_const_record_direct_reads() {
    verify_typescript(
        "export function total(left: number, right: number): number {\n  const point = { left, right };\n  return point.left + point.right;\n}\n",
        &["total"],
    )
    .unwrap();
}

#[test]
fn typescript_proves_exact_readonly_interface_and_satisfies() {
    verify_typescript(
        "interface Point { readonly left: number; readonly right: number; }\nfunction total(point: Readonly<{ left: number; right: number }>): number { return point.left + point.right; }\nexport function measure(left: number, right: number): number {\n  const point = { left, right } as const satisfies Point;\n  return total(point);\n}\n",
        &["measure"],
    )
    .unwrap();
}

#[test]
fn typescript_sequences_record_initializers_and_catches_helper_throw() {
    verify_typescript(
        "type Request = { readonly enabled: boolean; readonly value: number };\nfunction prepareEnabled(enabled: boolean): boolean { if (!enabled) { throw \"disabled\"; } return true; }\nfunction prepareValue(value: number): number { return value; }\nfunction inspect(request: Request): number { return request.value; }\nexport function safe(enabled: boolean, value: number): number {\n  try {\n    const request = { enabled: prepareEnabled(enabled), value: prepareValue(value) } as const satisfies Request;\n    return inspect(request);\n  } catch { return 0; }\n}\n",
        &["safe"],
    )
    .unwrap();
}

#[test]
fn check_js_proves_source_record_passed_to_private_jsdoc_helper() {
    verify_javascript(
        "/** @param {{left: number, right: number}} point @returns {number} */\nfunction total(point) { return point.left + point.right; }\n/** @param {number} left @param {number} right @returns {number} */\nexport function measure(left, right) {\n  const point = { left, right };\n  return total(point);\n}\n",
        &["measure"],
    )
    .unwrap();
}

#[test]
fn records_refuse_structural_parameters_at_requested_or_exported_boundaries() {
    for source in [
        "interface Point { readonly x: number; }\nexport function read(point: Point): number { return point.x; }\n",
        "interface Point { readonly x: number; }\nfunction read(point: Point): number { return point.x; }\n",
    ] {
        let failure = verify_typescript(source, &["read"]).unwrap_err();
        assert_eq!(
            failure.code,
            "frontend.typescript.record-boundary-unsupported"
        );
    }
}

#[test]
fn records_refuse_getters_setters_methods_computed_and_spread_properties() {
    for source in [
        "export function read(): number { const item = { get x(): number { return 1; } }; return item.x; }\n",
        "export function read(): number { const item = { x(): number { return 1; } }; return 1; }\n",
        "export function read(key: string): number { const item = { [key]: 1 }; return 1; }\n",
        "export function read(): number { const base = { x: 1 }; const item = { ...base, y: 2 }; return item.y; }\n",
        "export function read(): number { const item = new Proxy({ x: 1 }, {}); return item.x; }\n",
    ] {
        let failure = verify_typescript(source, &["read"]).unwrap_err();
        assert!(
            failure.code.contains("record-literal-shape-unsupported")
                || failure.code == "frontend.typescript.expression-unsupported"
        );
    }
}

#[test]
fn records_refuse_mutation_delete_and_destructuring() {
    for source in [
        "export function change(): number { const item = { x: 1 }; item.x = 2; return item.x; }\n",
        "export function change(): number { const item = { x: 1 }; item.x++; return item.x; }\n",
        "export function change(): number { const item = { x: 1 }; delete item.x; return 1; }\n",
        "export function change(): number { const item = { x: 1 }; const { x } = item; return x; }\n",
    ] {
        assert!(verify_typescript(source, &["change"]).is_err());
    }
}

#[test]
fn records_refuse_alias_escape_external_calls_and_parameter_forwarding() {
    for source in [
        "export function alias(): number { const item = { x: 1 }; const second = item; return second.x; }\n",
        "export function escape(): number { const item = { x: 1 }; JSON.stringify(item); return item.x; }\n",
        "interface Item { readonly x: number; }\nfunction second(item: Item): number { return item.x; }\nfunction first(item: Item): number { return second(item); }\nexport function root(): number { return first({ x: 1 }); }\n",
    ] {
        assert!(verify_typescript(source, &["root", "alias", "escape"]).is_err());
    }
}

#[test]
fn records_refuse_dynamic_optional_missing_and_prototype_reads() {
    for source in [
        "export function read(key: string): number { const item = { x: 1 }; return item[key] ?? 0; }\n",
        "export function read(): number { const item = { x: 1 }; return item?.x; }\n",
        "export function read(): number { const item = { x: 1 }; return item.y; }\n",
        "export function read(): number { const item = { x: 1 }; return item.toString().length; }\n",
    ] {
        assert!(verify_typescript(source, &["read"]).is_err());
    }
}

#[test]
fn records_refuse_optional_mutable_extended_generic_indexed_and_nested_types() {
    for source in [
        "interface Item { x: number; }\nfunction take(item: Item): number { return item.x; }\nexport function root(): number { return take({ x: 1 }); }\n",
        "interface Item { readonly x?: number; }\nfunction take(item: Item): number { return item.x ?? 0; }\nexport function root(): number { return take({}); }\n",
        "interface Base { readonly x: number; }\ninterface Item extends Base { readonly y: number; }\nexport function root(): number { return 1; }\n",
        "interface Item<T> { readonly x: T; }\nexport function root(): number { return 1; }\n",
        "interface Item { readonly [key: string]: number; }\nexport function root(): number { return 1; }\n",
        "interface Item { readonly nested: { readonly x: number }; }\nexport function root(): number { return 1; }\n",
    ] {
        assert!(verify_typescript(source, &["root"]).is_err());
    }
}
