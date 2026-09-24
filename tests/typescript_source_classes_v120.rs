use std::fs;

use maledictus::typescript::{
    TypeScriptExecution, TypeScriptFailure, verify_closed_javascript_module, verify_closed_module,
};

fn verify_typescript(
    source: &str,
    symbols: &[&str],
) -> Result<maledictus::typescript::TypeScriptVerification, TypeScriptFailure> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("classes.ts");
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
    let path = directory.path().join("classes.js");
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
fn immutable_source_class_fields_constructor_and_methods_compose() {
    let proof = verify_typescript(
        concat!(
            "class Offset {\n",
            "  readonly amount: number;\n",
            "  constructor(amount: number) { this.amount = amount; }\n",
            "  apply(value: number): number { return value + this.amount; }\n",
            "}\n",
            "export function run(value: number): number {\n",
            "  const offset = new Offset(2);\n",
            "  return offset.apply(value);\n",
            "}\n",
        ),
        &["run"],
    )
    .unwrap();

    assert_eq!(proof.schema, "maledictus-typescript-closed-verification/v8");
    assert_eq!(proof.classes.len(), 1);
    assert_eq!(proof.classes[0].name, "Offset");
    assert_eq!(proof.classes[0].constructor, "Offset.constructor");
    assert_eq!(proof.classes[0].methods, vec!["Offset.apply"]);
    assert!(
        proof
            .functions
            .iter()
            .any(|function| function.name == "Offset.constructor")
    );
    assert!(
        proof
            .functions
            .iter()
            .any(|function| function.name == "Offset.apply")
    );
}

#[test]
fn async_method_rejection_is_composed_at_the_await_site() {
    verify_typescript(
        concat!(
            "class Worker {\n",
            "  readonly floor: number;\n",
            "  constructor(floor: number) { this.floor = floor; }\n",
            "  async apply(value: number): Promise<number> {\n",
            "    if (value < this.floor) { throw \"low\"; }\n",
            "    return value;\n",
            "  }\n",
            "}\n",
            "export async function safe(value: number): Promise<number> {\n",
            "  const worker = new Worker(0);\n",
            "  try { return await worker.apply(value); } catch { return 0; }\n",
            "}\n",
        ),
        &["safe"],
    )
    .unwrap();

    let failure = verify_typescript(
        concat!(
            "class Worker {\n",
            "  readonly floor: number;\n",
            "  constructor(floor: number) { this.floor = floor; }\n",
            "  async apply(value: number): Promise<number> { if (value < this.floor) { throw \"low\"; } return value; }\n",
            "}\n",
            "export async function unsafe(value: number): Promise<number> {\n",
            "  const worker = new Worker(0);\n",
            "  return await worker.apply(value);\n",
            "}\n",
        ),
        &["unsafe"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-rejection");
}

#[test]
fn synchronous_method_raise_is_composed_at_the_direct_call_site() {
    verify_typescript(
        concat!(
            "class Worker { readonly id: number; constructor(id: number) { this.id = id; }\n",
            "  apply(value: number): number { if (value < 0) { throw \"low\"; } return value + this.id; } }\n",
            "export function safe(value: number): number { const worker = new Worker(1); try { return worker.apply(value); } catch { return 0; } }\n",
        ),
        &["safe"],
    )
    .unwrap();

    let failure = verify_typescript(
        concat!(
            "class Worker { readonly id: number; constructor(id: number) { this.id = id; }\n",
            "  apply(value: number): number { if (value < 0) { throw \"low\"; } return value + this.id; } }\n",
            "export function unsafe(value: number): number { const worker = new Worker(1); return worker.apply(value); }\n",
        ),
        &["unsafe"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-exception");
}

#[test]
fn constructor_raise_is_composed_at_the_new_expression() {
    verify_typescript(
        concat!(
            "class Checked { readonly value: number; constructor(value: number) { this.value = value; if (value < 0) { throw \"low\"; } } read(): number { return this.value; } }\n",
            "export function safe(value: number): number { try { const item = new Checked(value); return item.read(); } catch { return 0; } }\n",
        ),
        &["safe"],
    )
    .unwrap();

    let failure = verify_typescript(
        concat!(
            "class Checked { readonly value: number; constructor(value: number) { this.value = value; if (value < 0) { throw \"low\"; } } read(): number { return this.value; } }\n",
            "export function unsafe(value: number): number { const item = new Checked(value); return item.read(); }\n",
        ),
        &["unsafe"],
    )
    .unwrap_err();
    assert_eq!(failure.code, "frontend.typescript.unexpected-exception");
}

#[test]
fn checkjs_readonly_source_class_uses_the_same_closed_semantics() {
    let proof = verify_javascript(
        concat!(
            "class Offset {\n",
            "  /** @readonly @type {number} */\n",
            "  amount;\n",
            "  /** @param {number} amount */\n",
            "  constructor(amount) { this.amount = amount; }\n",
            "  /** @param {number} value @returns {number} */\n",
            "  apply(value) { return value + this.amount; }\n",
            "}\n",
            "/** @param {number} value @returns {number} */\n",
            "export function run(value) { const offset = new Offset(2); return offset.apply(value); }\n",
        ),
        &["run"],
    )
    .unwrap();
    assert_eq!(proof.schema, "maledictus-javascript-closed-verification/v8");
}

#[test]
fn unsafe_class_shapes_and_escapes_fail_closed() {
    let cases = [
        concat!(
            "class Base { readonly value: number; constructor(value: number) { this.value = value; } }\n",
            "class Child extends Base {}\n",
            "export function run(value: number): number { const child = new Child(value); return child.value; }\n",
        ),
        concat!(
            "class Mutable { value: number; constructor(value: number) { this.value = value; } }\n",
            "export function run(value: number): number { const item = new Mutable(value); return item.value; }\n",
        ),
        concat!(
            "class Item { readonly value: number; constructor(value: number) { this.value = value; } read(): number { return this.value; } }\n",
            "export function run(value: number): number { const item = new Item(value); item.value = 3; return item.read(); }\n",
        ),
        concat!(
            "class Item { readonly value: number; constructor(value: number) { this.value = value; } read(): number { return this.value; } }\n",
            "export function run(value: number): number { const item = new Item(value); const read = item.read; return read(); }\n",
        ),
        concat!(
            "class Item { readonly value: number; constructor(value: number) { this.value = value; } get read(): number { return this.value; } }\n",
            "export function run(value: number): number { const item = new Item(value); return item.read; }\n",
        ),
        concat!(
            "class Item<T> { readonly value: T; constructor(value: T) { this.value = value; } }\n",
            "export function run(value: number): number { const item = new Item(value); return item.value; }\n",
        ),
        concat!(
            "class Item { readonly value: number; constructor(value: number = 0) { this.value = value; } }\n",
            "export function run(value: number): number { const item = new Item(value); return item.value; }\n",
        ),
        concat!(
            "class Item { readonly value: number; constructor(...values: number[]) { this.value = values[0] ?? 0; } }\n",
            "export function run(value: number): number { const item = new Item(value); return item.value; }\n",
        ),
        concat!(
            "class Item { readonly value: number = 1; constructor() {} }\n",
            "export function run(): number { const item = new Item(); return item.value; }\n",
        ),
        concat!(
            "class Item { readonly value: number; constructor(value: number) { this.value = value; } static read(): number { return 1; } }\n",
            "export function run(value: number): number { const item = new Item(value); return item.value; }\n",
        ),
        concat!(
            "class Item { readonly left: number; readonly right: number; constructor(value: number) { this.left = value; this.right = this.left; } }\n",
            "export function run(value: number): number { const item = new Item(value); return item.right; }\n",
        ),
        "export function run(): number { const date = new Date(); return 1; }\n",
    ];
    for source in cases {
        assert!(
            verify_typescript(source, &["run"]).is_err(),
            "accepted unsafe class source:\n{source}"
        );
    }
}

#[test]
fn class_member_execution_metadata_is_preserved() {
    let proof = verify_typescript(
        concat!(
            "class Worker { readonly id: number; constructor(id: number) { this.id = id; } async get(): Promise<number> { return this.id; } }\n",
            "export async function run(): Promise<number> { const worker = new Worker(1); return worker.get(); }\n",
        ),
        &["run"],
    )
    .unwrap();
    let method = proof
        .functions
        .iter()
        .find(|function| function.name == "Worker.get")
        .unwrap();
    assert_eq!(method.execution, TypeScriptExecution::Asynchronous);
}
