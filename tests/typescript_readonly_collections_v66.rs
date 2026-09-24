use std::fs;

use maledictus::typescript::{verify_closed_javascript_module, verify_closed_module};

fn prove_typescript(source: &str, symbols: &[&str]) -> Result<(), String> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("collections.ts");
    fs::write(&path, source).unwrap();
    verify_closed_module(
        &path,
        &symbols
            .iter()
            .map(|symbol| (*symbol).to_owned())
            .collect::<Vec<_>>(),
    )
    .map(|_| ())
    .map_err(|failure| failure.code)
}

fn prove_javascript(source: &str, symbols: &[&str]) -> Result<(), String> {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("collections.js");
    fs::write(&path, source).unwrap();
    verify_closed_javascript_module(
        &path,
        &symbols
            .iter()
            .map(|symbol| (*symbol).to_owned())
            .collect::<Vec<_>>(),
    )
    .map(|_| ())
    .map_err(|failure| failure.code)
}

#[test]
fn typescript_proves_readonly_array_length_and_checked_index() {
    prove_typescript(
        "export function select(values: readonly number[], index: number): number {\n  return values[index] ?? values.length;\n}\n",
        &["select"],
    )
    .unwrap();
}

#[test]
fn typescript_proves_fixed_readonly_tuple_and_source_const_literals() {
    prove_typescript(
        "function tupleValue(flag: boolean, pair: readonly [number, string]): number {\n  return flag && pair[1] === \"ready\" ? pair[0] : pair.length;\n}\nexport function localValue(flag: boolean): number {\n  const values = [4, \"ready\"] as const;\n  return tupleValue(flag, values);\n}\n",
        &["localValue"],
    )
    .unwrap();
}

#[test]
fn check_js_proves_readonly_array_length_and_checked_index() {
    prove_javascript(
        "/** @param {ReadonlyArray<number>} values @param {number} index @returns {number} */\nexport function select(values, index) {\n  return values[index] ?? values.length;\n}\n",
        &["select"],
    )
    .unwrap();
}

#[test]
fn check_js_proves_source_owned_const_primitive_array_literal() {
    prove_javascript(
        "/** @param {number} index @returns {number} */\nexport function select(index) {\n  const values = [3, 5, 8];\n  return values[index] ?? values.length;\n}\n",
        &["select"],
    )
    .unwrap();
}

#[test]
fn collections_refuse_mutable_parameters_and_mutation_methods() {
    assert_eq!(
        prove_typescript(
            "function mutableParameter(values: number[]): number { return values.length; }\n",
            &[],
        ),
        Err("frontend.typescript.type-unsupported".to_owned()),
    );
    assert_eq!(
        prove_typescript(
            "function mutate(): number { const values = [1, 2]; values.push(3); return values.length; }\n",
            &[],
        ),
        Err("frontend.typescript.call-target-unsupported".to_owned()),
    );
    assert_eq!(
        prove_javascript(
            "/** @returns {number} */\nfunction mutate() { const values = [1, 2]; values.push(3); return values.length; }\n",
            &[],
        ),
        Err("frontend.javascript.call-target-unsupported".to_owned()),
    );
}

#[test]
fn collections_refuse_unchecked_possibly_undefined_indexing() {
    assert_eq!(
        prove_typescript(
            "function unsafe(values: ReadonlyArray<number>, index: number): number { const selected = values[index]; return selected ?? 0; }\n",
            &[],
        ),
        Err("frontend.typescript.collection-index-undefined".to_owned()),
    );
}

#[test]
fn collections_refuse_spread_literals() {
    assert_eq!(
        prove_typescript(
            "function spread(values: readonly number[]): number { const copy = [...values]; return copy.length; }\n",
            &[],
        ),
        Err("frontend.typescript.collection-literal-shape".to_owned()),
    );
}

#[test]
fn collections_refuse_destructuring() {
    assert_eq!(
        prove_typescript(
            "function destructure(values: readonly number[]): number { const [first] = values; return first ?? 0; }\n",
            &[],
        ),
        Err("frontend.typescript.local-shape-unsupported".to_owned()),
    );
}

#[test]
fn collections_refuse_nested_object_union_and_any_element_types() {
    for annotation in [
        "ReadonlyArray<readonly number[]>",
        "ReadonlyArray<{ value: number }>",
        "ReadonlyArray<number | string>",
        "ReadonlyArray<any>",
    ] {
        let source =
            format!("function invalid(values: {annotation}): number {{ return values.length; }}\n");
        let failure = prove_typescript(&source, &[]).unwrap_err();
        assert!(
            failure == "frontend.typescript.collection-element-type-unsupported"
                || failure == "frontend.typescript.collection-type-unsupported",
            "unexpected refusal for {annotation}: {failure}",
        );
    }
}

#[test]
fn collections_refuse_noncanonical_properties_and_bracketed_length() {
    assert_eq!(
        prove_typescript(
            "function mapped(values: readonly number[]): number { return values.map(value => value + 1).length; }\n",
            &[],
        ),
        Err("frontend.typescript.collection-base-unsupported".to_owned()),
    );
    assert_eq!(
        prove_typescript(
            "function bracketed(values: readonly number[]): number { return values[\"length\"]; }\n",
            &[],
        ),
        Err("frontend.typescript.collection-index-type".to_owned()),
    );
}
