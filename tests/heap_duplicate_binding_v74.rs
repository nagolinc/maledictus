use maledictus::conformance::check_pinned_heap_fixture;

#[test]
fn exact_upstream_duplicate_function_binding_fails_closed_before_heap_semantics() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let error = check_pinned_heap_fixture(
        &root.join(".upstream/nagini"),
        &root.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/translation/issues/00020.py",
    )
    .expect_err("duplicate top-level functions must not produce heap proof obligations");

    assert!(
        error.starts_with("frontend.python.heap.duplicate-function:"),
        "{error}"
    );
}
