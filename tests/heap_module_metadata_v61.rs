use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_heap_contracts::{
    verify_and_export_source_heap_module, verify_heap_module, verify_heap_module_with_imports,
    verify_heap_package_initializer_with_imports,
};

#[test]
fn exact_upstream_builtin_global_fixtures_match() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for fixture in [
        "tests/functional/verification/test_builtin_globals_1.py",
        "tests/functional/verification/test_builtin_globals_2.py",
    ] {
        let result = check_pinned_heap_fixture(
            &repository.join(".upstream/nagini"),
            &repository.join("conformance/nagini-v1.3.1.json"),
            fixture,
        )
        .unwrap_or_else(|error| panic!("exact upstream fixture {fixture} was refused: {error}"));

        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(result.expected, result.actual, "{fixture}: {result:#?}");
    }
}

#[test]
fn entry_metadata_is_stable_and_protected_rebinding_is_an_obligation() {
    let verification = verify_heap_module(
        "saved = __file__\nassert __name__ == '__main__'\nassert saved == __file__\n__name__ = 'provider'\n",
        "entry.py",
        &[],
    )
    .expect("entry metadata is verifier-known");

    assert!(!verification.passed);
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|item| !item.satisfied())
            .map(|item| item.id.as_str())
            .collect::<Vec<_>>(),
        ["module:field-write-permission:__name__"]
    );
}

#[test]
fn imported_module_has_its_qualified_name_and_star_import_leaks_no_metadata() {
    let (_, provider) = verify_and_export_source_heap_module(
        "assert __name__ == 'resources.provider'\nassert __file__ == 'resources/provider.py'\n",
        "resources/provider.py",
        "resources.provider",
        &[],
    )
    .expect("side-effect-only provider metadata is exact");

    let verification = verify_heap_module_with_imports(
        "from resources.provider import *\nassert __name__ == '__main__'\nassert __file__ == 'entry.py'\n",
        "entry.py",
        &[],
        &[provider],
    )
    .expect("a metadata-only star import contributes no bindings");

    assert!(verification.passed);
}

#[test]
fn metadata_cannot_be_imported_explicitly_from_a_provider() {
    let (_, provider) = verify_and_export_source_heap_module(
        "assert __name__ == 'provider'\n",
        "provider.py",
        "provider",
        &[],
    )
    .expect("provider metadata is verified but not exported");

    let verification = verify_heap_module_with_imports(
        "from provider import __name__\n",
        "entry.py",
        &[],
        &[provider],
    )
    .expect("protected metadata import is diagnosed as a write");

    assert!(!verification.passed);
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|item| !item.satisfied())
            .map(|item| item.id.as_str())
            .collect::<Vec<_>>(),
        ["module:field-write-permission:__name__"]
    );
}

#[test]
fn star_import_with_unmodeled_user_bindings_fails_closed() {
    let (_, provider) = verify_and_export_source_heap_module(
        "def value() -> int:\n    return 1\n",
        "provider.py",
        "provider",
        &[],
    )
    .expect("provider has one verified user export");

    let error =
        verify_heap_module_with_imports("from provider import *\n", "entry.py", &[], &[provider])
            .expect_err("star binding effects remain closed outside the metadata-only case");

    assert_eq!(
        error.code,
        "frontend.python.heap.star-import-exports-unsupported"
    );
}

#[test]
fn deletion_and_unknown_package_identity_fail_closed() {
    let deletion = verify_heap_module("del __file__\n", "entry.py", &[])
        .expect_err("protected metadata deletion is not modeled");
    assert_eq!(
        deletion.code,
        "frontend.python.heap.module-statement-unsupported"
    );

    let unknown_identity = verify_heap_package_initializer_with_imports(
        "assert __name__ == 'package'\n",
        "package/__init__.py",
        &[],
    )
    .expect_err("the package API cannot guess a qualified module identity");
    assert_eq!(unknown_identity.code, "frontend.python.name.unresolved");
}

#[test]
fn every_supported_binding_form_preserves_protected_metadata() {
    for (source, binding) in [
        ("def __name__() -> str:\n    return 'changed'\n", "__name__"),
        ("class __file__:\n    pass\n", "__file__"),
        ("import provider as __name__\n", "__name__"),
        ("__file__ += '.bak'\n", "__file__"),
    ] {
        let verification = verify_heap_module(source, "entry.py", &[])
            .unwrap_or_else(|error| panic!("protected binding {binding} was refused: {error:?}"));
        assert!(!verification.passed);
        assert_eq!(
            verification
                .obligations
                .iter()
                .filter(|item| !item.satisfied())
                .map(|item| item.id.clone())
                .collect::<Vec<_>>(),
            [format!("module:field-write-permission:{binding}")]
        );
    }
}
