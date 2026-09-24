use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::verify_heap_module;

fn refuse(source: &str) -> ContractFailure {
    verify_heap_module(source, "typing_sized_adversary.py", &[])
        .expect_err("unsupported typing.Sized behavior must refuse before proof issuance")
}

#[test]
fn exact_upstream_typing_sized_translation_fixture_matches_without_a_false_obligation() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let result = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/translation/test_mypy_superclass.py",
    )
    .expect("the canonical typing.Sized fixture should be modeled");

    assert!(result.expected.is_empty(), "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn typing_sized_does_not_supply_an_allocator_or_abstract_method_implementation() {
    let allocation = refuse(
        r#"from typing import Sized

class Whatever(Sized):
    def __len__(self) -> int:
        return 15

def run() -> None:
    value = Whatever()
"#,
    );
    assert_eq!(
        allocation.code, "frontend.python.heap.constructor-allocator-provenance-unsupported",
        "{allocation:#?}"
    );

    let inherited_method = refuse(
        r#"from typing import Sized

class Whatever(Sized):
    pass

def length(value: Whatever) -> int:
    return value.__len__()
"#,
    );
    assert_eq!(
        inherited_method.code, "frontend.python.heap.module-dispatch-method-unresolved",
        "{inherited_method:#?}"
    );
}
