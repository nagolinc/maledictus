use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_language_wellformedness::{
    INVALID_ACC, PERMISSION_TO_FINAL_VAR, validate_language_wellformedness,
};

fn failure(
    source: &str,
) -> maledictus::python_language_wellformedness::LanguageWellformednessFailure {
    validate_language_wellformedness(source, "acc_target_wellformedness_v108.py")
        .expect_err("invalid canonical Acc target unexpectedly passed source validation")
}

fn assert_valid(source: &str) {
    validate_language_wellformedness(source, "acc_target_wellformedness_v108.py")
        .unwrap_or_else(|error| panic!("{source}\n{error:#?}"));
}

#[test]
fn acc_distinguishes_predicates_and_fields_from_ordinary_members() {
    let method = failure(
        "from nagini_contracts.contracts import Acc\nclass Item:\n    def check(self) -> bool:\n        return True\ndef use(item: Item) -> None:\n    Acc(item.check())\n",
    );
    assert_eq!(method.code, INVALID_ACC);

    let property = failure(
        "from nagini_contracts.contracts import Acc\nclass Item:\n    @property\n    def value(self) -> int:\n        return 1\ndef use(item: Item) -> None:\n    Acc(item.value)\n",
    );
    assert_eq!(property.code, INVALID_ACC);

    assert_valid(
        "from nagini_contracts.contracts import Acc, Predicate\nclass Item:\n    def initialize(self) -> None:\n        self.value = 1\n    @Predicate\n    def owns(self) -> bool:\n        return Acc(self.value)\ndef use(item: Item) -> None:\n    Acc(item.value)\n    Acc(item.owns())\n",
    );
}

#[test]
fn inherited_source_members_retain_their_permission_kind() {
    let inherited_property = failure(
        "from nagini_contracts.contracts import Acc\nclass Base:\n    @property\n    def value(self) -> int:\n        return 1\nclass Derived(Base):\n    pass\ndef use(item: Derived) -> None:\n    Acc(item.value)\n",
    );
    assert_eq!(inherited_property.code, INVALID_ACC);

    assert_valid(
        "from nagini_contracts.contracts import Acc\nclass Base:\n    def initialize(self) -> None:\n        self.value = 1\nclass Derived(Base):\n    pass\ndef use(item: Derived) -> None:\n    Acc(item.value)\n",
    );
}

#[test]
fn only_single_assignment_unmutated_module_values_are_final() {
    let final_value = failure(
        "from nagini_contracts.contracts import Acc\nvalue = 1\ndef use() -> None:\n    Acc(value)\n",
    );
    assert_eq!(final_value.code, PERMISSION_TO_FINAL_VAR);

    for source in [
        "from nagini_contracts.contracts import Acc\nvalue = 1\nvalue = 2\ndef use() -> None:\n    Acc(value)\n",
        "from nagini_contracts.contracts import Acc\nvalue = 1\ndef use() -> None:\n    global value\n    Acc(value)\n    value += 1\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn aliases_qualified_calls_shadows_and_unknown_types_preserve_binding_identity() {
    let aliased = failure(
        "from nagini_contracts.contracts import Acc as Permission\nvalue = 1\ndef use() -> None:\n    Permission(value)\n",
    );
    assert_eq!(aliased.code, PERMISSION_TO_FINAL_VAR);

    let qualified = failure(
        "import nagini_contracts.contracts as contracts\nclass Item:\n    def check(self) -> bool:\n        return True\ndef use(item: Item) -> None:\n    contracts.Acc(item.check())\n",
    );
    assert_eq!(qualified.code, INVALID_ACC);

    for source in [
        "def Acc(value: object) -> bool:\n    return True\nvalue = 1\ndef use() -> None:\n    Acc(value)\n",
        "from nagini_contracts.contracts import Acc\nvalue = 1\ndef use(Acc: object) -> None:\n    pass\n",
        "from provider import Item\nfrom nagini_contracts.contracts import Acc\ndef use(item: Item) -> None:\n    Acc(item.provider_member)\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn all_three_exact_acc_failures_match_every_frontend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    for fixture in [
        "tests/functional/translation/test_acc_1.py",
        "tests/functional/translation/test_acc_2.py",
        "tests/functional/translation/test_acc_3.py",
    ] {
        let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("scalar {fixture}: {error}"));
        assert!(scalar.passed, "{scalar:#?}");
        assert_eq!(
            scalar.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection
        );

        let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("heap {fixture}: {error}"));
        assert!(heap.passed, "{heap:#?}");
        assert_eq!(
            heap.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection
        );

        let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(reference.passed, "{reference:#?}");
        assert_eq!(reference.expected, reference.actual);
    }
}
