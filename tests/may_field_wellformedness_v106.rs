use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_language_wellformedness::{
    INVALID_MAY_CREATE, INVALID_MAY_SET, validate_language_wellformedness,
};

fn failure(
    source: &str,
) -> maledictus::python_language_wellformedness::LanguageWellformednessFailure {
    validate_language_wellformedness(source, "may_field_wellformedness_v106.py")
        .expect_err("invalid canonical MayCreate/MaySet unexpectedly passed source validation")
}

fn assert_valid(source: &str) {
    validate_language_wellformedness(source, "may_field_wellformedness_v106.py")
        .unwrap_or_else(|error| panic!("{source}\n{error:#?}"));
}

#[test]
fn field_names_must_be_literal_and_declared_on_the_source_class() {
    for (contract, code) in [
        ("MayCreate", INVALID_MAY_CREATE),
        ("MaySet", INVALID_MAY_SET),
    ] {
        let dynamic = format!(
            "from nagini_contracts.contracts import {contract}\nclass Item:\n    def establish(self) -> None:\n        {contract}(self, 'va' + 'lue')\n    def assign(self) -> None:\n        self.value = 1\n"
        );
        assert_eq!(failure(&dynamic).code, code);

        let missing = format!(
            "from nagini_contracts.contracts import {contract}\nclass Item:\n    def establish(self) -> None:\n        {contract}(self, 'missing')\n    def assign(self) -> None:\n        self.value = 1\n"
        );
        assert_eq!(failure(&missing).code, code);

        let declared = format!(
            "from nagini_contracts.contracts import {contract}\nclass Item:\n    def establish(receiver) -> None:\n        {contract}(receiver, 'value')\n    def assign(receiver) -> None:\n        receiver.value = 1\n"
        );
        assert_valid(&declared);
    }
}

#[test]
fn inherited_fields_are_known_when_the_source_base_catalog_is_complete() {
    for contract in ["MayCreate", "MaySet"] {
        let source = format!(
            "from nagini_contracts.contracts import {contract}\nclass Base:\n    def assign(self) -> None:\n        self.value = 1\nclass Derived(Base):\n    def establish(self) -> None:\n        {contract}(self, 'value')\n"
        );
        assert_valid(&source);
    }

    assert_valid(
        "from provider import Base\nfrom nagini_contracts.contracts import MaySet\nclass Derived(Base):\n    def establish(self) -> None:\n        MaySet(self, 'provider_field')\n",
    );
}

#[test]
fn aliases_qualified_calls_and_source_shadows_preserve_binding_identity() {
    let aliased = failure(
        "from nagini_contracts.contracts import MayCreate as can_create\nclass Item:\n    def establish(self) -> None:\n        can_create(self, 'missing')\n    def assign(self) -> None:\n        self.value = 1\n",
    );
    assert_eq!(aliased.code, INVALID_MAY_CREATE);

    let qualified = failure(
        "import nagini_contracts.contracts as contracts\nclass Item:\n    def establish(self) -> None:\n        contracts.MaySet(self, 'missing')\n    def assign(self) -> None:\n        self.value = 1\n",
    );
    assert_eq!(qualified.code, INVALID_MAY_SET);

    for source in [
        "def MaySet(receiver: object, field: str) -> bool:\n    return True\nclass Item:\n    def establish(self) -> None:\n        MaySet(self, 'missing')\n",
        "from nagini_contracts.contracts import MayCreate\nclass Item:\n    def establish(self, MayCreate: object) -> None:\n        pass\n",
        "from nagini_contracts.contracts import MaySet\nclass Item:\n    def establish(self, other: object) -> None:\n        MaySet(other, 'unknown')\n",
        "from nagini_contracts.contracts import MaySet\nclass Item:\n    def establish(self) -> None:\n        def nested(receiver: object) -> None:\n            MaySet(receiver, 'unknown')\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn all_four_exact_may_field_failures_match_every_frontend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    for fixture in [
        "tests/functional/translation/test_may_create_1.py",
        "tests/functional/translation/test_may_create_2.py",
        "tests/functional/translation/test_may_set_1.py",
        "tests/functional/translation/test_may_set_2.py",
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
