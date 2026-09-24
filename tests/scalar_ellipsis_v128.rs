use std::path::PathBuf;

use maledictus::conformance::{check_pinned_scalar_fixture, check_scalar_source};
use maledictus::python_contracts::{parse_external_contract_module, verify_contract_module};

const IMPORT: &str = "from types import EllipsisType\n";

fn prove(body: &str) {
    let source = format!("{IMPORT}from nagini_contracts.contracts import *\n\n{body}");
    let verification = verify_contract_module(&source, "ellipsis_behavior.py", &[])
        .unwrap_or_else(|error| panic!("Ellipsis source refused: {error:#?}\n{source}"));
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn literal_and_builtin_ellipsis_share_equality_and_identity() {
    prove(
        "def run() -> None:\n    assert ... == Ellipsis\n    assert ... is Ellipsis\n    assert ... is ...\n",
    );
}

#[test]
fn ellipsis_type_parameters_have_the_singleton_value() {
    prove(
        "def run(value: EllipsisType) -> None:\n    assert value == ...\n    assert value is Ellipsis\n",
    );
}

#[test]
fn runtime_type_and_isinstance_use_the_canonical_imported_type() {
    prove(
        "def run() -> None:\n    assert isinstance(..., EllipsisType)\n    assert type(Ellipsis) == EllipsisType\n",
    );
}

#[test]
fn ellipsis_imports_and_builtin_bindings_fail_closed_on_aliases_and_collisions() {
    for (source, expected_code) in [
        (
            "from types import EllipsisType as ET\ndef run(value: ET) -> None:\n    pass\n",
            "frontend.python.contracts.module-statement-unsupported",
        ),
        (
            "from types import EllipsisType\nfrom types import EllipsisType\ndef run() -> None:\n    pass\n",
            "frontend.python.contracts.ellipsis-import-collision",
        ),
        (
            "from types import EllipsisType\nEllipsis = 1\ndef run() -> None:\n    pass\n",
            "frontend.python.contracts.ellipsis-binding-shadowed",
        ),
        (
            "from types import EllipsisType\ndef run(type: int) -> None:\n    assert ... is ...\n",
            "frontend.python.contracts.ellipsis-binding-shadowed",
        ),
        (
            "def run(value: EllipsisType) -> None:\n    pass\n",
            "frontend.python.contracts.ellipsis-type-import-required",
        ),
    ] {
        let failure = verify_contract_module(source, "ellipsis_binding.py", &[])
            .expect_err("shadowed or unproven Ellipsis binding must be refused");
        assert_eq!(
            failure.code, expected_code,
            "unexpected refusal for {source}"
        );
    }
}

#[test]
fn external_contract_entry_point_cannot_bypass_type_provenance() {
    let failure = parse_external_contract_module(
        "@ContractOnly\ndef run(value: EllipsisType) -> None:\n    ...\n",
        "provider.py",
        "provider",
    )
    .expect_err("external EllipsisType annotations require the same canonical provenance");
    assert_eq!(
        failure.code,
        "frontend.python.contracts.ellipsis-type-import-required"
    );
}

#[test]
fn exact_pinned_ellipsis_fixture_matches_all_seven_diagnostics() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let result = check_pinned_scalar_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/verification/test_ellipsis.py",
    )
    .expect("the scalar frontend must own the canonical Ellipsis singleton fixture");

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual, "{result:#?}");
    assert_eq!(result.actual.len(), 7, "{result:#?}");
}

#[test]
fn direct_conformance_does_not_require_a_fixture_router_special_case() {
    let result = check_scalar_source(
        "from types import EllipsisType\ndef run(value: EllipsisType) -> None:\n    assert value is ...\n",
        "ordinary_ellipsis.py",
    )
    .expect("ordinary source-bound Ellipsis semantics must verify");
    assert!(result.passed, "{result:#?}");
}
