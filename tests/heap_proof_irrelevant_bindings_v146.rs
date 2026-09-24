use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_heap_contracts::{
    verify_and_export_source_heap_module, verify_heap_module, verify_heap_module_with_imports,
};

fn verify(source: &str) -> Result<(), maledictus::python_contracts::ContractFailure> {
    let result = verify_heap_module(source, "proof_irrelevant_metadata.py", &[])?;
    assert!(result.passed, "all generated obligations must pass");
    Ok(())
}

#[test]
fn representative_arp_fixture_advances_past_obligation_metadata() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let verification = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/arp/verification/test_arp_lock_1.py",
    )
    .expect("the canonical obligations provider must resolve as verifier intrinsics");

    assert_eq!(
        verification.analysis_kind,
        maledictus::conformance::ConformanceMatchKind::SemanticVerification
    );
    assert!(
        verification.passed,
        "mixed ordinary-heap and obligation diagnostics must match exactly: {verification:#?}"
    );
    assert_eq!(verification.actual, verification.expected);
    assert_eq!(
        verification.actual.len(),
        6,
        "the ARP fixture contains six distinct mixed diagnostics"
    );
    assert!(
        verification
            .actual
            .iter()
            .all(|diagnostic| !diagnostic.code.contains("LevelType.__lt__")),
        "{verification:#?}"
    );
}

#[test]
fn closed_unobserved_metadata_is_omitted_without_becoming_a_proof_value() {
    verify(
        "METADATA = ['MustTerminate', ('Level', 1), {'WaitLevel': True}]\ndef answer() -> int:\n    return 42\n",
    )
    .expect("unobserved finite metadata must not block an otherwise verified module");

    for (name, source) in [
        (
            "load",
            "METADATA = [1, 2]\ndef answer() -> int:\n    return METADATA[0]\n",
        ),
        (
            "alias",
            "METADATA = [1, 2]\nALIAS = METADATA\ndef answer() -> int:\n    return 42\n",
        ),
        (
            "mutation",
            "METADATA = [1, 2]\nMETADATA.append(3)\ndef answer() -> int:\n    return 42\n",
        ),
        (
            "rebind",
            "METADATA = [1, 2]\nMETADATA = [3]\ndef answer() -> int:\n    return 42\n",
        ),
        (
            "escape",
            "METADATA = [1, 2]\ndef consume(value: object) -> None:\n    pass\nconsume(METADATA)\n",
        ),
    ] {
        assert!(
            verify(source).is_err(),
            "{name} must make the mutable container proof-relevant and fail closed"
        );
    }
}

#[test]
fn omitted_provider_metadata_cannot_cross_a_source_import_boundary() {
    let provider = "METADATA = ['translator-only']\ndef answer() -> int:\n    return 42\n";
    let (_, exported) =
        verify_and_export_source_heap_module(provider, "provider.py", "provider", &[])
            .expect("the provider's executable proof surface is closed");

    let named = verify_heap_module_with_imports(
        "from provider import METADATA\ndef answer() -> int:\n    return 42\n",
        "named_consumer.py",
        &[],
        std::slice::from_ref(&exported),
    )
    .expect_err("a direct consumer import makes omitted metadata observable");
    assert_eq!(
        named.code,
        "frontend.python.heap.proof-irrelevant-binding-imported"
    );

    let wildcard = verify_heap_module_with_imports(
        "from provider import *\ndef answer() -> int:\n    return 42\n",
        "wildcard_consumer.py",
        &[],
        &[exported],
    )
    .expect_err("a wildcard import cannot silently omit public provider metadata");
    assert_eq!(
        wildcard.code,
        "frontend.python.heap.star-import-exports-unsupported"
    );
}
