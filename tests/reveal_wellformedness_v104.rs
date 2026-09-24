use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_language_wellformedness::{
    INVALID_REVEAL_NO_FUNCTION, INVALID_REVEAL_NO_OPAQUE_FUNCTION, INVALID_REVEAL_NO_PURE_FUNCTION,
    validate_language_wellformedness,
};

fn failure(
    source: &str,
) -> maledictus::python_language_wellformedness::LanguageWellformednessFailure {
    validate_language_wellformedness(source, "reveal_wellformedness_v104.py")
        .expect_err("invalid canonical Reveal unexpectedly passed source validation")
}

fn assert_valid(source: &str) {
    validate_language_wellformedness(source, "reveal_wellformedness_v104.py")
        .unwrap_or_else(|error| panic!("{source}\n{error:#?}"));
}

#[test]
fn reveal_distinguishes_non_calls_non_pure_functions_and_non_opaque_functions() {
    let no_function = failure(
        "from nagini_contracts.contracts import Reveal\ndef run() -> int:\n    return Reveal(1 + 2)\n",
    );
    assert_eq!(no_function.code, INVALID_REVEAL_NO_FUNCTION);

    let no_pure = failure(
        "from nagini_contracts.contracts import Reveal\ndef hidden() -> int:\n    return 1\ndef run() -> int:\n    return Reveal(hidden())\n",
    );
    assert_eq!(no_pure.code, INVALID_REVEAL_NO_PURE_FUNCTION);

    let no_opaque = failure(
        "from nagini_contracts.contracts import Pure, Reveal\n@Pure\ndef hidden() -> int:\n    return 1\ndef run() -> int:\n    return Reveal(hidden())\n",
    );
    assert_eq!(no_opaque.code, INVALID_REVEAL_NO_OPAQUE_FUNCTION);
}

#[test]
fn pure_opaque_source_functions_are_valid_reveal_targets() {
    for source in [
        "from nagini_contracts.contracts import Opaque, Pure, Reveal\n@Pure\n@Opaque\ndef hidden() -> int:\n    return 1\ndef run() -> int:\n    return Reveal(hidden())\n",
        "import nagini_contracts.contracts as contracts\n@contracts.Pure\n@contracts.Opaque\ndef hidden() -> int:\n    return 1\ndef run() -> int:\n    return contracts.Reveal(hidden())\n",
        "from nagini_contracts.contracts import Opaque, Pure, Reveal\nshow = Reveal\n@Pure\n@Opaque\ndef hidden() -> int:\n    return 1\ndef run() -> int:\n    return show(hidden())\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn aliases_and_qualified_calls_preserve_each_failure_class() {
    let aliased = failure(
        "from nagini_contracts.contracts import Pure, Reveal as show\n@Pure\ndef hidden() -> int:\n    return 1\ndef run() -> int:\n    return show(hidden())\n",
    );
    assert_eq!(aliased.code, INVALID_REVEAL_NO_OPAQUE_FUNCTION);

    let qualified = failure(
        "import nagini_contracts.contracts as contracts\ndef hidden() -> int:\n    return 1\ndef run() -> int:\n    return contracts.Reveal(hidden())\n",
    );
    assert_eq!(qualified.code, INVALID_REVEAL_NO_PURE_FUNCTION);
}

#[test]
fn shadows_and_unresolved_external_metadata_are_not_invented() {
    for source in [
        "def Reveal(value: int) -> int:\n    return value\ndef run() -> int:\n    return Reveal(1 + 2)\n",
        "from nagini_contracts.contracts import Reveal\ndef hidden() -> int:\n    return 1\ndef run(Reveal: object) -> int:\n    return 1\n",
        "from provider import hidden\nfrom nagini_contracts.contracts import Reveal\ndef run() -> int:\n    return Reveal(hidden())\n",
        "from nagini_contracts.contracts import Reveal\ndef run(provider: object) -> object:\n    return Reveal(provider.hidden())\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn all_three_exact_reveal_failures_match_every_frontend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    for fixture in [
        "tests/functional/translation/test_reveal_1.py",
        "tests/functional/translation/test_reveal_2.py",
        "tests/functional/translation/test_reveal_3.py",
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
