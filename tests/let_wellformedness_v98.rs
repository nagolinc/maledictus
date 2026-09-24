use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_language_wellformedness::{INVALID_LET, validate_language_wellformedness};

const FIXTURE: &str = "tests/functional/translation/test_let_1.py";

fn failure(
    source: &str,
) -> maledictus::python_language_wellformedness::LanguageWellformednessFailure {
    validate_language_wellformedness(source, "let_wellformedness_v98.py")
        .expect_err("malformed canonical Let unexpectedly passed source validation")
}

fn assert_valid(source: &str) {
    validate_language_wellformedness(source, "let_wellformedness_v98.py")
        .unwrap_or_else(|error| panic!("{source}\n{error:#?}"));
}

#[test]
fn canonical_let_requires_an_inline_one_parameter_lambda() {
    for source in [
        "from nagini_contracts.contracts import Let\ndef body(value: int) -> bool:\n    return value > 0\ndef run(value: int) -> bool:\n    return Let(value, bool, body)\n",
        "from nagini_contracts.contracts import Let\ndef run(value: int) -> bool:\n    return Let(value, bool)\n",
        "from nagini_contracts.contracts import Let\ndef run(value: int) -> bool:\n    return Let(value, bool, lambda: True)\n",
        "from nagini_contracts.contracts import Let\ndef run(value: int) -> bool:\n    return Let(value, bool, lambda first, second: first > second)\n",
        "from nagini_contracts.contracts import Let\ndef run(value: int) -> bool:\n    return Let(value, bool, lambda bound=value: bound > 0)\n",
        "from nagini_contracts.contracts import Let\ndef run(value: int) -> bool:\n    return Let(value=value, result_type=bool, body=lambda bound: bound > 0)\n",
    ] {
        let error = failure(source);
        assert_eq!(error.code, INVALID_LET, "{source}");
        assert!(error.line > 0 && error.column > 0, "{error:#?}");
    }

    assert_valid(
        "from nagini_contracts.contracts import Let\ndef run(value: int) -> bool:\n    return Let(value, bool, lambda bound: bound > 0)\n",
    );
    assert_valid(
        "from nagini_contracts.contracts import Let\ndef run(value: int) -> bool:\n    return Let(value, bool, lambda bound, /: bound > 0)\n",
    );
}

#[test]
fn import_and_value_aliases_are_resolved_without_misclassifying_shadowed_calls() {
    for source in [
        "from nagini_contracts.contracts import Let as Bind\ndef body(value: int) -> bool:\n    return value > 0\ndef run(value: int) -> bool:\n    return Bind(value, bool, body)\n",
        "import nagini_contracts.contracts as contracts\ndef body(value: int) -> bool:\n    return value > 0\ndef run(value: int) -> bool:\n    return contracts.Let(value, bool, body)\n",
        "from nagini_contracts.contracts import Let\nBind = Let\ndef body(value: int) -> bool:\n    return value > 0\ndef run(value: int) -> bool:\n    return Bind(value, bool, body)\n",
    ] {
        assert_eq!(failure(source).code, INVALID_LET, "{source}");
    }

    for source in [
        "from nagini_contracts.contracts import Let\ndef run(Let: object, value: int) -> object:\n    return Let(value, bool, object())\n",
        "from nagini_contracts.contracts import Let\nLet = object\ndef run(value: int) -> object:\n    return Let(value, bool, object())\n",
        "import nagini_contracts.contracts as contracts\ndef run(contracts: object, value: int) -> object:\n    return contracts.Let(value, bool, object())\n",
        "from nagini_contracts.contracts import Let\ndef run(value: int) -> object:\n    from local_helpers import Let\n    return Let(value, bool, object())\n",
        "import nagini_contracts.contracts as contracts\ndef run(value: int) -> object:\n    import local_helpers as contracts\n    return contracts.Let(value, bool, object())\n",
        "class contracts:\n    @staticmethod\n    def Let(value: object, result: object, body: object) -> object:\n        return value\ndef run(value: int) -> object:\n    return contracts.Let(value, bool, object())\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn exact_invalid_let_fixture_matches_every_frontend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, FIXTURE)
        .unwrap_or_else(|error| panic!("scalar {FIXTURE}: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(
        scalar.analysis_kind,
        ConformanceMatchKind::SourceWellformednessRejection
    );

    let heap = check_pinned_heap_fixture(&suite, &pin, FIXTURE)
        .unwrap_or_else(|error| panic!("heap {FIXTURE}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(
        heap.analysis_kind,
        ConformanceMatchKind::SourceWellformednessRejection
    );

    let reference = check_pinned_reference_fixture(&suite, &pin, FIXTURE)
        .unwrap_or_else(|error| panic!("reference {FIXTURE}: {error}"));
    assert!(reference.passed, "{reference:#?}");
    assert_eq!(reference.expected, reference.actual);
}
