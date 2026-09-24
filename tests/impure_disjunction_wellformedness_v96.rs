use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_language_wellformedness::{
    IMPURE_DISJUNCTION, validate_language_wellformedness,
};

fn failure(
    source: &str,
) -> maledictus::python_language_wellformedness::LanguageWellformednessFailure {
    validate_language_wellformedness(source, "impure_disjunction_v96.py")
        .expect_err("impure predicate disjunction unexpectedly passed source validation")
}

fn assert_valid(source: &str) {
    validate_language_wellformedness(source, "impure_disjunction_v96.py")
        .unwrap_or_else(|error| panic!("{source}\n{error:#?}"));
}

#[test]
fn predicate_calls_inside_disjunction_are_rejected_at_the_boolean_expression() {
    let source = r#"from nagini_contracts.contracts import Predicate, Requires

@Predicate
def left() -> bool:
    return True

@Predicate
def right() -> bool:
    return True

def run() -> None:
    Requires(left() or right())
"#;

    let error = failure(source);
    assert_eq!(error.code, IMPURE_DISJUNCTION);
    assert_eq!(error.line, 12);
    assert!(error.column > 0);
}

#[test]
fn aliases_are_resolved_and_local_or_rebound_names_are_not_misclassified() {
    let aliased = failure(
        "from nagini_contracts.contracts import Predicate as Pred\n@Pred\ndef left() -> bool:\n    return True\n@Pred\ndef right() -> bool:\n    return True\ndef run() -> None:\n    assert left() or right()\n",
    );
    assert_eq!(aliased.code, IMPURE_DISJUNCTION);

    let predicate_values_aliased = failure(
        "from nagini_contracts.contracts import Predicate\n@Predicate\ndef left() -> bool:\n    return True\n@Predicate\ndef right() -> bool:\n    return True\nfirst, second = left, right\ndef run() -> None:\n    assert first() or second()\n",
    );
    assert_eq!(predicate_values_aliased.code, IMPURE_DISJUNCTION);

    for source in [
        "from nagini_contracts.contracts import Predicate\n@Predicate\ndef pred() -> bool:\n    return True\ndef run(pred: object) -> None:\n    assert pred() or False\n",
        "from nagini_contracts.contracts import Predicate\n@Predicate\ndef left() -> bool:\n    return True\n@Predicate\ndef right() -> bool:\n    return True\ndef ordinary() -> bool:\n    return True\nleft = ordinary\nright = ordinary\ndef run() -> None:\n    assert left() or right()\n",
        "from nagini_contracts.contracts import Predicate\ndef Predicate(value: object) -> object:\n    return value\n@Predicate\ndef left() -> bool:\n    return True\n@Predicate\ndef right() -> bool:\n    return True\ndef run() -> None:\n    assert left() or right()\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn conjunctions_pure_calls_and_deferred_lambda_bodies_remain_well_formed() {
    for source in [
        "from nagini_contracts.contracts import Predicate\n@Predicate\ndef left() -> bool:\n    return True\n@Predicate\ndef right() -> bool:\n    return True\ndef run() -> None:\n    assert left() and right()\n",
        "def left() -> bool:\n    return True\ndef right() -> bool:\n    return True\ndef run() -> None:\n    assert left() or right()\n",
        "from nagini_contracts.contracts import Predicate\n@Predicate\ndef pred() -> bool:\n    return True\ndef run(flag: bool) -> object:\n    return (lambda: pred()) or flag\n",
    ] {
        assert_valid(source);
    }
}

#[test]
fn exact_pinned_impure_disjunction_matches_every_frontend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/functional/translation/issues/00186.py";

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
