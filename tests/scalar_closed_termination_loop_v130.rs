use std::path::Path;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::verify_contract_module;

const TERMINATION_FIXTURE: &str =
    "tests/obligations/verification/chalice2silver/issues/chalice2silver-77-1.py";

fn termination_source() -> &'static str {
    "from nagini_contracts.contracts import Invariant, Requires\nfrom nagini_contracts.obligations import *\n\ndef count(limit: int) -> None:\n    Requires(limit > -4)\n    index = -8\n    while index < limit:\n        Invariant(MustTerminate(limit - index))\n        index += 2\n"
}

#[test]
fn closed_termination_loop_proves_positive_and_strictly_decreasing_measure() {
    let verified =
        verify_contract_module(termination_source(), "closed_termination.py", &[]).unwrap();
    assert!(verified.passed, "{verified:#?}");
    assert_eq!(verified.obligations.len(), 2, "{verified:#?}");
    assert!(
        verified
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains("termination-measure-positive")),
        "{verified:#?}"
    );
    assert!(
        verified
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains("termination-measure-decrease")),
        "{verified:#?}"
    );
}

#[test]
fn closed_termination_loop_rejects_non_decreasing_and_effectful_variants() {
    for changed in [
        termination_source().replace("index += 2", "index += 0"),
        termination_source().replace("limit - index", "limit + index"),
        termination_source().replace("index += 2", "index += step"),
        termination_source().replace("index += 2", "print(index)\n        index += 2"),
        termination_source().replace(
            "from nagini_contracts.obligations import *",
            "from nagini_contracts.obligations import MustTerminate",
        ),
    ] {
        assert!(
            verify_contract_module(&changed, "closed_termination_drift.py", &[]).is_err(),
            "unsupported termination loop verified:\n{changed}"
        );
    }
}

#[test]
fn exact_pinned_chalice_77_1_fixture_matches() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_scalar_fixture(&suite, &pin, TERMINATION_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
}
