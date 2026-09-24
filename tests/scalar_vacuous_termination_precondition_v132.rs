use std::path::Path;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::verify_contract_module;

const VACUOUS_PRECONDITION_FIXTURE: &str =
    "tests/obligations/verification/chalice2silver/issues/chalice2silver-79.py";

fn vacuous_precondition_source() -> &'static str {
    "from nagini_contracts.contracts import Implies, Invariant, Requires\nfrom nagini_contracts.obligations import *\n\ndef precondition() -> None:\n    Requires(Implies(2 + 2 < 3, MustTerminate(1)))\n\ndef loop() -> None:\n    while True:\n        Invariant(Implies(False, MustTerminate(1)))\n        pass\n"
}

fn assert_not_verified(source: &str) {
    assert!(
        !verify_contract_module(source, "vacuous_precondition_drift.py", &[])
            .is_ok_and(|verification| verification.passed),
        "unsupported or false precondition proof verified:\n{source}"
    );
}

#[test]
fn closed_false_termination_precondition_is_solver_proved() {
    let verified = verify_contract_module(
        vacuous_precondition_source(),
        "vacuous_precondition.py",
        &[],
    )
    .unwrap();
    assert!(verified.passed, "{verified:#?}");
    assert_eq!(verified.obligations.len(), 2, "{verified:#?}");
    assert!(
        verified
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains("vacuous-termination-precondition"))
    );
}

#[test]
fn vacuous_precondition_rejects_true_open_effectful_and_import_drift() {
    for changed in [
        vacuous_precondition_source().replace("2 + 2 < 3", "True"),
        vacuous_precondition_source().replace("2 + 2 < 3", "missing"),
        vacuous_precondition_source().replace(
            "Requires(Implies(2 + 2 < 3, MustTerminate(1)))",
            "Requires(MustTerminate(1))",
        ),
        vacuous_precondition_source().replace(
            "Requires(Implies(2 + 2 < 3, MustTerminate(1)))\n\n",
            "Requires(Implies(2 + 2 < 3, MustTerminate(1)))\n    print(1)\n\n",
        ),
        vacuous_precondition_source().replace(
            "from nagini_contracts.obligations import *",
            "from nagini_contracts.obligations import MustTerminate",
        ),
    ] {
        assert_not_verified(&changed);
    }
}

#[test]
fn exact_pinned_chalice_79_fixture_matches() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_scalar_fixture(&suite, &pin, VACUOUS_PRECONDITION_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
}
