use std::path::Path;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::verify_contract_module;

const VACUOUS_TERMINATION_FIXTURE: &str =
    "tests/obligations/verification/chalice2silver/issues/chalice2silver-77-2.py";

fn vacuous_termination_source() -> &'static str {
    "from nagini_contracts.contracts import Implies, Invariant\nfrom nagini_contracts.obligations import *\n\ndef unreachable() -> None:\n    while 8 - 3 < 2:\n        Invariant(MustTerminate(0))\n        pass\n\ndef unguarded() -> None:\n    while True:\n        Invariant(Implies(False, MustTerminate(0)))\n        pass\n"
}

fn assert_not_verified(source: &str) {
    assert!(
        !verify_contract_module(source, "vacuous_termination_drift.py", &[])
            .is_ok_and(|verification| verification.passed),
        "unsupported or false termination proof verified:\n{source}"
    );
}

#[test]
fn closed_vacuous_loops_prove_unreachable_guard_and_false_antecedent() {
    let verified =
        verify_contract_module(vacuous_termination_source(), "vacuous_termination.py", &[])
            .unwrap();
    assert!(verified.passed, "{verified:#?}");
    assert_eq!(verified.obligations.len(), 2, "{verified:#?}");
    assert!(
        verified
            .obligations
            .iter()
            .all(|obligation| obligation.id.contains("vacuous-termination-condition"))
    );
}

#[test]
fn closed_vacuous_loops_reject_false_proofs_effects_and_open_terms() {
    for changed in [
        vacuous_termination_source().replace("8 - 3 < 2", "8 - 3 < missing"),
        vacuous_termination_source().replace("8 - 3 < 2", "True"),
        vacuous_termination_source().replace("Implies(False", "Implies(True"),
        vacuous_termination_source().replace("        pass\n\n", "        print(1)\n\n"),
        vacuous_termination_source().replace(
            "        pass\n\ndef unguarded",
            "        pass\n    print(1)\n\ndef unguarded",
        ),
        vacuous_termination_source().replace(
            "from nagini_contracts.obligations import *",
            "from nagini_contracts.obligations import MustTerminate",
        ),
    ] {
        assert_not_verified(&changed);
    }
}

#[test]
fn exact_pinned_chalice_77_2_fixture_matches() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_scalar_fixture(&suite, &pin, VACUOUS_TERMINATION_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
}
