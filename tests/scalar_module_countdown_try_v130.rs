use std::path::Path;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::verify_contract_module;
use maledictus::vc::ObligationStatus;

const COUNTDOWN_TRY_FIXTURE: &str = "tests/functional/verification/test_global_program.py";

#[test]
fn closed_module_countdown_executes_success_and_exception_paths_exactly() {
    let success = verify_contract_module(
        "from nagini_contracts.contracts import Invariant\n\nvalues = [True]\ntry:\n    counter = 3\n    while counter > 0:\n        Invariant(counter >= 0)\n        counter -= 1\n    values = [values[counter]]\nexcept Exception as error:\n    values = [False]\nassert values\n",
        "module_countdown_success.py",
        &[],
    )
    .unwrap();
    assert!(success.passed, "{success:#?}");

    let fallback = verify_contract_module(
        "from nagini_contracts.contracts import Invariant\n\nvalues = [True]\ntry:\n    counter = 2\n    while counter > -2:\n        Invariant(counter >= -2)\n        counter -= 1\n    values = [values[counter]]\nexcept Exception as error:\n    values = [False]\nassert not values[0]\n",
        "module_countdown_fallback.py",
        &[],
    )
    .unwrap();
    assert!(fallback.passed, "{fallback:#?}");
}

#[test]
fn closed_module_countdown_checks_invariants_and_fails_closed_on_shape_changes() {
    let false_invariant = verify_contract_module(
        "from nagini_contracts.contracts import Invariant\n\nvalues = [True]\ntry:\n    counter = 2\n    while counter > 0:\n        Invariant(counter < 0)\n        counter -= 1\n    values = [values[counter]]\nexcept Exception as error:\n    values = [False]\n",
        "module_countdown_false_invariant.py",
        &[],
    )
    .unwrap();
    assert!(!false_invariant.passed, "{false_invariant:#?}");
    assert!(
        false_invariant
            .obligations
            .iter()
            .any(|obligation| obligation.status == ObligationStatus::Refuted),
        "{false_invariant:#?}"
    );

    for source in [
        "values = [True]\ntry:\n    counter = 2\n    while counter >= 0:\n        counter -= 1\n    values = [values[counter]]\nexcept Exception:\n    values = [False]\n",
        "values = [True]\ntry:\n    counter = 2\n    while counter > 0:\n        counter -= 0\n    values = [values[counter]]\nexcept Exception:\n    values = [False]\n",
        "values = [True]\ntry:\n    counter = 2\n    while counter > 0:\n        counter -= 1\n    values = [values[counter]]\nexcept ValueError:\n    values = [False]\n",
    ] {
        assert!(
            verify_contract_module(source, "unsupported_module_countdown.py", &[]).is_err(),
            "unsupported countdown shape verified:\n{source}"
        );
    }
}

#[test]
fn exact_pinned_module_countdown_fixture_matches() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_scalar_fixture(&suite, &pin, COUNTDOWN_TRY_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
}
