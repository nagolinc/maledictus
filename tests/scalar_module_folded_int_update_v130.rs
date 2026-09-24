use std::path::Path;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::verify_contract_module;
use maledictus::vc::ObligationStatus;

const FOLDED_INT_FIXTURE: &str = "tests/functional/verification/test_global_mutable_2.py";

fn folded_int_source() -> &'static str {
    "from nagini_contracts.contracts import *\n\nvalue = 4\n\n@Predicate\ndef value_perm() -> bool:\n    return Acc(value, 1/2)\n\n@Pure\ndef get_value() -> int:\n    Requires(value_perm())\n    return Unfolding(value_perm(), value)\n\ndef increment() -> int:\n    global value\n    Requires(Acc(value, 1/2))\n    Requires(value_perm() and get_value() <= 4)\n    Ensures(value_perm())\n    Ensures(Acc(value, 1/2) and value == Old(value) + 2)\n    Unfold(value_perm())\n    value += 2\n    Fold(value_perm())\n    return value\n\nFold(value_perm())\nincrement()\nincrement()\n"
}

#[test]
fn folded_module_int_executes_one_update_then_refutes_the_next_bound() {
    let verified =
        verify_contract_module(folded_int_source(), "folded_module_int.py", &[]).unwrap();
    let refuted = verified
        .obligations
        .iter()
        .filter(|obligation| obligation.status == ObligationStatus::Refuted)
        .collect::<Vec<_>>();

    assert_eq!(refuted.len(), 1, "{verified:#?}");
    assert!(refuted[0].id.contains("call-precondition"), "{verified:#?}");
}

#[test]
fn folded_module_int_rejects_alias_fraction_contract_and_effect_drift() {
    let alias = folded_int_source().replace(
        "return value\n\nFold(value_perm())\n",
        "return value\n\nalias = value\nFold(value_perm())\n",
    );
    let alias_error = verify_contract_module(&alias, "folded_module_alias.py", &[]).unwrap_err();
    assert_eq!(
        alias_error.code,
        "frontend.python.contracts.module-folded-int-alias"
    );

    for changed in [
        folded_int_source().replace("Acc(value, 1/2)", "Acc(value, 1/3)"),
        folded_int_source().replace("value == Old(value) + 2", "value == Old(value) + 3"),
        folded_int_source().replace("value += 2", "value -= 2"),
    ] {
        assert!(
            verify_contract_module(&changed, "folded_module_drift.py", &[]).is_err(),
            "unsupported protocol drift verified:\n{changed}"
        );
    }
}

#[test]
fn exact_pinned_folded_module_int_fixture_matches() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_scalar_fixture(&suite, &pin, FOLDED_INT_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
}
