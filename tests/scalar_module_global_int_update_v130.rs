use std::path::Path;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::verify_contract_module;
use maledictus::vc::ObligationStatus;

const GLOBAL_INT_UPDATE_FIXTURE: &str = "tests/functional/verification/test_global_mutable_1.py";

fn source_with_calls(calls: &str) -> String {
    format!(
        "from nagini_contracts.contracts import *\n\nvalue = 1\nvalue += 1\n\ndef consume() -> int:\n    global value\n    Requires(Acc(value) and value >= 1)\n    value += 1\n    return value\n\ndef preserve() -> int:\n    global value\n    Requires(Acc(value) and value >= 1)\n    Ensures(Acc(value) and value == Old(value) + 1)\n    value += 1\n    return value\n\n{calls}\n"
    )
}

#[test]
fn closed_module_int_updates_track_value_and_exclusive_permission_in_order() {
    let verified = verify_contract_module(
        &source_with_calls(
            "preserve()\nassert value == 3\npreserve()\nassert value == 4\nconsume()\nconsume()",
        ),
        "module_int_updates.py",
        &[],
    )
    .unwrap();

    let refuted = verified
        .obligations
        .iter()
        .filter(|obligation| obligation.status == ObligationStatus::Refuted)
        .collect::<Vec<_>>();
    assert_eq!(refuted.len(), 1, "{verified:#?}");
    assert!(
        refuted[0].id.contains("call-permission-precondition"),
        "{verified:#?}"
    );
}

#[test]
fn closed_module_int_updates_fail_closed_on_alias_contract_and_effect_drift() {
    let alias = source_with_calls("alias = value\npreserve()");
    let alias_error = verify_contract_module(&alias, "module_int_alias.py", &[]).unwrap_err();
    assert_eq!(
        alias_error.code,
        "frontend.python.contracts.module-int-update-alias"
    );

    let wrong_postcondition = source_with_calls("preserve()").replace(
        "Ensures(Acc(value) and value == Old(value) + 1)",
        "Ensures(Acc(value) and value == Old(value) + 2)",
    );
    assert!(verify_contract_module(&wrong_postcondition, "module_int_wrong_post.py", &[]).is_err());

    let wrong_effect = source_with_calls("preserve()").replace("value += 1", "value -= 1");
    assert!(verify_contract_module(&wrong_effect, "module_int_wrong_effect.py", &[]).is_err());

    let escape = source_with_calls("preserve()").replace(
        "def preserve() -> int:",
        "def unrelated() -> int:\n    return value\n\ndef preserve() -> int:",
    );
    assert!(verify_contract_module(&escape, "module_int_escape.py", &[]).is_err());
}

#[test]
fn exact_pinned_module_global_int_update_fixture_matches() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_scalar_fixture(&suite, &pin, GLOBAL_INT_UPDATE_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
}
