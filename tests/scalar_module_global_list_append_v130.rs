use std::path::Path;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::verify_contract_module;
use maledictus::vc::ObligationStatus;

const GLOBAL_LIST_APPEND_FIXTURE: &str = "tests/functional/verification/test_global_stateful.py";

fn source_with_calls(calls: &str) -> String {
    format!(
        "from nagini_contracts.contracts import *\nfrom typing import List\n\na = [12]  # type: List[int]\n\ndef append_one() -> None:\n    Requires(Acc(list_pred(a)) and len(a) < 2)\n    Ensures(Acc(list_pred(a)))\n    Ensures(len(a) == Old(len(a)) + 1)\n    a.append(1)\n\n{calls}\n"
    )
}

#[test]
fn closed_module_global_list_append_executes_in_call_order() {
    let once = verify_contract_module(
        &source_with_calls("append_one()"),
        "global_append_once.py",
        &[],
    )
    .unwrap();
    assert!(once.passed, "{once:#?}");

    let twice = verify_contract_module(
        &source_with_calls("append_one()\nappend_one()"),
        "global_append_twice.py",
        &[],
    )
    .unwrap();
    assert!(!twice.passed, "{twice:#?}");
    assert_eq!(
        twice
            .obligations
            .iter()
            .filter(|obligation| obligation.status == ObligationStatus::Refuted)
            .count(),
        1,
        "{twice:#?}"
    );
}

#[test]
fn closed_module_global_list_append_rejects_aliases_and_contract_drift() {
    let alias = source_with_calls("alias = a\nappend_one()");
    let alias_error = verify_contract_module(&alias, "global_append_alias.py", &[]).unwrap_err();
    assert_eq!(
        alias_error.code,
        "frontend.python.contracts.module-list-append-alias"
    );

    let wrong_postcondition = source_with_calls("append_one()").replace(
        "Ensures(len(a) == Old(len(a)) + 1)",
        "Ensures(len(a) == Old(len(a)) + 2)",
    );
    assert!(
        verify_contract_module(&wrong_postcondition, "global_append_wrong_post.py", &[]).is_err()
    );

    let wrong_effect = source_with_calls("append_one()").replace("a.append(1)", "a.append('one')");
    assert!(verify_contract_module(&wrong_effect, "global_append_wrong_effect.py", &[]).is_err());
}

#[test]
fn exact_pinned_global_list_append_fixture_matches() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_scalar_fixture(&suite, &pin, GLOBAL_LIST_APPEND_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
}
