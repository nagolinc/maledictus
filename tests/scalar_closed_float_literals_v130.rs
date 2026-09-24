use std::path::Path;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::verify_contract_module;
use maledictus::vc::ObligationStatus;

const NON_REAL_FIXTURE: &str = "tests/functional/verification/float_real/test_non_real.py";

fn closed_float_source() -> &'static str {
    "from nagini_contracts.contracts import *\n\ndef classify() -> None:\n    nan = float('NaN')\n    infinity = float('inF')\n    finite = float('1.5')\n    negative = float('-2.25')\n    Assert(infinity > finite)\n    Assert(negative < finite)\n    Assert(not nan == nan)\n    Assert(nan == nan)\n"
}

#[test]
fn closed_float_literals_execute_ieee_comparisons_in_source_order() {
    let verified = verify_contract_module(closed_float_source(), "closed_float.py", &[]).unwrap();
    let refuted = verified
        .obligations
        .iter()
        .filter(|obligation| obligation.status == ObligationStatus::Refuted)
        .collect::<Vec<_>>();

    assert_eq!(refuted.len(), 1, "{verified:#?}");
    assert!(refuted[0].id.contains("closed-float"), "{verified:#?}");
}

#[test]
fn closed_float_literals_fail_closed_on_aliases_dynamic_inputs_and_arithmetic() {
    let alias = closed_float_source().replace(
        "infinity = float('inF')",
        "alias = nan\n    infinity = float('inF')",
    );
    assert!(verify_contract_module(&alias, "closed_float_alias.py", &[]).is_err());

    let dynamic = closed_float_source().replace("float('1.5')", "float(text)");
    assert!(verify_contract_module(&dynamic, "closed_float_dynamic.py", &[]).is_err());

    let arithmetic = closed_float_source().replace(
        "Assert(negative < finite)",
        "Assert(negative + finite < finite)",
    );
    assert!(verify_contract_module(&arithmetic, "closed_float_arithmetic.py", &[]).is_err());

    let reassigned =
        closed_float_source().replace("negative = float('-2.25')", "nan = float('-2.25')");
    let error = verify_contract_module(&reassigned, "closed_float_reassigned.py", &[]).unwrap_err();
    assert_eq!(
        error.code,
        "frontend.python.contracts.closed-float-reassignment"
    );
}

#[test]
fn exact_pinned_non_real_float_fixture_matches() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_scalar_fixture(&suite, &pin, NON_REAL_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
}
