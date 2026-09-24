use std::path::Path;

use maledictus::InformationFlowVerificationProfile;
use maledictus::conformance::{ConformanceMatchKind, check_pinned_heap_fixture};
use maledictus::python_heap_contracts::verify_heap_module_with_information_flow_profile;

fn verify_sif(
    source: &str,
    path: &str,
) -> Result<
    maledictus::python_heap_contracts::HeapContractVerification,
    maledictus::python_contracts::ContractFailure,
> {
    verify_heap_module_with_information_flow_profile(
        source,
        path,
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
}

fn assert_exact_fixture(fixture: &str) {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let result = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap_or_else(|error| panic!("heap classifier refused {fixture}: {error}"));

    assert!(result.passed, "{fixture}: {result:#?}");
    assert!(result.semantic_verified, "{fixture}: {result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SemanticVerification,
        "{fixture}: {result:#?}"
    );
}

fn assert_exact_secondary_refusal(fixture: &str, expected_code: &str) {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let failure = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .expect_err("the exact fixture still has a documented secondary frontend blocker");

    assert!(
        failure.starts_with(expected_code),
        "{fixture}: expected {expected_code}, received {failure}"
    );
}

#[test]
fn a_total_constant_source_call_produces_a_low_result() {
    let verification = verify_sif(
        r#"from nagini_contracts.contracts import *

def public_value() -> int:
    return 7

def caller(secret: int) -> int:
    Ensures(Low(Result()))
    return public_value()
"#,
        "sif_source_constant.py",
    )
    .expect("the total source call must lower");

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn an_identity_summary_substitutes_the_actual_argument_label() {
    let positive = verify_sif(
        r#"from nagini_contracts.contracts import *

def identity(value: int) -> int:
    Ensures(Result() == value)
    return value

def caller(public: int) -> int:
    Requires(Low(public))
    Ensures(Low(Result()))
    return identity(public)
"#,
        "sif_source_identity_positive.py",
    )
    .expect("the identity source call must lower");
    assert!(positive.passed, "{positive:#?}");

    let negative = verify_sif(
        r#"from nagini_contracts.contracts import *

def identity(value: int) -> int:
    Ensures(Result() == value)
    return value

def caller(secret: int) -> int:
    Ensures(Low(Result()))
    return identity(secret)
"#,
        "sif_source_identity_negative.py",
    )
    .expect("a security violation is a false VC, not a frontend refusal");
    assert!(!negative.passed, "{negative:#?}");
}

#[test]
fn a_source_identity_preserves_the_canonical_term_at_a_high_join() {
    let verification = verify_sif(
        r#"from nagini_contracts.contracts import *

def identity(value: int) -> int:
    return value

def caller(secret: bool) -> int:
    Ensures(Low(Result()))
    if secret:
        value = identity(1)
    else:
        value = 1
    return value
"#,
        "sif_source_identity_join.py",
    )
    .expect("the source identity must retain its exact canonical result term");

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn a_recursive_value_postcondition_is_not_a_totality_proof() {
    let failure = verify_sif(
        r#"from nagini_contracts.contracts import *

def zero(count: int) -> int:
    Ensures(Result() == 0)
    if count == 0:
        return 0
    return zero(count - 1)

def caller(secret: int) -> int:
    Ensures(Low(Result()))
    return zero(secret)
"#,
        "sif_source_recursive_seed.py",
    )
    .expect_err("a circular value postcondition is not a well-founded totality proof");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn an_exceptional_callee_is_not_made_total_by_its_value_postcondition() {
    let failure = verify_sif(
        r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

def maybe(secret: bool) -> int:
    Ensures(Result() == 0)
    if secret:
        raise Failure()
    return 0

def caller(secret: bool) -> int:
    Ensures(Low(Result()))
    return maybe(secret)
"#,
        "sif_source_exceptional.py",
    )
    .expect_err("an explicit exceptional exit must prevent a total source summary");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn dynamic_and_lexically_shadowed_calls_remain_refused() {
    let dynamic = verify_sif(
        r#"from nagini_contracts.contracts import *

def caller(callback: object) -> int:
    Ensures(Low(Result()))
    return callback()
"#,
        "sif_dynamic_call.py",
    )
    .expect_err("a dynamic call must not acquire a source summary");
    assert_eq!(dynamic.code, "frontend.python.sif.low-form-unsupported");

    let shadowed = verify_sif(
        r#"from nagini_contracts.contracts import *

def identity(value: int) -> int:
    return value

def caller(identity: object) -> int:
    Ensures(Low(Result()))
    return identity(0)
"#,
        "sif_shadowed_source_call.py",
    )
    .expect_err("a parameter must shadow the same-named source function");
    assert_eq!(shadowed.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn exact_joana_direct_constant_call_matches() {
    assert_exact_fixture("tests/sif-true/verification/examples/joana-fig13-l.py");
}

#[test]
fn exact_terauchi_direct_identity_call_matches() {
    assert_exact_secondary_refusal(
        "tests/sif-true/verification/examples/terauchi-fig3.py",
        "frontend.python.sif.low-form-unsupported: runtime expression effects",
    );
}

#[test]
fn exact_control_flow_direct_calls_match() {
    assert_exact_secondary_refusal(
        "tests/sif-true/verification/test_ctrl_flow.py",
        "frontend.python.heap.conditional-statement-effects-unsupported",
    );
}

#[test]
fn exact_field_reader_direct_calls_match() {
    assert_exact_secondary_refusal(
        "tests/sif-true/verification/test_functions_2.py",
        "frontend.python.heap.type-unsupported",
    );
}

#[test]
fn exact_recursive_constant_time_calls_match() {
    assert_exact_secondary_refusal(
        "tests/sif-prob/verification/examples/no_obligations/secc-ct.py",
        "frontend.python.sif.low-form-unsupported: runtime expression may have an unmodeled exceptional control channel",
    );
}
