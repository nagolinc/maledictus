use std::path::Path;

use maledictus::InformationFlowVerificationProfile;
use maledictus::conformance::{ConformanceMatchKind, check_pinned_heap_fixture};
use maledictus::python_heap_contracts::verify_heap_module_with_information_flow_profile;

fn verify_sif(
    source: &str,
    path: &str,
) -> maledictus::python_heap_contracts::HeapContractVerification {
    verify_heap_module_with_information_flow_profile(
        source,
        path,
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

#[test]
fn low_control_and_low_data_prove_a_low_field_postcondition() {
    let verification = verify_sif(
        r#"from nagini_contracts.contracts import *

class Negative(Exception):
    pass

class Box:
    value: int

def classify(value: int, box: Box) -> None:
    Requires(Low(value))
    Requires(Acc(box.value))
    Ensures(Acc(box.value))
    Ensures(Low(box.value))
    try:
        if value < 0:
            raise Negative()
        box.value = 1
    except Negative:
        box.value = -1
"#,
        "low_control.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn high_control_refutes_a_low_field_postcondition_even_when_each_rhs_is_public() {
    let verification = verify_sif(
        r#"from nagini_contracts.contracts import *

class Box:
    value: int

def reveal(secret: bool, box: Box) -> None:
    Requires(Acc(box.value))
    Ensures(Acc(box.value))
    Ensures(Low(box.value))
    if secret:
        box.value = 0
    else:
        box.value = 1
"#,
        "high_control.py",
    );

    assert!(!verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains(":postcondition:") && !obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn high_exception_selection_remains_tainted_through_finally() {
    let verification = verify_sif(
        r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

class Box:
    value: int

def reveal(secret: bool, box: Box) -> None:
    Requires(Acc(box.value))
    Ensures(Acc(box.value))
    Ensures(Low(box.value))
    try:
        if secret:
            raise Failure()
    except Failure:
        box.value = 0
    else:
        box.value = 1
    finally:
        box.value = box.value
"#,
        "high_exception_control.py",
    );

    assert!(!verification.passed, "{verification:#?}");
}

#[test]
fn ordinary_verification_does_not_silently_enable_low_semantics() {
    let source = r#"from nagini_contracts.contracts import *

def identity(value: int) -> int:
    Requires(Low(value))
    return value
"#;
    let failure = verify_heap_module_with_information_flow_profile(
        source,
        "ordinary.py",
        &[],
        InformationFlowVerificationProfile::Ordinary,
    )
    .expect_err("the ordinary profile must not interpret canonical Low");

    assert_ne!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn concurrent_sif_profiles_retain_low_label_verification() {
    let source = r#"from nagini_contracts.contracts import *

def reveal(secret: int) -> int:
    Ensures(Low(Result()))
    return secret
"#;
    for profile in [
        InformationFlowVerificationProfile::PossibilisticSecureInformationFlow,
        InformationFlowVerificationProfile::ProbabilisticSecureInformationFlow,
    ] {
        let verification = verify_heap_module_with_information_flow_profile(
            source,
            "concurrent_sif_low.py",
            &[],
            profile,
        )
        .unwrap_or_else(|failure| {
            panic!(
                "expected {profile:?} to lower, but it refused with {}: {}",
                failure.code, failure.message
            )
        });
        assert!(!verification.passed, "{profile:?}: {verification:#?}");
        assert!(
            verification.obligations.iter().any(|obligation| {
                obligation.id.contains(":postcondition:") && !obligation.satisfied()
            }),
            "{profile:?}: {verification:#?}"
        );
    }
}

#[test]
fn unsupported_relational_loop_invariants_fail_closed() {
    let source = r#"from nagini_contracts.contracts import *

def count(limit: int) -> int:
    Requires(Low(limit))
    value = 0
    while value < limit:
        Invariant(Low(value))
        value += 1
    return value
"#;
    let failure = verify_heap_module_with_information_flow_profile(
        source,
        "low_loop.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("unmodeled relational loop invariants must not be guessed");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn mutation_through_an_alias_cannot_preserve_a_low_field_fact() {
    let verification = verify_sif(
        r#"from nagini_contracts.contracts import *

class Box:
    value: int

def reveal(secret: int, box: Box, alias: Box) -> None:
    Requires(alias is box)
    Requires(Acc(alias.value))
    Requires(Low(box.value))
    Ensures(Acc(alias.value))
    Ensures(Low(box.value))
    alias.value = secret
"#,
        "low_alias_mutation.py",
    );

    assert!(!verification.passed, "{verification:#?}");
}

#[test]
fn rebinding_a_field_root_cannot_preserve_the_old_objects_low_fact() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

class Box:
    value: int

def replace(original: Box, replacement: Box) -> None:
    Requires(Acc(original.value))
    Requires(Low(original.value))
    Ensures(Low(original.value))
    original = replacement
"#,
        "low_root_rebinding.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("the heap frontend currently refuses reference-valued local rebinding");

    assert_ne!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn a_negated_low_precondition_cannot_be_assumed_as_a_positive_low_fact() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

def reveal(secret: int) -> int:
    Requires(not Low(secret))
    Ensures(Low(Result()))
    return secret
"#,
        "negative_low_precondition.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("a negative occurrence of Low must fail closed");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn a_disjunctive_low_precondition_cannot_be_assumed_unconditionally() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

def reveal(secret: int, alternative: bool) -> int:
    Requires(Low(secret) or alternative)
    Ensures(Low(Result()))
    return secret
"#,
        "disjunctive_low_precondition.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("a disjunctive occurrence of Low must fail closed");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn an_unmodeled_effectful_call_cannot_preserve_low_heap_facts() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

class Box:
    value: int

def mutate(box: Box) -> None:
    pass

def reveal(box: Box) -> None:
    Requires(Low(box.value))
    Ensures(Low(box.value))
    mutate(box)
"#,
        "effectful_low_call.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("unmodeled calls on a Low heap path must fail closed");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn a_shadowed_contract_wrapper_cannot_turn_runtime_low_into_an_assumption() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

def reveal(Requires: object, secret: int) -> int:
    Requires(Low(secret))
    Ensures(Low(Result()))
    return secret
"#,
        "shadowed_requires.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("a shadowed Requires name must remain an ordinary runtime call");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn an_assignment_expression_binding_cannot_retain_canonical_low_semantics() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

def reveal(secret: int, replacement: object) -> int:
    Requires((Low := replacement) and Low(secret))
    Ensures(Low(Result()))
    return secret
"#,
        "named_expression_low_shadow.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("an assignment expression makes Low a local binding for the whole function");

    assert_ne!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn a_parameter_named_result_cannot_acquire_the_ghost_result_semantics() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

def constant(Result: object) -> int:
    Ensures(Low(Result()))
    return 0
"#,
        "shadowed_result.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("a parameter named Result is an ordinary source value, not the ghost result");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn canonical_result_is_low_only_when_every_return_value_and_control_path_is_low() {
    let verification = verify_sif(
        r#"from nagini_contracts.contracts import *

def constant() -> int:
    Ensures(Low(Result()))
    return 0
"#,
        "canonical_low_result.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn a_parameter_named_len_cannot_acquire_canonical_builtin_semantics() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

def constant(len: object, value: int) -> int:
    Requires(Low(value))
    Ensures(Low(len(value)))
    return 0
"#,
        "shadowed_len.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("a parameter named len is an ordinary source callable, not the builtin");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn an_unrelated_contract_import_alias_cannot_retain_builtin_len_semantics() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *
from nagini_contracts.contracts import Acc as len

def constant(value: int) -> int:
    Requires(Low(value))
    Ensures(Low(len(value)))
    return 0
"#,
        "import_alias_len.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("an imported alias named len shadows the builtin");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn an_unsupported_low_form_cannot_become_a_false_implication_antecedent() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

def constant(callback: object) -> int:
    Ensures(Implies(Low(callback()), Low(Result())))
    return 0
"#,
        "unsupported_low_polarity.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("unsupported Low expressions must not be rewritten to false by default");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn path_varying_low_cannot_be_summarized_in_an_implication_antecedent() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

def reveal(flag: bool, secret: int) -> int:
    Requires(Low(flag))
    Ensures(Implies(Low(value), Low(secret)))
    if flag:
        value = 0
    else:
        value = secret
    return 0
"#,
        "path_varying_low_antecedent.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("a universal Low summary cannot move into a negative logical position");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn low_in_two_argument_exsures_fails_closed_until_exceptional_relations_are_supported() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

class Box:
    value: int

def fail(box: Box) -> None:
    Exsures(Failure, Low(box.value))
    raise Failure()
"#,
        "low_exsures.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("two-argument Exsures relations are not modeled by the SIF lowering yet");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn an_implicit_exception_channel_cannot_manufacture_a_low_postcondition() {
    let failure = verify_heap_module_with_information_flow_profile(
        r#"from nagini_contracts.contracts import *

class Box:
    value: int

def reveal(secret: int, box: Box) -> None:
    Requires(Acc(box.value))
    Ensures(Acc(box.value))
    Ensures(Low(box.value))
    try:
        quotient = 1 // secret
    except ZeroDivisionError:
        box.value = 0
    else:
        box.value = 1
"#,
        "implicit_exception_control.py",
        &[],
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .expect_err("implicit exceptions need an explicit SIF control-flow model");

    assert_eq!(failure.code, "frontend.python.sif.low-form-unsupported");
}

#[test]
fn exact_terauchi_figure_one_matches_after_equal_value_high_pc_join() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/sif-true/verification/examples/terauchi-fig1.py";
    let result = check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap_or_else(|error| panic!("heap classifier refused {fixture}: {error}"));

    assert!(result.passed, "{result:#?}");
    assert!(result.expected.is_empty(), "{result:#?}");
    assert!(result.actual.is_empty(), "{result:#?}");
    assert!(result.semantic_verified, "{result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SemanticVerification,
        "{result:#?}"
    );
}

#[test]
fn unequal_public_constants_under_a_secret_guard_remain_high_after_the_join() {
    let verification = verify_sif(
        r#"from nagini_contracts.contracts import *

def reveal(secret: bool) -> int:
    Ensures(Low(Result()))
    if secret:
        value = 0
    else:
        value = 1
    return value
"#,
        "unequal_high_pc_join.py",
    );

    assert!(!verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains(":postcondition:") && !obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn unequal_public_constants_under_a_public_guard_remain_low_after_the_join() {
    let verification = verify_sif(
        r#"from nagini_contracts.contracts import *

def choose(public: bool) -> int:
    Requires(Low(public))
    Ensures(Low(Result()))
    if public:
        value = 0
    else:
        value = 1
    return value
"#,
        "unequal_low_pc_join.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn equal_branch_terms_that_still_depend_on_a_secret_do_not_become_low() {
    let verification = verify_sif(
        r#"from nagini_contracts.contracts import *

def reveal(secret: bool) -> bool:
    Ensures(Low(Result()))
    if secret:
        value = secret
    else:
        value = secret
    return value
"#,
        "equal_secret_dependent_join.py",
    );

    assert!(!verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains(":postcondition:") && !obligation.satisfied()),
        "{verification:#?}"
    );
}
