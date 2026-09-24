use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_contracts::verify_contract_module;
use maledictus::vc::ObligationStatus;

const GLOBAL_SCOPES_FIXTURE: &str = "tests/functional/verification/test_global_scopes.py";

#[test]
fn static_module_unpacking_binds_nested_values_in_parallel() {
    let verification = verify_contract_module(
        r#"left, (middle, right) = 1, (2, 4)

def total() -> int:
    return left + middle + right
"#,
        "module_unpacking.py",
        &[],
    )
    .expect("nested static module unpacking should lower");
    assert!(verification.passed, "{verification:#?}");

    let unresolved = verify_contract_module(
        "left, right = 1, left\n",
        "parallel_module_unpacking.py",
        &[],
    )
    .expect_err("all right-hand-side leaves must use the pre-assignment environment");
    assert_eq!(unresolved.code, "frontend.python.name.unresolved");
}

#[test]
fn dynamic_starred_mismatched_and_duplicate_unpacking_fail_closed() {
    let dynamic = verify_contract_module(
        "pair = (1, 2)\nleft, right = pair\n",
        "dynamic_module_unpacking.py",
        &[],
    )
    .expect_err("a dynamic iterable may raise or have a different length");
    assert_eq!(
        dynamic.code,
        "frontend.python.contracts.module-unpacking-value-unsupported"
    );

    let starred =
        verify_contract_module("left, *rest = (1, 2)\n", "starred_module_unpacking.py", &[])
            .expect_err("starred unpacking has variable-length semantics");
    assert_eq!(
        starred.code,
        "frontend.python.contracts.module-unpacking-starred-unsupported"
    );

    let mismatched = verify_contract_module(
        "left, right = (1,)\n",
        "mismatched_module_unpacking.py",
        &[],
    )
    .expect_err("statically mismatched unpacking must fail before lowering");
    assert_eq!(
        mismatched.code,
        "frontend.python.contracts.module-unpacking-arity"
    );

    let duplicate = verify_contract_module(
        "value, value = (1, 2)\n",
        "duplicate_module_unpacking.py",
        &[],
    )
    .expect_err("the immutable module model cannot silently rebind a target");
    assert_eq!(
        duplicate.code,
        "frontend.python.contracts.module-binding-reassigned"
    );
}

#[test]
fn global_permissions_guard_reads_and_writes_and_stop_failed_paths() {
    let permitted = verify_contract_module(
        r#"from nagini_contracts.contracts import Acc, Requires

value = 1

def update() -> int:
    global value
    Requires(Acc(value))
    old = value
    value = 2
    return old + value
"#,
        "permitted_global_update.py",
        &[],
    )
    .expect("an explicit module-global permission should authorize reads and writes");
    assert!(permitted.passed, "{permitted:#?}");

    let missing_read = verify_contract_module(
        r#"value = 1

def update() -> int:
    global value
    old = value
    value = 2
    return old
"#,
        "missing_global_read_permission.py",
        &[],
    )
    .expect("missing permission is a refuted proof obligation, not a frontend refusal");
    let failures = missing_read
        .obligations
        .iter()
        .filter(|obligation| obligation.status == ObligationStatus::Refuted)
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{missing_read:#?}");
    assert!(
        failures[0]
            .id
            .contains(":assignment-read-permission:value:"),
        "{missing_read:#?}"
    );
    assert!(
        missing_read
            .obligations
            .iter()
            .all(|obligation| !obligation.id.contains(":field-write-permission:")),
        "the failed read has no normal successor that reaches the later write: {missing_read:#?}"
    );

    let missing_write = verify_contract_module(
        "value = 1\n\ndef update() -> None:\n    global value\n    value = 2\n",
        "missing_global_write_permission.py",
        &[],
    )
    .expect("missing write permission is a refuted proof obligation");
    let failures = missing_write
        .obligations
        .iter()
        .filter(|obligation| obligation.status == ObligationStatus::Refuted)
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{missing_write:#?}");
    assert!(
        failures[0].id.contains(":field-write-permission:value:"),
        "{missing_write:#?}"
    );
}

#[test]
fn global_write_values_remain_effect_free_and_total() {
    let effectful = verify_contract_module(
        r#"value = 1

def produce() -> int:
    return 2

def update() -> None:
    global value
    value = produce()
"#,
        "effectful_global_write.py",
        &[],
    )
    .expect_err("source calls need a separate global effect-transfer model");
    assert_eq!(
        effectful.code,
        "frontend.python.contracts.global-write-value-unsupported"
    );
}

#[test]
fn exact_global_scopes_fixture_matches_scalar_and_is_refused_by_other_frontends() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, GLOBAL_SCOPES_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar {GLOBAL_SCOPES_FIXTURE}: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(scalar.expected, scalar.actual, "{scalar:#?}");

    let heap = check_pinned_heap_fixture(&suite, &pin, GLOBAL_SCOPES_FIXTURE)
        .expect_err("the heap backend still requires a mutable module-resource model");
    assert!(
        heap.contains("frontend.python.heap.module-assignment-target-unsupported"),
        "{heap}"
    );

    let reference = check_pinned_reference_fixture(&suite, &pin, GLOBAL_SCOPES_FIXTURE)
        .expect_err("the fixture is not a nominal-reference program");
    assert!(
        reference.contains("frontend.python.references.module-runtime-state-unsupported"),
        "{reference}"
    );
}
