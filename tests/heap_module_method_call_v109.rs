use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_heap_contracts::verify_heap_module;
use maledictus::vc::ObligationStatus;

const MODULE_METHOD_FIXTURE: &str = "tests/functional/verification/issues/00196.py";

#[test]
fn assigned_module_method_calls_report_the_real_failed_precondition() {
    let verification = verify_heap_module(
        r#"from nagini_contracts.contracts import *
from typing import *

class Worker:
    def stop(self, payload: Tuple[Union[int, slice], ...]) -> Tuple[int, ...]:
        Requires(False)
        ...

worker = Worker()
result = worker.stop((1, 2))
"#,
        "module_method_precondition.py",
        &[],
    )
    .expect("the module executor should reach the method precondition");

    assert!(!verification.passed, "{verification:#?}");
    let refuted = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.status == ObligationStatus::Refuted)
        .collect::<Vec<_>>();
    assert_eq!(refuted.len(), 1, "{verification:#?}");
    assert!(
        refuted[0].id.contains("module:call-precondition:stop:0"),
        "{verification:#?}"
    );
}

#[test]
fn only_an_empty_legal_call_domain_erases_unobservable_rich_types() {
    let unsupported = verify_heap_module(
        r#"from nagini_contracts.contracts import *
from typing import *

class Worker:
    def inspect(self, payload: Tuple[Union[int, slice], ...]) -> None:
        pass
"#,
        "reachable_rich_parameter.py",
        &[],
    )
    .expect_err("a reachable rich parameter must not be weakened to object");
    assert_eq!(unsupported.code, "frontend.python.heap.type-unsupported");

    let unsupported_return = verify_heap_module(
        r#"from typing import *

class Worker:
    def inspect(self) -> Tuple[int, ...]:
        pass
"#,
        "reachable_rich_return.py",
        &[],
    )
    .expect_err("a reachable rich return must retain its declared type");
    assert_eq!(
        unsupported_return.code,
        "frontend.python.heap.type-unsupported"
    );
}

#[test]
fn normally_returning_module_calls_do_not_skip_result_and_effect_modeling() {
    let unsupported = verify_heap_module(
        r#"class Worker:
    def identity(self, value: int) -> int:
        return value

worker = Worker()
result = worker.identity(4)
"#,
        "module_method_result.py",
        &[],
    )
    .expect_err("a successful module call needs explicit result and effect transfer");
    assert_eq!(
        unsupported.code,
        "frontend.python.heap.module-method-result-binding-unsupported"
    );
}

#[test]
fn module_method_receivers_are_source_ordered_and_fieldful_instances_stay_closed() {
    let before_binding = verify_heap_module(
        r#"class Worker:
    def stop(self) -> None:
        Requires(False)
        pass

result = worker.stop()
worker = Worker()
"#,
        "module_method_before_receiver.py",
        &[],
    )
    .expect_err("a later receiver binding must not be visible to an earlier call");
    assert_eq!(
        before_binding.code,
        "frontend.python.heap.expression-unsupported"
    );

    let fieldful = verify_heap_module(
        r#"class Worker:
    value: int

    def __init__(self) -> None:
        self.value = 1

    def stop(self) -> None:
        Requires(False)
        pass

worker = Worker()
result = worker.stop()
"#,
        "fieldful_module_method.py",
        &[],
    )
    .expect_err("module references with heap state require constructor effect transfer");
    assert_eq!(
        fieldful.code,
        "frontend.python.heap.module-passive-reference-unsupported"
    );
}

#[test]
fn exact_module_method_fixture_adds_one_heap_match_only() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let heap = check_pinned_heap_fixture(&suite, &pin, MODULE_METHOD_FIXTURE)
        .unwrap_or_else(|error| panic!("heap {MODULE_METHOD_FIXTURE}: {error}"));
    assert!(heap.passed, "{heap:#?}");
    assert_eq!(heap.expected, heap.actual, "{heap:#?}");

    let scalar = check_pinned_scalar_fixture(&suite, &pin, MODULE_METHOD_FIXTURE)
        .expect_err("source classes remain outside the scalar backend");
    assert!(
        scalar.contains("frontend.python.contracts.module-statement-unsupported"),
        "{scalar}"
    );

    let reference = check_pinned_reference_fixture(&suite, &pin, MODULE_METHOD_FIXTURE)
        .expect_err("behavioral classes remain outside the reference marker backend");
    assert!(
        reference.contains("frontend.python.references.class-unsupported"),
        "{reference}"
    );
}
