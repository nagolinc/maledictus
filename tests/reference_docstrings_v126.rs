use maledictus::python_reference_contracts::{
    parse_external_reference_contract_module, verify_and_export_source_reference_module,
    verify_reference_module, verify_reference_module_with_imports,
};
use std::path::PathBuf;

#[test]
fn source_reference_verification_preserves_inert_string_statement_semantics() {
    let result = verify_reference_module(
        r#"
"""module documentation"""

class Widget:
    """class documentation"""
    pass

def identity(value: Widget) -> Widget:
    """function documentation"""
    "an inert standalone string"
    return value
"#,
        "documented_references.py",
        &["identity".to_owned()],
    )
    .unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.functions, ["identity"]);
}

#[test]
fn checked_external_reference_contracts_may_be_documented() {
    let module = parse_external_reference_contract_module(
        r#"
"""external contract documentation"""
from nagini_contracts.contracts import ContractOnly

class Widget:
    """nominal type documentation"""
    pass

@ContractOnly
def identity(value: Widget) -> Widget:
    """summary documentation"""
    ...
"#,
        "provider_contract.py",
        "provider",
    )
    .unwrap();

    assert_eq!(module.module(), "provider");
    assert_eq!(module.type_names(), ["provider.Widget"]);
    assert_eq!(module.function_names(), ["identity"]);
}

#[test]
fn executable_module_expression_statements_remain_fail_closed() {
    let error = verify_reference_module(
        r#"
register()

class Widget:
    pass

def identity(value: Widget) -> Widget:
    return value
"#,
        "executable_module.py",
        &[],
    )
    .unwrap_err();

    assert_eq!(
        error.code,
        "frontend.python.references.module-statement-unsupported"
    );
}

#[test]
fn reference_conformance_defers_linear_io_runtime_modules() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture = "tests/io/verification/master/example1_fork.py";

    let error = maledictus::conformance::check_pinned_reference_fixture(&suite, &pin, fixture)
        .expect_err("nominal-reference conformance claimed linear IO runtime semantics");

    assert!(
        error.starts_with("frontend.python.references.io-semantics-unsupported:"),
        "{error}"
    );
}

#[test]
fn explicit_pinned_nominal_imports_preserve_qualified_type_identity() {
    let (provider_verification, provider) = verify_and_export_source_reference_module(
        r#"
from nagini_contracts.adt import ADT
from nagini_contracts.lock import Lock as RuntimeLock
from nagini_contracts.thread import Thread

def preserve_adt(value: ADT) -> ADT:
    return value

def preserve_lock(value: RuntimeLock) -> RuntimeLock:
    return value

def preserve_thread(value: Thread) -> Thread:
    return value
"#,
        "provider.py",
        "provider",
        &[],
    )
    .unwrap();
    assert!(provider_verification.passed, "{provider_verification:#?}");

    let consumer = verify_reference_module_with_imports(
        r#"
from nagini_contracts.contracts import Assert
from nagini_contracts.lock import Lock
from provider import preserve_lock

def run(value: Lock) -> None:
    returned = preserve_lock(value)
    Assert(returned is not None)
"#,
        "consumer.py",
        &["run".to_owned()],
        &[provider],
    )
    .unwrap();

    assert!(consumer.passed, "{consumer:#?}");
}

#[test]
fn pinned_nominal_modules_do_not_smuggle_effectful_symbols() {
    let error = verify_reference_module(
        "from nagini_contracts.thread import Thread, getArg\n\ndef use(value: Thread) -> Thread:\n    return value\n",
        "thread_effect.py",
        &[],
    )
    .unwrap_err();

    assert_eq!(
        error.code,
        "frontend.python.references.pinned-nominal-symbol-unsupported"
    );
}

#[test]
fn importing_a_nominal_type_does_not_make_an_empty_module_owned() {
    let error = verify_reference_module(
        "from nagini_contracts.lock import Lock\n",
        "empty_lock_module.py",
        &[],
    )
    .unwrap_err();

    assert_eq!(error.code, "frontend.python.references.empty-module");
}

#[test]
fn wildcard_imports_cannot_hide_unmodeled_contract_effects() {
    for module in [
        "nagini_contracts.io_contracts",
        "nagini_contracts.obligations",
    ] {
        let source = format!(
            "from {module} import *\n\nclass Marker:\n    pass\n\ndef preserve(value: Marker) -> Marker:\n    return value\n"
        );
        let error = verify_reference_module(&source, "effect_wildcard.py", &[]).unwrap_err();
        assert_eq!(
            error.code, "frontend.python.references.effect-wildcard-import-unsupported",
            "{module}"
        );
    }
}

#[test]
fn passive_constructor_only_records_provide_nominal_identity() {
    let result = verify_reference_module(
        r#"
class Pair:
    """A passive nominal record declaration."""

    def __init__(self, left: int, right: int) -> None:
        """Initialize fields without calls or computed expressions."""
        self.left = left
        self.right = right

def preserve(value: Pair) -> Pair:
    return value
"#,
        "passive_record.py",
        &["preserve".to_owned()],
    )
    .unwrap();

    assert!(result.passed, "{result:#?}");
}

#[test]
fn behavioral_class_bodies_are_not_reclassified_as_passive_records() {
    let constructor_error = verify_reference_module(
        r#"
class Active:
    def __init__(self, value: int) -> None:
        self.value = value
        audit(value)

def preserve(value: Active) -> Active:
    return value
"#,
        "active_constructor.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        constructor_error.code,
        "frontend.python.references.constructor-semantics-unsupported"
    );

    let method_error = verify_reference_module(
        r#"
class Active:
    def __init__(self, value: int) -> None:
        self.value = value

    def read(self) -> int:
        return self.value

def preserve(value: Active) -> Active:
    return value
"#,
        "active_method.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        method_error.code,
        "frontend.python.references.class-unsupported"
    );
}

#[test]
fn passive_record_declarations_do_not_fabricate_constructor_summaries() {
    let error = verify_reference_module(
        r#"
class Box:
    def __init__(self, value: int) -> None:
        self.value = value

def build() -> Box:
    return Box(1)
"#,
        "record_constructor_call.py",
        &[],
    )
    .unwrap_err();

    assert_eq!(error.code, "frontend.python.references.call-unresolved");
}

#[test]
fn mixed_runtime_state_and_collection_programs_defer_to_owning_frontends() {
    let module_state = verify_reference_module(
        "class Marker:\n    pass\n\nSUCCESS = 0\n\ndef preserve(value: Marker) -> Marker:\n    return value\n",
        "module_state.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        module_state.code,
        "frontend.python.references.module-runtime-state-unsupported"
    );

    let collection = verify_reference_module(
        "from typing import List\n\nclass Marker:\n    pass\n\ndef first(values: List[Marker]) -> Marker:\n    return values[0]\n",
        "collection_type.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        collection.code,
        "frontend.python.references.collection-type-unsupported"
    );
}

#[test]
fn inherited_nominal_classes_remain_specialized_semantics() {
    let error = verify_reference_module(
        "from nagini_contracts.lock import Lock\n\nclass Guard(Lock):\n    pass\n\ndef preserve(value: Guard) -> Guard:\n    return value\n",
        "lock_subclass.py",
        &[],
    )
    .unwrap_err();

    assert_eq!(
        error.code,
        "frontend.python.references.inherited-class-semantics-unsupported"
    );
}
