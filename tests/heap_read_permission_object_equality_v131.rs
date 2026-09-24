use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to verify, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refusal(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("unsupported equality/read-permission behavior must fail closed")
}

#[test]
fn canonical_rd_and_root_object_equality_verify_read_only_method_calls() {
    let result = verify(
        r#"from nagini_contracts.contracts import *

class Cell:
    def __init__(self) -> None:
        Ensures(Acc(self.value))
        self.value = 7

    def read(self) -> None:
        Requires(self != None)
        Requires(Rd(self.value))
        Ensures(Rd(self.value))
        assert self.value == self.value

    def client(self) -> None:
        Requires(self != None)
        Requires(Acc(self.value))
        Ensures(Acc(self.value))
        assert self != None
        self.read()
"#,
        "read_permission_identity.py",
    );
    assert!(result.passed, "{result:#?}");
}

#[test]
fn equality_hooks_inheritance_and_noncanonical_rd_remain_closed() {
    let cases = [
        (
            r#"from nagini_contracts.contracts import *
class CustomEq:
    def __eq__(self, other: object) -> bool:
        return True
    def check(self) -> None:
        Requires(self == self)
"#,
            "custom_eq.py",
            "frontend.python.heap.reference-equality-unsupported",
        ),
        (
            r#"from nagini_contracts.contracts import *
class CustomNe:
    def __ne__(self, other: object) -> bool:
        return False
    def check(self) -> None:
        Requires(self != None)
"#,
            "custom_ne.py",
            "frontend.python.heap.reference-equality-unsupported",
        ),
        (
            r#"from nagini_contracts.contracts import *
class Base:
    pass
class Derived(Base):
    def check(self) -> None:
        Requires(self != None)
"#,
            "inherited_eq.py",
            "frontend.python.heap.reference-equality-unsupported",
        ),
        (
            r#"class Cell:
    def __init__(self) -> None:
        self.value = 1
    def read(self) -> int:
        Requires(Rd(self.value))
        return self.value
"#,
            "unbound_rd.py",
            "frontend.python.heap.read-permission-binding-unsupported",
        ),
        (
            r#"from nagini_contracts.contracts import *
class Cell:
    def __init__(self) -> None:
        self.value = 1
    def read(self, Rd: object) -> int:
        Requires(Rd(self.value))
        return self.value
"#,
            "shadowed_rd.py",
            "frontend.python.heap.read-permission-binding-unsupported",
        ),
    ];
    for (source, path, expected) in cases {
        let failure = refusal(source, path);
        assert_eq!(failure.code, expected, "{path}: {failure:#?}");
    }
}

#[test]
fn rd_arity_targets_and_unmatched_transfers_fail_closed() {
    let cases = [
        (
            r#"from nagini_contracts.contracts import *
class Cell:
    def __init__(self) -> None:
        self.value = 1
    def read(self) -> int:
        Requires(Rd(self.value, self.value))
        return self.value
"#,
            "rd_arity.py",
            "frontend.python.heap.read-permission-arguments-unsupported",
        ),
        (
            r#"from nagini_contracts.contracts import *
class Cell:
    def read(self, value: int) -> int:
        Requires(Rd(value))
        return value
"#,
            "rd_nonfield.py",
            "frontend.python.heap.read-permission-target-unsupported",
        ),
        (
            r#"from nagini_contracts.contracts import *
class Cell:
    def __init__(self) -> None:
        Ensures(Acc(self.value))
        self.value = 1
    def consume(self) -> None:
        Requires(Rd(self.value))
        pass
    def client(self) -> None:
        Requires(Acc(self.value))
        self.consume()
"#,
            "rd_unmatched_transfer.py",
            "frontend.python.heap.method-call-read-wildcard-transfer-unsupported",
        ),
    ];
    for (source, path, expected) in cases {
        let failure = refusal(source, path);
        assert_eq!(failure.code, expected, "{path}: {failure:#?}");
    }
}

#[test]
fn exact_simple_rd_fixture_converts_without_changing_profile_ignored_cohort() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let converted =
        check_pinned_heap_fixture(&suite, &pin, "tests/arp/verification/test_simple_rd.py")
            .unwrap();
    assert!(converted.passed, "{converted:#?}");
    assert!(converted.semantic_verified, "{converted:#?}");
    assert_eq!(converted.expected, converted.actual, "{converted:#?}");

    let ignored =
        check_pinned_heap_fixture(&suite, &pin, "tests/arp/verification/test_rd.py").unwrap();
    assert!(!ignored.passed, "{ignored:#?}");
    assert!(!ignored.semantic_verified, "{ignored:#?}");
}
