use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str) -> HeapContractVerification {
    verify_heap_module(source, "heap_constructor_annotations_v60.py", &[]).unwrap_or_else(
        |failure| {
            panic!(
                "expected constructor annotations to lower, but got {}: {}",
                failure.code, failure.message
            )
        },
    )
}

fn refuse(source: &str) -> ContractFailure {
    verify_heap_module(source, "heap_constructor_annotations_adversary_v60.py", &[])
        .expect_err("invalid constructor annotations must fail closed")
}

#[test]
fn quoted_forward_fields_and_constructor_attribute_annotations_are_verified() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *

class Child:
    parent: "Parent"

    def __init__(self, parent: "Parent") -> None:
        Ensures(Acc(self.parent))
        Ensures(self.parent is parent)
        self.parent: "Parent" = parent

class Parent:
    child: "Child"

    def __init__(self) -> None:
        Ensures(Acc(self.child))
        Ensures(Acc(self.child.parent))
        Ensures(self.child.parent is self)
        self.child: "Child" = Child(self)

def run() -> None:
    parent = Parent()
    Assert(parent.child.parent is parent)
"#,
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn optional_quoted_forward_constructor_annotation_accepts_none() {
    let verification = verify(
        r#"from nagini_contracts.contracts import *
from typing import Optional

class Node:
    parent: Optional["Node"]

    def __init__(self) -> None:
        Ensures(Acc(self.parent))
        self.parent: Optional["Node"] = None
"#,
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn unknown_and_conflicting_quoted_constructor_annotations_fail_closed() {
    let unknown = refuse(
        r#"class Holder:
    missing: "Missing"
"#,
    );
    assert_eq!(
        unknown.code, "frontend.python.heap.field-type-unsupported",
        "{unknown:#?}"
    );

    let conflict = refuse(
        r#"class Expected:
    pass

class Actual:
    pass

class Holder:
    item: "Expected"

    def __init__(self, item: Actual) -> None:
        self.item: "Actual" = item
"#,
    );
    assert_eq!(
        conflict.code, "frontend.python.heap.field-type-conflict",
        "{conflict:#?}"
    );
}
