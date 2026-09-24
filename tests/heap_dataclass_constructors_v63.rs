use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_heap_contracts::verify_heap_module;

#[test]
fn exact_upstream_dataclass_fixtures_match() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (fixture, expected_diagnostics) in [
        ("tests/functional/translation/test_dataclass.py", 0),
        ("tests/functional/translation/test_dataclass_field.py", 1),
        ("tests/functional/translation/test_dataclass_no_init.py", 1),
    ] {
        let result = check_pinned_heap_fixture(
            &repository.join(".upstream/nagini"),
            &repository.join("conformance/nagini-v1.3.1.json"),
            fixture,
        )
        .unwrap_or_else(|error| panic!("exact upstream fixture {fixture} was refused: {error}"));

        assert!(result.passed, "{result:#?}");
        assert_eq!(result.expected, result.actual);
        assert_eq!(result.actual.len(), expected_diagnostics);
    }
}

#[test]
fn generated_constructor_binds_positional_named_and_default_values() {
    let source = r#"from dataclasses import dataclass, field
from typing import List

@dataclass
class Record:
    count: int
    label: str = "ready"

@dataclass
class Batch:
    values: List[int] = field(default_factory=list)

def run() -> None:
    positional = Record(3)
    named = Record(label="done", count=4)
    batch = Batch()
    assert positional.count == 3
    assert positional.label == "ready"
    assert named.count == 4
    assert named.label == "done"
    assert len(batch.values) == 0
"#;
    let verification = verify_heap_module(source, "dataclass_values.py", &[])
        .unwrap_or_else(|failure| panic!("dataclass source refused: {failure:#?}"));
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn generated_constructor_uses_the_shared_argument_binder() {
    for (source, expected_code) in [
        (
            "from dataclasses import dataclass\n@dataclass\nclass A:\n    value: int\ndef run() -> None:\n    item = A()\n",
            "frontend.python.heap.call-argument-missing",
        ),
        (
            "from dataclasses import dataclass\n@dataclass\nclass A:\n    value: int\ndef run() -> None:\n    item = A(1, value=2)\n",
            "frontend.python.heap.call-argument-duplicate",
        ),
        (
            "from dataclasses import dataclass\n@dataclass\nclass A:\n    value: int\ndef run() -> None:\n    item = A(value='wrong')\n",
            "frontend.python.heap.constructor-argument-type",
        ),
        (
            "from dataclasses import dataclass\n@dataclass\nclass Payload:\n    value: int\n@dataclass\nclass Other:\n    value: int\n@dataclass\nclass Envelope:\n    payload: Payload\ndef run() -> None:\n    other = Other(1)\n    item = Envelope(payload=other)\n",
            "frontend.python.heap.constructor-call-nominal-argument-mismatch",
        ),
    ] {
        let failure = verify_heap_module(source, "dataclass_binding.py", &[]).unwrap_err();
        assert_eq!(failure.code, expected_code, "{failure:#?}");
    }
}

#[test]
fn frozen_dataclass_fields_cannot_be_written() {
    let source = r#"from dataclasses import dataclass

@dataclass(frozen=True)
class Frozen:
    value: int

def run() -> None:
    item = Frozen(1)
    item.value = 2
"#;
    let failure = verify_heap_module(source, "frozen_dataclass.py", &[]).unwrap_err();
    assert_eq!(failure.code, "frontend.python.heap.dataclass-frozen-write");
}

#[test]
fn dataclass_boundary_refuses_unmodeled_generation_and_factory_features() {
    for source in [
        "from dataclasses import dataclass\n@dataclass(order=True)\nclass A:\n    value: int\n",
        "from dataclasses import dataclass\n@dataclass\nclass A:\n    value: int\n    def __post_init__(self) -> None:\n        pass\n",
        "from dataclasses import dataclass, field\n@dataclass\nclass A:\n    values: list[int] = field(default_factory=lambda: [])\n",
        "from dataclasses import dataclass\n@dataclass\nclass Base:\n    value: int\n@dataclass\nclass Child(Base):\n    other: int\n",
    ] {
        assert!(
            verify_heap_module(source, "dataclass_unsupported.py", &[]).is_err(),
            "unsupported dataclass shape was accepted: {source}"
        );
    }
}

#[test]
fn list_factory_identity_is_not_invented_by_the_sequence_value_model() {
    let source = r#"from dataclasses import dataclass, field

@dataclass
class Batch:
    values: list[int] = field(default_factory=list)

def run() -> None:
    left = Batch()
    right = Batch()
    assert left.values is not right.values
"#;
    assert!(verify_heap_module(source, "dataclass_factory_identity.py", &[]).is_err());
}
