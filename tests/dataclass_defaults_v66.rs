use std::fs;

use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};
use maledictus::python_heap_contracts::verify_heap_module;
use maledictus::{FrontendDisposition, analyze_python_frontend};

fn request(source: &str) -> (tempfile::TempDir, ProofRequest) {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("dataclass_program.py"), source).unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "dataclass_program.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };
    (directory, request)
}

fn frontend(source: &str) -> maledictus::FrontendAnalysis {
    let (_directory, request) = request(source);
    analyze_python_frontend(&request)
}

fn diagnostic_codes(source: &str) -> Vec<String> {
    match verify_heap_module(source, "dataclass_program.py", &[]) {
        Ok(_) => Vec::new(),
        Err(failure) => vec![failure.code.to_owned()],
    }
}

const PRELUDE: &str = "from enum import IntEnum\nfrom typing import List\nfrom nagini_contracts.contracts import *\nfrom dataclasses import dataclass, field\n";

#[test]
fn production_issuance_proves_fresh_defaults_and_explicit_aliases_after_strict_mypy() {
    let source = format!(
        "{PRELUDE}\n@dataclass(frozen=True)\nclass Box:\n    value: int\n    items: List[int] = field(default_factory=list)\n\nclass Color(IntEnum):\n    red = 0\n    green = 1\n\n@dataclass\nclass Painted:\n    color: Color = Color.green\n\ndef run() -> None:\n    first = Box(1)\n    second = Box(2)\n    first.items.append(7)\n    assert len(first.items) == 1\n    assert len(second.items) == 0\n    assert first.items is not second.items\n    shared = [1]\n    left = Box(3, shared)\n    right = Box(4, shared)\n    left.items.append(2)\n    assert len(right.items) == 2\n    assert left.items is right.items\n    painted = Painted()\n    assert painted.color == Color.green\n"
    );
    let (_directory, request) = request(&source);
    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(response.verifier_identity.is_some(), "{response:#?}");
}

#[test]
fn production_issuance_refutes_a_false_primitive_default_after_strict_mypy() {
    let source = format!(
        "{PRELUDE}\nclass Marker(IntEnum):\n    ordinary = 0\n\n@dataclass\nclass Record:\n    value: int = 2\n\ndef run() -> None:\n    item = Record()\n    assert item.value == 3\n"
    );
    let (_directory, request) = request(&source);
    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|item| !item.satisfied())
            .count(),
        1,
        "{response:#?}"
    );
}

#[test]
fn pinned_dataclass_defaults_fixture_matches_all_five_diagnostics() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let result = maledictus::conformance::check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/verification/test_dataclass_defaults.py",
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual);
    assert_eq!(result.actual.len(), 5);
}

#[test]
fn frontend_refuses_user_factories_mutable_defaults_and_unknown_calls() {
    let user_factory = format!(
        "{PRELUDE}\ndef make() -> List[int]:\n    return []\n\n@dataclass\nclass Bad:\n    values: List[int] = field(default_factory=make)\n"
    );
    assert!(
        diagnostic_codes(&user_factory)
            .iter()
            .any(|code| code == "frontend.python.dataclass-defaults.default-unsupported")
    );

    let mutable_default =
        format!("{PRELUDE}\n@dataclass\nclass Bad:\n    values: List[int] = []\n");
    assert!(
        diagnostic_codes(&mutable_default)
            .iter()
            .any(|code| code == "frontend.python.dataclass-defaults.mutable-literal-default")
    );

    let call = format!(
        "{PRELUDE}\n@dataclass\nclass Good:\n    value: int = 1\n\ndef run() -> None:\n    value = dangerous()\n"
    );
    assert!(
        diagnostic_codes(&call)
            .iter()
            .any(|code| code == "frontend.python.dataclass-defaults.call-unsupported")
    );
}

#[test]
fn frontend_refuses_generated_behavior_inheritance_and_descriptors() {
    let inheritance = format!(
        "{PRELUDE}\n@dataclass\nclass Base:\n    value: int\n\n@dataclass\nclass Child(Base):\n    other: int\n"
    );
    assert!(
        diagnostic_codes(&inheritance)
            .iter()
            .any(|code| code == "frontend.python.dataclass-defaults.inheritance-unsupported")
    );

    for member in [
        "    def __init__(self, value: int) -> None:\n        self.value = value\n",
        "    def __post_init__(self) -> None:\n        pass\n",
        "    @property\n    def value(self) -> int:\n        return 1\n",
    ] {
        let source = format!("{PRELUDE}\n@dataclass\nclass Bad:\n    stored: int\n{member}");
        assert!(
            diagnostic_codes(&source)
                .iter()
                .any(|code| code == "frontend.python.dataclass-defaults.class-body-unsupported"),
            "{source}"
        );
    }
}

#[test]
fn frontend_refuses_frozen_writes_unknown_aliasing_and_unsupported_field_types() {
    let frozen = format!(
        "{PRELUDE}\n@dataclass(frozen=True)\nclass Frozen:\n    value: int\n\ndef run() -> None:\n    item = Frozen(1)\n    item.value = 2\n"
    );
    assert!(
        diagnostic_codes(&frozen)
            .iter()
            .any(|code| code == "frontend.python.heap.dataclass-frozen-write")
    );

    let alias = format!(
        "{PRELUDE}\n@dataclass\nclass Box:\n    values: List[int] = field(default_factory=list)\n\ndef run() -> None:\n    first = Box()\n    second = Box()\n    alias = first.values\n    alias = second.values\n"
    );
    assert!(
        diagnostic_codes(&alias)
            .iter()
            .any(|code| code == "frontend.python.dataclass-defaults.rebinding-unsupported")
    );

    let unsupported_type = format!("{PRELUDE}\n@dataclass\nclass Bad:\n    values: List[str]\n");
    assert!(
        diagnostic_codes(&unsupported_type)
            .iter()
            .any(|code| code == "frontend.python.dataclass-defaults.field-type-unsupported")
    );
}

#[test]
fn frontend_enforces_source_order_unique_bindings_and_protected_builtins() {
    let late_import = "from enum import IntEnum\n@dataclass\nclass Bad:\n    value: int\nfrom dataclasses import dataclass\n";
    assert!(matches!(
        frontend(late_import).disposition,
        FrontendDisposition::Unsupported
    ));

    let duplicate = format!("{PRELUDE}\n@dataclass\nclass Bad:\n    value: int\n    value: int\n");
    assert!(
        diagnostic_codes(&duplicate)
            .iter()
            .any(|code| code == "frontend.python.dataclass-defaults.field-redefined")
    );

    let shadow = format!("{PRELUDE}\n@dataclass\nclass int:\n    value: int\n");
    assert!(
        diagnostic_codes(&shadow)
            .iter()
            .any(|code| code == "frontend.python.dataclass-defaults.binding-redefined")
    );
}
