use std::fs;

use maledictus::conformance::check_heap_source;
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};

fn request_in(directory: &tempfile::TempDir, source: &str) -> ProofRequest {
    fs::write(directory.path().join("optional_program.py"), source).unwrap();
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "optional_program.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    }
}

fn verify_issuance(source: &str) -> maledictus::protocol::ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    maledictus::verify(&request_in(&directory, source))
}

#[test]
fn production_issuance_proves_guarded_optional_access_and_explicit_none_return() {
    let response = verify_issuance(
        "from typing import Optional\n\nclass Item:\n    pass\n\ndef choose(flag: bool) -> Optional[Item]:\n    if flag:\n        return Item()\n    return None\n\ndef inspect(item: Optional[Item]) -> None:\n    if item is not None:\n        assert isinstance(item, Item)\n",
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(response.verifier_identity.is_some(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
}

#[test]
fn heap_semantics_refute_nonoptional_fallthrough() {
    let result = check_heap_source(
        "class Item:\n    pass\n\n#:: ExpectedOutput(postcondition.violated:assertion.false)\ndef choose(flag: bool) -> Item:\n    if flag:\n        return Item()\n",
        "nonoptional_fallthrough.py",
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
}

#[test]
fn optional_alias_rebinding_and_unsupported_inner_types_fail_closed() {
    for (case_index, source) in [
        "from typing import Optional\nclass Item:\n    pass\nAlias = Optional[Item]\nAlias = Item\ndef inspect(value: Alias) -> None:\n    pass\n",
        "from typing import Optional\ndef inspect(value: Optional[int]) -> None:\n    pass\n",
        "class Item:\n    pass\ndef inspect(value: Optional[Item]) -> None:\n    pass\n",
        "from typing import Optional\nclass Item:\n    pass\ndef inspect(value: Optional[Item]) -> None:\n    pass\nOptional = Item\n",
        "class Item:\n    pass\nclass Optional:\n    pass\ndef inspect(value: Optional[Item]) -> None:\n    pass\n",
    ]
    .into_iter()
    .enumerate()
    {
        let result = check_heap_source(source, "invalid_optional.py");
        assert!(result.is_err(), "case {case_index}: {result:#?}");
    }
}

#[test]
fn isinstance_without_nominal_provenance_refuses_instead_of_panicking() {
    let error = check_heap_source(
        "class Item:\n    pass\n\ndef inspect(value: object) -> None:\n    assert isinstance(value, Item)\n",
        "untyped_isinstance.py",
    )
    .unwrap_err();
    assert!(
        error.contains("frontend.python.heap.isinstance-value-untyped"),
        "{error}"
    );
}

#[test]
fn symbolic_list_loop_keeps_an_independent_exhaustion_path() {
    let result = check_heap_source(
        "from typing import List\nfrom nagini_contracts.contracts import Acc, Requires, list_pred\n\nclass Item:\n    pass\n\n#:: ExpectedOutput(postcondition.violated:assertion.false)\ndef choose(items: List[bool]) -> Item:\n    Requires(Acc(list_pred(items)))\n    for selected in items:\n        if selected:\n            return Item()\n",
        "symbolic_list_exhaustion.py",
    )
    .unwrap();
    assert!(result.passed, "{result:#?}");
}

#[test]
fn symbolic_list_loop_requires_explicit_list_predicate_permission() {
    let result = check_heap_source(
        "from typing import List\n\nclass Item:\n    pass\n\ndef choose(items: List[bool]) -> Item:\n    for selected in items:\n        if selected:\n            return Item()\n    return Item()\n",
        "symbolic_list_permission.py",
    )
    .unwrap();
    assert!(!result.passed, "{result:#?}");
    assert!(!result.actual.is_empty(), "{result:#?}");
}

#[test]
fn symbolic_list_loop_refuses_else_and_mutating_bodies() {
    for source in [
        "from typing import List\nfrom nagini_contracts.contracts import Acc, Requires, list_pred\nclass Item:\n    pass\ndef choose(items: List[bool]) -> Item:\n    Requires(Acc(list_pred(items)))\n    for selected in items:\n        if selected:\n            return Item()\n    else:\n        return Item()\n",
        "from typing import List\nfrom nagini_contracts.contracts import Acc, Requires, list_pred\nclass Item:\n    pass\ndef choose(items: List[bool]) -> Item:\n    Requires(Acc(list_pred(items)))\n    for selected in items:\n        selected = False\n    return Item()\n",
    ] {
        let result = check_heap_source(source, "unsupported_symbolic_loop.py");
        assert!(result.is_err(), "{result:#?}");
    }
}
