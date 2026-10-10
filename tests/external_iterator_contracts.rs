use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, SourceFile,
};
use std::fs;

const ITERATOR: &str = r#"from typing import Generic, Self, TypeVar
from nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Result

T = TypeVar('T')

class Iterator(Generic[T]):
    @ContractOnly
    def __iter__(self) -> Self:
        Ensures(Result() is self)
        Exsures(Exception, True)
        ...

    @ContractOnly
    def __next__(self) -> T:
        Exsures(StopIteration, True)
        Exsures(Exception, True)
        ...
"#;

const PROVIDER: &str = r#"from collections.abc import Iterator
from nagini_contracts.contracts import ContractOnly, Exsures

@ContractOnly
def chunks() -> Iterator[bytes]:
    Exsures(Exception, True)
    ...
"#;

fn verify(iterator: Option<&str>, source: &str) -> ProofResponse {
    verify_with_stdlib_shadow(iterator, source, false)
}

fn verify_with_stdlib_shadow(iterator: Option<&str>, source: &str, shadow: bool) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    if shadow {
        fs::create_dir(directory.path().join("collections")).unwrap();
        fs::write(directory.path().join("collections/__init__.py"), "").unwrap();
        fs::write(
            directory.path().join("collections/abc.py"),
            "raise RuntimeError('owned code cannot be trusted as a stdlib contract')\n",
        )
        .unwrap();
    }
    fs::write(directory.path().join("provider_contract.py"), PROVIDER).unwrap();
    fs::write(directory.path().join("app.py"), source).unwrap();
    let mut overlays = vec![ExternalOverlay {
        adapter_path: "app.py".to_owned(),
        module: "provider".to_owned(),
        stub_path: "provider_contract.py".to_owned(),
        exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
    }];
    if let Some(iterator) = iterator {
        fs::write(directory.path().join("iterator_contract.py"), iterator).unwrap();
        overlays.push(ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "collections.abc".to_owned(),
            stub_path: "iterator_contract.py".to_owned(),
            exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
        });
    }
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        external_contract_overlays: overlays,
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    })
}

const SOURCE: &str = r#"from provider import chunks

def run() -> bytes:
    try:
        stream = chunks()
        iterator = stream.__iter__()
        assert iterator is stream
        value = iterator.__next__()
    except Exception:
        return b''
    return value
"#;

#[test]
fn native_byte_iterator_uses_real_static_types_and_checked_effects() {
    let response = verify(Some(ITERATOR), SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some());
    let contract = response
        .external_contracts
        .iter()
        .find(|item| item.module == "collections.abc")
        .unwrap();
    assert!(
        contract
            .declared_exceptions
            .contains(&"StopIteration".to_owned()),
        "{contract:#?}"
    );
    assert!(
        contract.functions.contains(&"Iterator.__next__".to_owned()),
        "{contract:#?}"
    );
}

#[test]
fn typed_iterator_cannot_be_replaced_with_a_list_or_another_element_type() {
    let wrong_type = SOURCE
        .replace("def run() -> bytes:", "def run() -> int:")
        .replace("return b''", "return 0");
    let response = verify(Some(ITERATOR), &wrong_type);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|d| d.code.contains("typecheck")),
        "{response:#?}"
    );
    let response = verify(
        Some(ITERATOR),
        &SOURCE.replace("assert iterator is stream", "assert iterator is not stream"),
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}

#[test]
fn iteration_end_handler_does_not_swallow_other_native_exceptions() {
    let source = r#"from provider import chunks

def run() -> bytes:
    try:
        stream = chunks()
        iterator = stream.__iter__()
    except Exception:
        return b''
    try:
        return iterator.__next__()
    except StopIteration:
        return b''
"#;
    let response = verify(Some(ITERATOR), source);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|o| o.id.contains("exception-undeclared:Exception") && o.counterexample.is_some()),
        "{response:#?}"
    );
    let stop_only = ITERATOR.replace(
        "        Exsures(StopIteration, True)\n        Exsures(Exception, True)",
        "        Exsures(StopIteration, True)",
    );
    let response = verify(Some(&stop_only), source);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
}

#[test]
fn static_iterator_interface_alone_never_supplies_native_effects() {
    let response = verify(None, SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
}

#[test]
fn a_source_owned_stdlib_shadow_cannot_hide_behind_the_pinned_static_interface() {
    let response = verify_with_stdlib_shadow(Some(ITERATOR), SOURCE, true);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code.contains("overlay-source-conflict")),
        "{response:#?}"
    );
}

#[test]
fn an_unmodeled_iteration_loop_cannot_be_accepted_as_finite_collection_iteration() {
    let source = r#"from provider import chunks

def run() -> bytes:
    try:
        stream = chunks()
        for value in stream:
            return value
    except Exception:
        return b''
    return b''
"#;
    let response = verify(Some(ITERATOR), source);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
}
