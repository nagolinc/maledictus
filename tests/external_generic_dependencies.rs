use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, SourceFile,
};
use std::fs;

const STREAM: &str = r#"from typing import Generic, TypeVar
from nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Result

T = TypeVar('T')

class Feed(Generic[T]):
    @ContractOnly
    def next(self) -> T:
        Exsures(Exception, True)
        ...

    @ContractOnly
    def accept(self, value: T) -> int:
        Ensures(Result() == 7)
        Exsures(Exception, True)
        ...
"#;

const PROVIDER: &str = r#"from native_stream import Feed
from nagini_contracts.contracts import ContractOnly, Exsures

@ContractOnly
def open_bytes() -> Feed[bytes]:
    Exsures(Exception, True)
    ...

@ContractOnly
def open_ints() -> Feed[int]:
    Exsures(Exception, True)
    ...
"#;

fn verify(provider: &str, source: &str) -> ProofResponse {
    verify_with(&[("provider", provider), ("native_stream", STREAM)], source)
}

fn verify_with(contracts: &[(&str, &str)], source: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    let overlays = contracts
        .iter()
        .enumerate()
        .map(|(index, (module, contract))| {
            let path = format!("contract_{index}.py");
            fs::write(directory.path().join(&path), contract).unwrap();
            ExternalOverlay {
                adapter_path: "app.py".to_owned(),
                module: (*module).to_owned(),
                stub_path: path,
                exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
            }
        })
        .collect();
    fs::write(directory.path().join("app.py"), source).unwrap();
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

const SOURCE: &str = r#"from provider import open_bytes, open_ints

def run() -> bytes:
    try:
        stream = open_bytes()
        value = stream.next()
        result = stream.accept(value)
    except Exception:
        return b''
    assert result == 7
    return value
"#;

#[test]
fn native_generic_template_is_checked_before_provider_composition() {
    let template = maledictus::python_heap_contracts::parse_external_heap_contract_module(
        STREAM,
        "stream_contract.py",
        "native_stream",
    )
    .unwrap();
    assert!(template.class_names().contains(&"Feed".to_owned()));
}

#[test]
fn native_factory_carries_foreign_generic_bytes_type_and_method_contract() {
    let response = verify(PROVIDER, SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
}

#[test]
fn native_generic_return_preserves_declared_exceptions() {
    let source = r#"from provider import open_bytes

def run() -> bytes:
    try:
        stream = open_bytes()
    except Exception:
        return b''
    return stream.next()
"#;
    let response = verify(PROVIDER, source);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains("exception-undeclared")
                && obligation.counterexample.is_some()),
        "{response:#?}"
    );
}

#[test]
fn generic_dependency_does_not_erase_value_assertions_or_element_types() {
    let response = verify(
        PROVIDER,
        &SOURCE.replace("assert result == 7", "assert result == 8"),
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    let response = verify(
        PROVIDER,
        &SOURCE.replace("stream.accept(value)", "stream.accept(7)"),
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    let response = verify(
        PROVIDER,
        &SOURCE.replace("stream = open_bytes()", "stream = open_ints()"),
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
}

#[test]
fn provider_dependencies_must_be_supplied_and_unrelated_overlays_remain_rejected() {
    let missing = verify_with(&[("provider", PROVIDER)], SOURCE);
    assert!(
        matches!(missing.status, ProofStatus::Refused),
        "{missing:#?}"
    );
    let unused = verify_with(
        &[
            ("provider", PROVIDER),
            ("native_stream", STREAM),
            ("unrelated", STREAM),
        ],
        SOURCE,
    );
    assert!(matches!(unused.status, ProofStatus::Refused), "{unused:#?}");
    assert!(
        unused.diagnostics.iter().any(|diagnostic| diagnostic.code
            == "frontend.python.heap.import-unused"
            && diagnostic.message.contains("unrelated")),
        "{unused:#?}"
    );
}

#[test]
fn generic_type_alias_preserves_the_foreign_provider_identity() {
    let provider = PROVIDER
        .replace(
            "from native_stream import Feed",
            "from native_stream import Feed as NativeFeed",
        )
        .replace("-> Feed[", "-> NativeFeed[");
    let response = verify(&provider, SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
}

#[test]
fn transitive_native_type_dependencies_keep_nested_returned_objects_available() {
    let middle = r#"from native_stream import Feed
from nagini_contracts.contracts import ContractOnly, Exsures

class Response:
    @ContractOnly
    def body(self) -> Feed[bytes]:
        Exsures(Exception, True)
        ...
"#;
    let provider = r#"from middle import Response
from nagini_contracts.contracts import ContractOnly, Exsures

@ContractOnly
def open_response() -> Response:
    Exsures(Exception, True)
    ...
"#;
    let source = r#"from provider import open_response

def run() -> bytes:
    try:
        response = open_response()
        stream = response.body()
        value = stream.next()
        result = stream.accept(value)
    except Exception:
        return b''
    assert result == 7
    return value
"#;
    let response = verify_with(
        &[
            ("provider", provider),
            ("native_stream", STREAM),
            ("middle", middle),
        ],
        source,
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
}

#[test]
fn generic_native_self_return_retains_receiver_identity_and_element_type() {
    let stream = STREAM.replace("Generic, TypeVar", "Generic, Self, TypeVar")
        + r#"

    @ContractOnly
    def same(self) -> Self:
        Ensures(Result() is self)
        Exsures(Exception, True)
        ...
"#;
    let source = SOURCE.replace(
        "value = stream.next()",
        "same = stream.same()\n        assert same is stream\n        value = same.next()",
    );
    let response = verify_with(
        &[("provider", PROVIDER), ("native_stream", &stream)],
        &source,
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let response = verify_with(
        &[("provider", PROVIDER), ("native_stream", &stream)],
        &source.replace("assert same is stream", "assert same is not stream"),
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}

#[test]
fn native_self_return_requires_the_canonical_unshadowed_typing_binding() {
    let stream = STREAM.replace("Generic, TypeVar", "Generic, Self, TypeVar")
        + r#"

    @ContractOnly
    def same(self) -> Self:
        Ensures(Result() is self)
        Exsures(Exception, True)
        ...
"#;
    for invalid in [
        stream.replace("Generic, Self, TypeVar", "Generic, TypeVar"),
        stream.replace(
            "class Feed(Generic[T]):",
            "class Self:\n    pass\n\nclass Feed(Generic[T]):",
        ),
        stream.replace(
            "class Feed(Generic[T]):",
            "class Feed(Generic[T]):\n    Self: int",
        ),
    ] {
        let response = verify_with(
            &[("provider", PROVIDER), ("native_stream", &invalid)],
            SOURCE,
        );
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{response:#?}"
        );
    }
}

const OBJECT_PROVIDER: &str = r#"from native_stream import Feed
from nagini_contracts.contracts import ContractOnly, Exsures

@ContractOnly
def open_objects() -> Feed[object]:
    Exsures(Exception, True)
    ...
"#;

const OBJECT_INPUT: &str = r#"from provider import open_objects

def run() -> int:
    try:
        stream = open_objects()
        result = stream.accept(7)
    except Exception:
        return 0
    assert result == 7
    return result
"#;

#[test]
fn native_generic_object_input_keeps_actual_scalar_sort_and_contract() {
    for value in ["7", "'text'", "True", "None", "b'bytes'"] {
        let source = OBJECT_INPUT.replace("stream.accept(7)", &format!("stream.accept({value})"));
        let response = verify(OBJECT_PROVIDER, &source);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{value}: {response:#?}"
        );
        let response = verify(
            OBJECT_PROVIDER,
            &source.replace("assert result == 7", "assert result == 8"),
        );
        assert!(
            matches!(response.status, ProofStatus::Refuted),
            "{value}: {response:#?}"
        );
    }
}

#[test]
fn native_generic_object_input_retains_exception_paths() {
    let source = r#"from provider import open_objects

def run() -> int:
    try:
        stream = open_objects()
    except Exception:
        return 0
    return stream.accept(7)
"#;
    let response = verify(OBJECT_PROVIDER, source);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|o| o.id.contains("exception-undeclared") && o.counterexample.is_some())
    );
}

#[test]
fn native_generic_object_results_cannot_be_narrowed_to_heap_references() {
    let source = r#"from provider import open_objects

def run() -> int:
    try:
        stream = open_objects()
        value = stream.next()
    except Exception:
        return 0
    assert value is not None
    return 1
"#;
    for return_type in ["T", "Optional[T]", "Tuple[T, int]"] {
        let stream = STREAM
            .replace("Generic, TypeVar", "Generic, Optional, Tuple, TypeVar")
            .replace(
                "def next(self) -> T:",
                &format!("def next(self) -> {return_type}:"),
            );
        let response = verify_with(
            &[("provider", OBJECT_PROVIDER), ("native_stream", &stream)],
            source,
        );
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{return_type}: {response:#?}"
        );
        assert!(
            response
                .diagnostics
                .iter()
                .any(|d| d.code == "frontend.python.heap.native-object-result-unsupported"),
            "{return_type}: {response:#?}"
        );
    }
}

#[test]
fn native_generic_object_fields_cannot_use_reference_only_heap_storage() {
    let stream = STREAM.replace(
        "class Feed(Generic[T]):",
        "class Feed(Generic[T]):\n    value: T",
    );
    let response = verify_with(
        &[("provider", OBJECT_PROVIDER), ("native_stream", &stream)],
        OBJECT_INPUT,
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|d| d.code == "frontend.python.heap.generic-field-value-shape-unsupported"),
        "{response:#?}"
    );
}

#[test]
fn native_generic_object_specialization_does_not_erase_other_payload_identity() {
    let provider = OBJECT_PROVIDER.to_owned()
        + r#"

@ContractOnly
def accept_ints(stream: Feed[int]) -> Feed[int]:
    Exsures(Exception, True)
    ...

@ContractOnly
def open_ints() -> Feed[int]:
    Exsures(Exception, True)
    ...
"#;
    let source = OBJECT_INPUT
        .replace(
            "from provider import open_objects",
            "from provider import open_objects, accept_ints",
        )
        .replace("result = stream.accept(7)", "result = accept_ints(stream)")
        .replace("    assert result == 7\n    return result", "    return 0");
    let positive = verify(&provider, &source.replace("open_objects", "open_ints"));
    assert!(
        matches!(positive.status, ProofStatus::Proved),
        "{positive:#?}"
    );
    let response = verify(&provider, &source);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|d| d.code == "frontend.python.typecheck.arg-type"),
        "{response:#?}"
    );
}

#[test]
fn native_object_input_preserves_float_parameters_without_inventing_literal_support() {
    let source = OBJECT_INPUT
        .replace("def run() -> int:", "def run(value: float) -> int:")
        .replace("stream.accept(7)", "stream.accept(value)");
    let response = verify(OBJECT_PROVIDER, &source);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let response = verify(
        OBJECT_PROVIDER,
        &source.replace("assert result == 7", "assert result == 8"),
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    let response = verify(
        OBJECT_PROVIDER,
        &OBJECT_INPUT.replace("stream.accept(7)", "stream.accept(0.5)"),
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|d| d.code == "frontend.python.heap.expression-unsupported")
    );
}

#[test]
fn native_constructor_keeps_imported_generic_argument_identity_and_effects() {
    let wrapper = r#"from native_stream import Feed
from nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Result

class Box:
    @ContractOnly
    def __init__(self, stream: Feed[object]) -> None:
        Exsures(Exception, True)
        ...

    @ContractOnly
    def read(self) -> int:
        Ensures(Result() == 7)
        Exsures(Exception, True)
        ...
"#;
    let source = OBJECT_INPUT
        .replace(
            "from provider import open_objects",
            "from provider import open_objects\nfrom wrapper import Box",
        )
        .replace(
            "result = stream.accept(7)",
            "box = Box(stream)\n        result = box.read()",
        );
    for (source, good) in [
        (&source, true),
        (
            &source.replace("assert result == 7", "assert result == 8"),
            false,
        ),
    ] {
        let response = verify_with(
            &[
                ("provider", OBJECT_PROVIDER),
                ("native_stream", STREAM),
                ("wrapper", wrapper),
            ],
            source,
        );
        assert!(
            matches!(
                (&response.status, good),
                (ProofStatus::Proved, true) | (ProofStatus::Refuted, false)
            ),
            "{response:#?}"
        );
    }
}

#[test]
fn native_constructor_still_refuses_unbound_forward_class_annotations() {
    let provider = r#"from nagini_contracts.contracts import ContractOnly, Exsures

class Box:
    @ContractOnly
    def __init__(self, value: Later) -> None:
        Exsures(Exception, True)
        ...

class Later:
    pass
"#;
    let response = verify_with(
        &[("provider", provider)],
        "from provider import Box\n\ndef run() -> int:\n    return 0\n",
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|d| d.code == "frontend.python.heap.method-annotation-class-unresolved"),
        "{response:#?}"
    );
}
