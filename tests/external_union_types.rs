use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, SourceFile,
};
use std::fs;

const FEED: &str = r#"from typing import Generic, TypeVar
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

const PROVIDER: &str = r#"from native_feed import Feed
from nagini_contracts.contracts import ContractOnly, Exsures

@ContractOnly
def open_feed() -> Feed[str | int | float | bool | None]:
    Exsures(Exception, True)
    ...
"#;

const SOURCE: &str = r#"from provider import open_feed

def run() -> int:
    try:
        feed = open_feed()
        value = feed.next()
        result = feed.accept(value)
    except Exception:
        return 0
    assert result == 7
    return result
"#;

fn verify(feed: &str, provider: &str, source: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("native_feed_contract.py"), feed).unwrap();
    fs::write(directory.path().join("provider_contract.py"), provider).unwrap();
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
        external_contract_overlays: vec![
            ExternalOverlay {
                adapter_path: "app.py".to_owned(),
                module: "provider".to_owned(),
                stub_path: "provider_contract.py".to_owned(),
                exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
            },
            ExternalOverlay {
                adapter_path: "app.py".to_owned(),
                module: "native_feed".to_owned(),
                stub_path: "native_feed_contract.py".to_owned(),
                exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
            },
        ],
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    })
}

#[test]
fn native_generic_closed_union_round_trip_keeps_every_value_alternative() {
    let response = verify(FEED, PROVIDER, SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some());
}

#[test]
fn native_union_does_not_invent_values_or_remove_exceptions() {
    let response = verify(
        FEED,
        PROVIDER,
        &SOURCE.replace("assert result == 7", "assert result == 8"),
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    let source = r#"from provider import open_feed

def run() -> int:
    try:
        feed = open_feed()
    except Exception:
        return 0
    value = feed.next()
    try:
        return feed.accept(value)
    except Exception:
        return 0
"#;
    let response = verify(FEED, PROVIDER, source);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|o| o.id.contains("exception-undeclared") && o.counterexample.is_some()),
        "{response:#?}"
    );
}

#[test]
fn native_union_rejects_values_outside_the_closed_set() {
    let response = verify(
        FEED,
        PROVIDER,
        &SOURCE.replace(
            "feed.accept(value)",
            "feed.accept(b'not a permitted alternative')",
        ),
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
}

#[test]
fn native_union_checks_both_none_and_non_none_paths() {
    for assertion in ["assert value is None", "assert value is not None"] {
        // The assertion must be outside the exception handler: AssertionError
        // is an ordinary exception and an application may intentionally catch it.
        let source = format!(
            "from provider import open_feed\n\ndef run() -> int:\n    try:\n        feed = open_feed()\n        value = feed.next()\n    except Exception:\n        return 0\n    {assertion}\n    return 1\n"
        );
        let response = verify(FEED, PROVIDER, &source);
        assert!(
            matches!(response.status, ProofStatus::Refuted),
            "{assertion}: {response:#?}"
        );
    }
}

#[test]
fn native_union_without_declared_exceptions_still_splits_result_paths() {
    let feed = FEED.replace(
        "def next(self) -> T:\n        Exsures(Exception, True)",
        "def next(self) -> T:",
    );
    let response = verify(&feed, PROVIDER, SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let source = "from provider import open_feed\n\ndef run() -> int:\n    try:\n        feed = open_feed()\n    except Exception:\n        return 0\n    value = feed.next()\n    assert value is not None\n    return 1\n";
    let response = verify(&feed, PROVIDER, source);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}

#[test]
fn unsupported_nested_union_storage_is_refused() {
    for feed in [
        FEED.replace(
            "class Feed(Generic[T]):",
            "class Feed(Generic[T]):\n    value: T",
        ),
        FEED.replace("def next(self) -> T:", "def next(self) -> tuple[T, int]:"),
        FEED.replace("def next(self) -> T:", "def next(self) -> list[T]:"),
    ] {
        let source = "from provider import open_feed\n\ndef run() -> int:\n    try:\n        feed = open_feed()\n        value = feed.next()\n    except Exception:\n        return 0\n    return 1\n";
        let response = verify(&feed, PROVIDER, source);
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{response:#?}"
        );
    }
}

#[test]
fn native_generic_fixed_tuple_keeps_element_types_and_order() {
    let provider = PROVIDER.replace("str | int | float | bool | None", "tuple[str, bytes, str]");
    let response = verify(FEED, &provider, SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let response = verify(
        FEED,
        &provider,
        &SOURCE.replace(
            "feed.accept(value)",
            "feed.accept((b'wrong', 'order', 'mime'))",
        ),
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
}

const TIMEOUT_PROVIDER: &str = r#"

class Timeout:
    @ContractOnly
    def __init__(self) -> None:
        Exsures(Exception, True)
        ...

class Client:
    @ContractOnly
    def __init__(self, *, timeout: float | Timeout | None = None) -> None:
        Exsures(Exception, True)
        ...

    @ContractOnly
    def accept(self, timeout: float | Timeout | None = None) -> int:
        Ensures(Result() == 7)
        Exsures(Exception, True)
        ...
"#;

#[test]
fn mixed_scalar_nominal_none_parameters_keep_defaults_and_native_identity() {
    let provider = PROVIDER.replace(
        "ContractOnly, Exsures",
        "ContractOnly, Ensures, Exsures, Result",
    ) + TIMEOUT_PROVIDER;
    for (construction, argument) in [
        ("Client()", ""),
        ("Client(timeout=None)", "None"),
        ("Client(timeout=delay)", "delay"),
        ("Client(timeout=timeout)", "timeout"),
    ] {
        let source = format!(
            "from provider import Client, Timeout\n\ndef run(delay: float) -> int:\n    try:\n        timeout = Timeout()\n        client = {construction}\n        result = client.accept({argument})\n    except Exception:\n        return 0\n    assert result == 7\n    return result\n"
        );
        let response = verify(FEED, &provider, &source);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{construction}, {argument}: {response:#?}"
        );
    }
}

#[test]
fn nominal_union_parameter_does_not_assume_mutable_argument_frames() {
    let provider = PROVIDER.replace(
        "ContractOnly, Exsures",
        "ContractOnly, Ensures, Exsures, Result",
    ) + &TIMEOUT_PROVIDER
        .replace("class Timeout:", "class Timeout:\n    value: int");
    let source = "from provider import Client, Timeout\n\ndef run() -> int:\n    try:\n        timeout = Timeout()\n        client = Client(timeout=timeout)\n        result = client.accept(timeout)\n    except Exception:\n        return 0\n    return result\n";
    let response = verify(FEED, &provider, source);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|d| d.code == "frontend.python.heap.native-union-argument-effects-unsupported"),
        "{response:#?}"
    );
}

#[test]
fn exceptional_contract_cannot_claim_a_union_return_value() {
    let feed = FEED.replace(
        "def next(self) -> T:\n        Exsures(Exception, True)",
        "def next(self) -> T:\n        Exsures(Exception, Result() is None)",
    );
    let response = verify(&feed, PROVIDER, SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        maledictus::python_heap_contracts::parse_external_heap_contract_module(
            &feed,
            "native_feed_contract.py",
            "native_feed",
        )
        .is_err_and(
            |failure| failure.code == "frontend.python.heap.external-exception-result-unsupported"
        ),
        "invalid exception postcondition must be rejected in the defining provider"
    );
}

#[test]
fn native_union_getter_keeps_all_return_and_exception_paths() {
    let feed = FEED.replace(
        "    @ContractOnly\n    def next",
        "    @property\n    @ContractOnly\n    def next",
    );
    let source = SOURCE.replace("feed.next()", "feed.next");
    let response = verify(&feed, PROVIDER, &source);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let source = "from provider import open_feed\n\ndef run() -> int:\n    try:\n        feed = open_feed()\n        value = feed.next\n    except Exception:\n        return 0\n    assert value is not None\n    return 1\n";
    let response = verify(&feed, PROVIDER, source);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}

#[test]
fn native_factory_binds_mixed_union_arguments_without_erasing_the_return_type() {
    let provider = PROVIDER.replace("ContractOnly, Exsures", "ContractOnly, Ensures, Exsures, Result")
        .replace("@ContractOnly\ndef open_feed()", &format!("{TIMEOUT_PROVIDER}\n@ContractOnly\ndef open_feed(*, timeout: float | Timeout | None = None)"));
    for argument in ["", "timeout=None", "timeout=delay", "timeout=timeout"] {
        let source = SOURCE
            .replace(
                "from provider import open_feed",
                "from provider import open_feed, Timeout",
            )
            .replace("def run()", "def run(delay: float)")
            .replace(
                "feed = open_feed()",
                &format!("timeout = Timeout()\n        feed = open_feed({argument})"),
            );
        let response = verify(FEED, &provider, &source);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{argument}: {response:#?}"
        );
    }
}

#[test]
fn native_specialization_rules_do_not_replace_owned_generic_body_proofs() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("owned.py"), "from typing import Generic, TypeVar\n\nT = TypeVar('T')\n\nclass Echo(Generic[T]):\n    def same(self, value: T) -> T:\n        return value\n").unwrap();
    fs::write(directory.path().join("app.py"), "from owned import Echo\n\ndef run() -> None:\n    echo = Echo[int | str]()\n    echo.same(1)\n").unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
            SourceFile {
                path: "owned.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec![],
            },
        ],
        external_contract_overlays: vec![],
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    });
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|d| d.code
            == "frontend.python.heap.source-generic-composite-specialization-unsupported"),
        "{response:#?}"
    );
}

#[test]
fn native_optional_generic_scalar_result_keeps_the_none_path_after_specialization() {
    let feed = FEED
        .replace("Generic, TypeVar", "Generic, Optional, TypeVar")
        .replace("def next(self) -> T:", "def next(self) -> Optional[T]:");
    maledictus::python_heap_contracts::parse_external_heap_contract_module(
        &feed,
        "native_feed_contract.py",
        "native_feed",
    )
    .unwrap();
    let provider = PROVIDER.replace("Feed[str | int | float | bool | None]", "Feed[bool]");
    let response = verify(
        &feed,
        &provider,
        "from provider import open_feed\n\ndef run() -> int:\n    try:\n        feed = open_feed()\n        value = feed.next()\n    except Exception:\n        return 0\n    assert value is not None\n    return 1\n",
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}

#[test]
fn native_optional_generic_parameter_keeps_explicit_none_and_omitted_default() {
    let feed = FEED
        .replace("Generic, TypeVar", "Generic, Optional, TypeVar")
        .replace(
            "def accept(self, value: T)",
            "def accept(self, value: Optional[T] = None)",
        );
    let provider = PROVIDER.replace("Feed[str | int | float | bool | None]", "Feed[bool]");
    for arguments in ["", "None", "True"] {
        let source = format!(
            "from provider import open_feed\n\ndef run() -> int:\n    try:\n        feed = open_feed()\n        value = feed.accept({arguments})\n    except Exception:\n        return 0\n    assert value == 7\n    return 1\n"
        );
        let response = verify(&feed, &provider, &source);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
    }
}

#[test]
fn native_optional_generic_scalar_field_refuses_without_sum_storage() {
    let feed = FEED
        .replace("Generic, TypeVar", "Generic, Optional, TypeVar")
        .replace(
            "class Feed(Generic[T]):",
            "class Feed(Generic[T]):\n    value: Optional[T]",
        );
    let provider = PROVIDER.replace("Feed[str | int | float | bool | None]", "Feed[bool]");
    let response = verify(&feed, &provider, SOURCE);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
}
