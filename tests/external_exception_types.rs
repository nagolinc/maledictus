use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, SourceFile,
};
use std::fs;

const TYPES: &str = "class TracebackType:\n    pass\n";
const CONTEXT: &str = r#"from types import TracebackType
from typing import Generic, TypeVar
from nagini_contracts.contracts import ContractOnly, Exsures
T = TypeVar('T')
class AbstractContextManager(Generic[T]):
    @ContractOnly
    def __enter__(self) -> T:
        Exsures(Exception, True)
        ...
    @ContractOnly
    def __exit__(self, exc_type: type[BaseException] | None, exc_value: BaseException | None, traceback: TracebackType | None) -> bool | None:
        Exsures(Exception, True)
        ...
"#;
const PROVIDER: &str = r#"from types import TracebackType
from nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Result
class Resource:
    @ContractOnly
    def __enter__(self) -> 'Resource':
        Ensures(Result() is self)
        Exsures(Exception, True)
        ...
    @ContractOnly
    def __exit__(self, exc_type: type[BaseException] | None, exc_value: BaseException | None, traceback: TracebackType | None) -> None:
        Exsures(Exception, True)
        ...
@ContractOnly
def open_resource() -> Resource:
    Exsures(Exception, True)
    ...
"#;

fn verify(contracts: &[(&str, &str)], source: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("app.py"), source).unwrap();
    let overlays = contracts
        .iter()
        .map(|(module, contract)| {
            let stub = format!("{}_contract.py", module.replace('.', "_"));
            fs::write(directory.path().join(&stub), contract).unwrap();
            ExternalOverlay {
                adapter_path: "app.py".to_owned(),
                module: (*module).to_owned(),
                stub_path: stub,
                exception_policy: if contract.contains("Exsures(") {
                    ExternalExceptionPolicy::DeclaredByExsures
                } else {
                    ExternalExceptionPolicy::AssumeNoException
                },
            }
        })
        .collect();
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

#[test]
fn typed_exception_triple_composes_on_normal_and_exceptional_body_exit() {
    for body in ["return 7", "raise Exception()"] {
        let source = format!(
            "from provider import open_resource\n\ndef run() -> int:\n    try:\n        with open_resource():\n            {body}\n    except Exception:\n        return 0\n"
        );
        let response = verify(&[("provider", PROVIDER), ("types", TYPES)], &source);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
    }
}

#[test]
fn typed_cleanup_does_not_remove_body_or_cleanup_exceptions() {
    let source = "from provider import open_resource\n\ndef run() -> int:\n    resource = open_resource()\n    with resource:\n        raise Exception()\n";
    let response = verify(&[("provider", PROVIDER), ("types", TYPES)], source);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}

#[test]
fn native_context_generic_keeps_response_type_and_cleanup_paths() {
    let provider = r#"from contextlib import AbstractContextManager
from nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Result
class Response:
    @ContractOnly
    def read(self) -> int:
        Ensures(Result() == 7)
        Exsures(Exception, True)
        ...
@ContractOnly
def open_resource() -> AbstractContextManager[Response]:
    Exsures(Exception, True)
    ...
"#;
    let source = "from provider import open_resource\n\ndef run() -> int:\n    result = 0\n    try:\n        with open_resource() as response:\n            result = response.read()\n    except Exception:\n        return 0\n    assert result == 0 or result == 7\n    return result\n";
    let contracts = [
        ("provider", provider),
        ("contextlib", CONTEXT),
        ("types", TYPES),
    ];
    let response = verify(&contracts, source);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let response = verify(
        &contracts,
        &source.replace("result == 0 or result == 7", "result == 9"),
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}

#[test]
fn typed_exit_receives_matching_exception_class_and_instance() {
    let provider = PROVIDER.replace("        Exsures(Exception, True)\n", "")
        .replace("traceback: TracebackType | None) -> None:\n        ...", "traceback: TracebackType | None) -> bool:\n        Ensures(Result() == (exc_type is not type(exc_value)))\n        ...");
    let source = "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        raise Exception()\n    return 1\n";
    let response = verify(&[("provider", &provider), ("types", TYPES)], source);
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
fn typed_normal_exit_keeps_all_none_arguments() {
    let provider = PROVIDER.replace("Ensures, Exsures", "Ensures, Requires, Exsures")
        .replace("traceback: TracebackType | None) -> None:\n", "traceback: TracebackType | None) -> None:\n        Requires(exc_type is None and exc_value is None and traceback is None)\n");
    let source = "from provider import open_resource\n\ndef run() -> int:\n    try:\n        with open_resource():\n            return 7\n    except Exception:\n        return 0\n";
    let response = verify(&[("provider", &provider), ("types", TYPES)], source);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
}

#[test]
fn missing_traceback_effect_interface_cannot_be_filled_by_typeshed_alone() {
    let source = "from provider import open_resource\n\ndef run() -> int:\n    try:\n        with open_resource():\n            return 7\n    except Exception:\n        return 0\n";
    let response = verify(&[("provider", PROVIDER)], source);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
}

#[test]
fn native_exception_result_and_builtin_shadow_are_refused() {
    for source in [
        "from nagini_contracts.contracts import ContractOnly\nclass Source:\n    @ContractOnly\n    def read(self) -> type[BaseException]:\n        ...\n",
        "from nagini_contracts.contracts import ContractOnly\nclass BaseException:\n    pass\nclass Source:\n    @ContractOnly\n    def accept(self, value: type[BaseException]) -> None:\n        ...\n",
    ] {
        let failure = maledictus::python_heap_contracts::parse_external_heap_contract_module(
            source,
            "provider_contract.py",
            "provider",
        )
        .unwrap_err();
        assert!(
            matches!(
                failure.code,
                "frontend.python.heap.native-exception-result-unsupported"
                    | "frontend.python.heap.native-exception-type-shadowed"
            ),
            "{failure:#?}"
        );
    }
}

#[test]
fn source_exception_fields_cannot_acquire_unmodeled_native_frame_guarantees() {
    let provider = PROVIDER.replace("        Exsures(Exception, True)\n", "");
    let source = "from provider import open_resource\nfrom nagini_contracts.contracts import Acc, Ensures\n\nclass Failure(Exception):\n    code: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.code))\n        self.code = 1\n\ndef run() -> int:\n    try:\n        with open_resource():\n            raise Failure()\n    except Exception:\n        return 0\n";
    let response = verify(&[("provider", &provider), ("types", TYPES)], source);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.diagnostics.iter().any(|d| d.code == "frontend.python.heap.native-exception-argument-effects-unsupported"), "{response:#?}");
}

#[test]
fn exception_class_parameters_are_checked_for_native_constructors_and_factories() {
    let provider = "from nagini_contracts.contracts import ContractOnly, Exsures\nclass Resource:\n    @ContractOnly\n    def __init__(self, exc_type: type[BaseException] | None = None) -> None:\n        Exsures(Exception, True)\n        ...\n@ContractOnly\ndef open_resource(exc_type: type[BaseException] | None = None) -> Resource:\n    Exsures(Exception, True)\n    ...\n";
    for argument in ["", "None", "Exception"] {
        let source = format!(
            "from provider import Resource, open_resource\n\ndef run() -> int:\n    try:\n        a = Resource({argument})\n        b = open_resource({argument})\n    except Exception:\n        return 0\n    return 1\n"
        );
        let response = verify(&[("provider", provider)], &source);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
    }
}

#[test]
fn native_exception_bounds_reject_wider_and_shadowed_classes() {
    let provider = "from nagini_contracts.contracts import ContractOnly\nclass Resource:\n    @ContractOnly\n    def __init__(self, exc_type: type[ValueError]) -> None:\n        ...\n@ContractOnly\ndef open_resource(exc_type: type[ValueError]) -> Resource:\n    ...\n";
    for prefix in ["", "class ValueError(Exception):\n    pass\n\n"] {
        for argument in ["Exception", "BaseException", "ValueError"] {
            if prefix.is_empty() && argument == "ValueError" {
                continue;
            }
            for constructor in ["Resource", "open_resource"] {
                let source = format!(
                    "from provider import Resource, open_resource\n\n{prefix}def run() -> int:\n    value = {constructor}({argument})\n    return 1\n"
                );
                let response = verify(&[("provider", provider)], &source);
                assert!(
                    matches!(response.status, ProofStatus::Refused),
                    "source: {source}\n{response:#?}"
                );
            }
        }
    }
}

#[test]
fn provider_local_payload_names_do_not_collide_inside_foreign_generic_contexts() {
    let provider = "from contextlib import AbstractContextManager\nfrom nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Result\nclass Response:\n    @ContractOnly\n    def read(self) -> int:\n        Ensures(Result() == 7)\n        Exsures(Exception, True)\n        ...\n@ContractOnly\ndef open_resource() -> AbstractContextManager[Response]:\n    Exsures(Exception, True)\n    ...\n";
    let second = provider.replace("Result() == 7", "Result() == 9");
    let source = "import first\nimport second\n\ndef run() -> int:\n    a = 0\n    b = 0\n    try:\n        with first.open_resource() as response_one:\n            a = response_one.read()\n        with second.open_resource() as response_two:\n            b = response_two.read()\n    except Exception:\n        return 0\n    assert a == 0 or a == 7\n    assert b == 0 or b == 9\n    return a + b\n";
    let contracts = [
        ("first", provider),
        ("second", second.as_str()),
        ("contextlib", CONTEXT),
        ("types", TYPES),
    ];
    let response = verify(&contracts, source);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let response = verify(&contracts, &source.replace("a == 7", "a == 9"));
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}
