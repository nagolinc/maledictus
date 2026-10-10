use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, SourceFile,
};
use std::fs;

const PROVIDER: &str = r#"from nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Requires, Result

class Resource:
    @ContractOnly
    def __enter__(self) -> 'Resource':
        Ensures(Result() is self)
        ...

    @ContractOnly
    def __exit__(self, exc_type: object, exc: object, tb: object) -> None:
        ...

@ContractOnly
def open_resource() -> Resource:
    ...
"#;

fn verify(provider: &str, source: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
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
        external_contract_overlays: vec![ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: if provider.contains("Exsures(") {
                ExternalExceptionPolicy::DeclaredByExsures
            } else {
                ExternalExceptionPolicy::AssumeNoException
            },
        }],
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    })
}

fn expect(provider: &str, source: &str, expected: ProofStatus) {
    let response = verify(provider, source);
    assert_eq!(
        std::mem::discriminant(&response.status),
        std::mem::discriminant(&expected),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
}

#[test]
fn none_exit_preserves_normal_return_and_does_not_suppress_body_exception() {
    expect(
        PROVIDER,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        return 7\n",
        ProofStatus::Proved,
    );
    expect(
        PROVIDER,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        raise Exception()\n",
        ProofStatus::Refuted,
    );
    expect(
        PROVIDER,
        "from provider import open_resource\n\ndef run() -> int:\n    try:\n        with open_resource():\n            raise Exception()\n    except Exception:\n        return 7\n",
        ProofStatus::Proved,
    );
}

#[test]
fn optional_boolean_exit_checks_both_suppressed_and_propagating_paths() {
    let provider = PROVIDER.replace("tb: object) -> None:", "tb: object) -> bool | None:");
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        raise Exception()\n    return 1\n",
        ProofStatus::Refuted,
    );
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    try:\n        with open_resource():\n            raise Exception()\n    except Exception:\n        return 2\n    return 1\n",
        ProofStatus::Proved,
    );
}

#[test]
fn optional_exit_cannot_discard_the_only_non_suppressing_none_path() {
    let provider = PROVIDER.replace(
        "tb: object) -> None:\n        ...",
        "tb: object) -> bool | None:\n        Ensures(Result() is not False)\n        ...",
    );
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        raise Exception()\n    return 1\n",
        ProofStatus::Refuted,
    );
}

#[test]
fn boolean_exit_identity_does_not_admit_numeric_identity_as_value_equality() {
    let provider = PROVIDER.replace(
        "tb: object) -> None:\n        ...",
        "tb: object) -> bool:\n        Ensures(Result() is not 1)\n        ...",
    );
    let response = verify(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    resource = open_resource()\n    value = resource.__exit__(None, None, None)\n    assert value == False\n    return 1\n",
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|d| d.code == "frontend.python.heap.result-identity-external-unsupported"),
        "{response:#?}"
    );
}

#[test]
fn stdlib_context_and_traceback_effect_overlays_preserve_full_typeshed_and_reject_owned_shadows() {
    for shadow in [None, Some("contextlib"), Some("types")] {
        let directory = tempfile::tempdir().unwrap();
        fs::write(directory.path().join("app.py"), "from contextlib import AbstractContextManager, ExitStack\nfrom types import TracebackType, FunctionType\n\ndef run(stack: ExitStack, manager: AbstractContextManager[int], tb: TracebackType, callback: FunctionType) -> str:\n    return callback.__name__\n").unwrap();
        let contracts = [
            ("contextlib", "class AbstractContextManager:\n    pass\n"),
            ("types", "class TracebackType:\n    pass\n"),
        ];
        let overlays = contracts
            .iter()
            .map(|(module, contract)| {
                let stub = format!("{module}_contract.py");
                fs::write(directory.path().join(&stub), contract).unwrap();
                ExternalOverlay {
                    adapter_path: "app.py".to_owned(),
                    module: (*module).to_owned(),
                    stub_path: stub,
                    exception_policy: ExternalExceptionPolicy::AssumeNoException,
                }
            })
            .collect::<Vec<_>>();
        if let Some(module) = shadow {
            fs::write(
                directory.path().join(format!("{module}.py")),
                "raise RuntimeError('owned source is not a native premise')\n",
            )
            .unwrap();
        }
        let result = maledictus::python_typecheck::typecheck_request_sources(
            directory.path(),
            &[SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            }],
            &overlays,
        );
        if shadow.is_some() {
            assert_eq!(
                result.unwrap_err().code,
                "frontend.python.typecheck.overlay-source-conflict"
            );
        } else {
            let result = result.unwrap().unwrap();
            assert!(result.passed(), "{result:#?}");
        }
    }
}

#[test]
fn true_exit_suppresses_exception_but_preserves_pending_return() {
    let provider = PROVIDER.replace(
        "tb: object) -> None:\n        ...",
        "tb: object) -> bool:\n        Ensures(Result() == True)\n        ...",
    );
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        raise Exception()\n    return 1\n",
        ProofStatus::Proved,
    );
    expect(
        &provider,
        "from provider import open_resource\nfrom nagini_contracts.contracts import Ensures, Result\n\ndef run() -> int:\n    Ensures(Result() == 7)\n    with open_resource():\n        return 7\n    return 0\n",
        ProofStatus::Proved,
    );
}

#[test]
fn exception_exit_receives_non_null_traceback() {
    // If the verifier invents tb=None for a raised body exception, this
    // provider would incorrectly suppress it and prove the unsafe caller.
    let provider = PROVIDER.replace(
        "tb: object) -> None:\n        ...",
        "tb: object) -> bool:\n        Ensures(Result() == (tb is None))\n        ...",
    );
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        raise Exception()\n    return 1\n",
        ProofStatus::Refuted,
    );
}

#[test]
fn normal_exit_receives_three_none_values() {
    let provider = PROVIDER.replace("tb: object) -> None:\n        ...", "tb: object) -> None:\n        Requires(exc_type is None and exc is None and tb is None)\n        ...");
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        return 7\n",
        ProofStatus::Proved,
    );
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        try:\n            raise Exception()\n        except Exception:\n            return 7\n",
        ProofStatus::Proved,
    );
}

#[test]
fn untyped_exception_metaclass_contract_is_refused_until_typed_class_objects_are_modeled() {
    let provider = PROVIDER.replace("tb: object) -> None:\n        ...", "tb: object) -> bool:\n        Ensures(Result() == (exc_type is not type(exc)))\n        ...");
    let response = verify(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        raise Exception()\n    return 1\n",
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|d| d.code == "frontend.python.heap.reference-comparison-type-mismatch"),
        "{response:#?}"
    );
}

#[test]
fn cleanup_exception_is_not_misclassified_as_original_body_exception() {
    let provider = format!(
        "{}\nclass BodyError(Exception):\n    pass\n\nclass ExitError(Exception):\n    pass\n",
        PROVIDER.replace(
            "tb: object) -> None:\n        ...",
            "tb: object) -> None:\n        Exsures(ExitError, True)\n        ..."
        )
    );
    expect(
        &provider,
        "from provider import open_resource\n\nclass BodyError(Exception):\n    pass\n\ndef run() -> int:\n    try:\n        with open_resource():\n            raise BodyError()\n    except BodyError:\n        return 1\n",
        ProofStatus::Refuted,
    );
}

#[test]
fn unsupported_context_manager_loops_refuse_instead_of_ignoring_cleanup() {
    let provider = PROVIDER.replace(
        "tb: object) -> None:\n        ...",
        "tb: object) -> None:\n        Exsures(Exception, True)\n        ...",
    );
    for jump in ["break", "continue"] {
        let source = format!(
            "from provider import open_resource\n\ndef run() -> int:\n    for i in [0, 1]:\n        with open_resource():\n            {jump}\n    return 7\n"
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
                .any(|d| d.code == "frontend.python.heap.symbolic-for-iterable-unsupported"),
            "{response:#?}"
        );
    }
}

#[test]
fn cleanup_failure_overrides_pending_return_or_body_exception() {
    let provider = PROVIDER.replace(
        "tb: object) -> None:\n        ...",
        "tb: object) -> None:\n        Exsures(Exception, True)\n        ...",
    );
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        return 7\n",
        ProofStatus::Refuted,
    );
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    try:\n        with open_resource():\n            return 7\n    except Exception:\n        return 0\n",
        ProofStatus::Proved,
    );
}

#[test]
fn entry_failure_skips_exit() {
    // Both entry failure and success are possible. An impossible exit
    // precondition makes the success path fail; entry failure still escapes.
    let provider = PROVIDER
        .replace(
            "Ensures(Result() is self)",
            "Ensures(False)\n        Exsures(Exception, True)",
        )
        .replace(
            "tb: object) -> None:\n        ...",
            "tb: object) -> None:\n        Requires(False)\n        ...",
        );
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    try:\n        with open_resource():\n            return 7\n    except Exception:\n        return 0\n",
        ProofStatus::Proved,
    );
    expect(
        &provider,
        "from provider import open_resource\n\ndef run() -> int:\n    with open_resource():\n        return 7\n",
        ProofStatus::Refuted,
    );
}
