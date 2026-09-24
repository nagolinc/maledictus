use std::fs;

use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofStatus,
    PythonCallableBinding, PythonCallableProvider, PythonCallableProviderResult, SourceFile,
};

const CONSUMER: &str = "from dataclasses import dataclass\nfrom typing import Callable\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Request:\n    value: str\n    enhance: Callable[[str], str]\n\n@dataclass(frozen=True)\nclass Completed:\n    value: str\n\n@dataclass(frozen=True)\nclass Rejected:\n    value: str\n\n@operation\ndef prepare(request: Request) -> Completed | Rejected:\n    try:\n        return Completed(request.enhance(request.value))\n    except ValueError:\n        return Rejected(request.value)\n";

fn source_request(
    directory: &tempfile::TempDir,
    provider: &str,
    with_binding: bool,
) -> ProofRequest {
    fs::write(directory.path().join("consumer.py"), CONSUMER).unwrap();
    fs::write(directory.path().join("provider.py"), provider).unwrap();
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "consumer.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["prepare".to_owned()],
            },
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["enhance".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        cross_language_bindings: Vec::new(),
        python_callable_bindings: if with_binding {
            vec![PythonCallableBinding {
                id: "prepare-enhancer".to_owned(),
                consumer_path: "consumer.py".to_owned(),
                operation_symbol: "prepare".to_owned(),
                input_record: "Request".to_owned(),
                field: "enhance".to_owned(),
                provider: PythonCallableProvider::Source {
                    path: "provider.py".to_owned(),
                    symbol: "enhance".to_owned(),
                },
            }]
        } else {
            Vec::new()
        },
    }
}

#[test]
fn public_verifier_composes_source_callback_returns_and_caught_exceptions() {
    let directory = tempfile::tempdir().unwrap();
    let request = source_request(
        &directory,
        "def enhance(value: str) -> str:\n    if value == 'bad':\n        raise ValueError('rejected')\n    return value + '!'\n",
        true,
    );

    let response = maledictus::verify(&request);

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let consumer = response
        .files
        .iter()
        .find(|file| file.path == "consumer.py")
        .unwrap();
    assert_eq!(
        consumer.fragment.as_deref(),
        Some("dagcert-closed-typed-operations/v3")
    );
    assert_eq!(response.python_callable_bindings.len(), 1);
    let binding = &response.python_callable_bindings[0];
    assert_eq!(binding.consumer_sha256, consumer.sha256);
    assert!(matches!(
        &binding.provider,
        PythonCallableProviderResult::Source { path, symbol, sha256 }
            if path == "provider.py" && symbol == "enhance" && sha256.len() == 64
    ));
}

#[test]
fn abstract_callable_and_uncaught_provider_exit_fail_closed() {
    let directory = tempfile::tempdir().unwrap();
    let abstract_request = source_request(
        &directory,
        "def enhance(value: str) -> str:\n    return value\n",
        false,
    );
    let abstract_response = maledictus::analyze_python_frontend(&abstract_request);
    assert!(matches!(
        abstract_response.disposition,
        maledictus::FrontendDisposition::Unsupported
    ));
    assert!(abstract_response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "frontend.python.dagcert.callable-binding-missing"
    }));

    let uncaught_request = source_request(
        &directory,
        "def enhance(value: str) -> str:\n    raise KeyboardInterrupt()\n",
        true,
    );
    let uncaught_response = maledictus::analyze_python_frontend(&uncaught_request);
    assert!(matches!(
        uncaught_response.disposition,
        maledictus::FrontendDisposition::Unsupported
    ));
    assert!(uncaught_response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "frontend.python.dagcert.operation-not-total"
            && diagnostic.message.contains("KeyboardInterrupt")
    }));
}

#[test]
fn provider_signature_and_body_are_authoritative_not_the_request() {
    let directory = tempfile::tempdir().unwrap();
    for provider in [
        "def enhance(value: int) -> str:\n    return 'wrong input'\n",
        "def enhance(value: str) -> int:\n    return 1\n",
        "def enhance(value: str) -> str:\n    alias = value\n    return alias\n",
        "def enhance(*values: str) -> str:\n    return 'variadic'\n",
        "async def enhance(value: str) -> str:\n    return value\n",
    ] {
        let response =
            maledictus::analyze_python_frontend(&source_request(&directory, provider, true));
        assert!(
            matches!(
                response.disposition,
                maledictus::FrontendDisposition::Unsupported
            ),
            "provider unexpectedly verified:\n{provider}\n{response:#?}"
        );
    }
}

#[test]
fn explicit_external_contract_supplies_signature_and_exception_union() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("consumer.py"), CONSUMER).unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef enhance(value: str) -> str:\n    Exsures(ValueError, True)\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "consumer.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["prepare".to_owned()],
        }],
        external_contract_overlays: vec![ExternalOverlay {
            adapter_path: "consumer.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
        }],
        cross_language_bindings: Vec::new(),
        python_callable_bindings: vec![PythonCallableBinding {
            id: "external-enhancer".to_owned(),
            consumer_path: "consumer.py".to_owned(),
            operation_symbol: "prepare".to_owned(),
            input_record: "Request".to_owned(),
            field: "enhance".to_owned(),
            provider: PythonCallableProvider::ExternalContract {
                module: "provider".to_owned(),
                symbol: "enhance".to_owned(),
            },
        }],
    };

    let response = maledictus::analyze_python_frontend(&request);

    assert!(
        matches!(
            response.disposition,
            maledictus::FrontendDisposition::Supported
        ),
        "{response:#?}"
    );
    assert!(matches!(
        &response.python_callable_bindings[0].provider,
        PythonCallableProviderResult::ExternalContract {
            module,
            symbol,
            stub_sha256,
            ..
        } if module == "provider" && symbol == "enhance" && stub_sha256.len() == 64
    ));
}

#[test]
fn every_callable_field_binding_is_validated_even_when_the_field_is_not_invoked() {
    let directory = tempfile::tempdir().unwrap();
    let consumer = CONSUMER.replace(
        "    try:\n        return Completed(request.enhance(request.value))\n    except ValueError:\n        return Rejected(request.value)\n",
        "    return Completed(request.value)\n",
    );
    fs::write(directory.path().join("consumer.py"), consumer).unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "def enhance(value: int) -> str:\n    return 'wrong'\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "consumer.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["prepare".to_owned()],
            },
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["enhance".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        cross_language_bindings: Vec::new(),
        python_callable_bindings: vec![PythonCallableBinding {
            id: "unused-but-bound".to_owned(),
            consumer_path: "consumer.py".to_owned(),
            operation_symbol: "prepare".to_owned(),
            input_record: "Request".to_owned(),
            field: "enhance".to_owned(),
            provider: PythonCallableProvider::Source {
                path: "provider.py".to_owned(),
                symbol: "enhance".to_owned(),
            },
        }],
    };

    let response = maledictus::analyze_python_frontend(&request);
    assert!(matches!(
        response.disposition,
        maledictus::FrontendDisposition::Unsupported
    ));
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "frontend.python.dagcert.callable-binding-type-mismatch"
    }));
}

#[test]
fn same_file_source_callback_identity_is_checked_without_treating_glue_as_an_operation() {
    let directory = tempfile::tempdir().unwrap();
    let source = format!("def enhance(value: str) -> str:\n    return value + '!'\n\n{CONSUMER}");
    fs::write(directory.path().join("app.py"), source).unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["enhance".to_owned(), "prepare".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        cross_language_bindings: Vec::new(),
        python_callable_bindings: vec![PythonCallableBinding {
            id: "same-file-enhancer".to_owned(),
            consumer_path: "app.py".to_owned(),
            operation_symbol: "prepare".to_owned(),
            input_record: "Request".to_owned(),
            field: "enhance".to_owned(),
            provider: PythonCallableProvider::Source {
                path: "app.py".to_owned(),
                symbol: "enhance".to_owned(),
            },
        }],
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("dagcert-closed-typed-operations/v3")
    );
}

#[test]
fn passed_at_construction_dependencies_compose_across_multiple_typed_local_results() {
    let directory = tempfile::tempdir().unwrap();
    let consumer = "from dataclasses import dataclass\nfrom typing import Callable\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Request:\n    value: str\n    select: Callable[[str], str]\n    reserve: Callable[[str], bool]\n    enhance: Callable[[str], str]\n\n@dataclass(frozen=True)\nclass Completed:\n    value: str\n\n@dataclass(frozen=True)\nclass Rejected:\n    value: str\n\n@operation\ndef prepare(request: Request) -> Completed | Rejected:\n    try:\n        selected: str = request.select(request.value)\n        reserved: bool = request.reserve(selected)\n        if reserved:\n            enhanced: str = request.enhance(selected)\n            return Completed(enhanced)\n        return Rejected(selected)\n    except BaseException:\n        return Rejected(request.value)\n";
    fs::write(directory.path().join("consumer.py"), consumer).unwrap();
    for (path, source) in [
        (
            "selector.py",
            "def select(value: str) -> str:\n    if value == 'missing':\n        raise LookupError('missing')\n    return value\n",
        ),
        (
            "reserver.py",
            "def reserve(value: str) -> bool:\n    if value == 'busy':\n        raise RuntimeError('busy')\n    return value != ''\n",
        ),
        (
            "enhancer.py",
            "def enhance(value: str) -> str:\n    if value == 'bad':\n        raise ValueError('bad')\n    return value + '!'\n",
        ),
    ] {
        fs::write(directory.path().join(path), source).unwrap();
    }
    let files = vec![
        SourceFile {
            path: "consumer.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["prepare".to_owned()],
        },
        SourceFile {
            path: "selector.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["select".to_owned()],
        },
        SourceFile {
            path: "reserver.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["reserve".to_owned()],
        },
        SourceFile {
            path: "enhancer.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["enhance".to_owned()],
        },
    ];
    let bindings = [
        ("select", "selector.py", "select"),
        ("reserve", "reserver.py", "reserve"),
        ("enhance", "enhancer.py", "enhance"),
    ]
    .into_iter()
    .map(|(field, path, symbol)| PythonCallableBinding {
        id: format!("prepare-{field}"),
        consumer_path: "consumer.py".to_owned(),
        operation_symbol: "prepare".to_owned(),
        input_record: "Request".to_owned(),
        field: field.to_owned(),
        provider: PythonCallableProvider::Source {
            path: path.to_owned(),
            symbol: symbol.to_owned(),
        },
    })
    .collect();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files,
        external_contract_overlays: Vec::new(),
        cross_language_bindings: Vec::new(),
        python_callable_bindings: bindings,
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(response.python_callable_bindings.len(), 3);
    assert!(response.files.iter().all(|file| {
        matches!(file.result, ProofStatus::Proved)
            && file.fragment.as_deref() == Some("dagcert-closed-typed-operations/v3")
    }));
}

#[test]
fn callable_values_cannot_be_aliased_escaped_mutated_or_invoked_as_floating_effects() {
    let bodies = [
        "    alias = request.enhance\n    return Completed(request.value)\n",
        "    return Completed(request.enhance)\n",
        "    request.enhance = request.enhance\n    return Completed(request.value)\n",
        "    request.enhance(request.value)\n    return Completed(request.value)\n",
    ];
    for body in bodies {
        let directory = tempfile::tempdir().unwrap();
        let consumer = CONSUMER.replace(
            "    try:\n        return Completed(request.enhance(request.value))\n    except ValueError:\n        return Rejected(request.value)\n",
            body,
        );
        fs::write(directory.path().join("consumer.py"), consumer).unwrap();
        fs::write(
            directory.path().join("provider.py"),
            "def enhance(value: str) -> str:\n    return value\n",
        )
        .unwrap();
        let request = ProofRequest {
            schema: PROTOCOL_SCHEMA.to_owned(),
            source_root: directory.path().display().to_string(),
            source_fingerprint: "0".repeat(64),
            proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
            files: vec![
                SourceFile {
                    path: "consumer.py".to_owned(),
                    language: "python".to_owned(),
                    symbols: vec!["prepare".to_owned()],
                },
                SourceFile {
                    path: "provider.py".to_owned(),
                    language: "python".to_owned(),
                    symbols: vec!["enhance".to_owned()],
                },
            ],
            external_contract_overlays: Vec::new(),
            cross_language_bindings: Vec::new(),
            python_callable_bindings: vec![PythonCallableBinding {
                id: "closed-enhancer".to_owned(),
                consumer_path: "consumer.py".to_owned(),
                operation_symbol: "prepare".to_owned(),
                input_record: "Request".to_owned(),
                field: "enhance".to_owned(),
                provider: PythonCallableProvider::Source {
                    path: "provider.py".to_owned(),
                    symbol: "enhance".to_owned(),
                },
            }],
        };

        let response = maledictus::analyze_python_frontend(&request);
        assert!(
            matches!(
                response.disposition,
                maledictus::FrontendDisposition::Unsupported
            ),
            "callback escape unexpectedly verified:\n{body}\n{response:#?}"
        );
    }
}

#[test]
fn external_callbacks_require_a_real_overlay_and_refuse_unproved_preconditions() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("consumer.py"), CONSUMER).unwrap();
    let binding = PythonCallableBinding {
        id: "external-enhancer".to_owned(),
        consumer_path: "consumer.py".to_owned(),
        operation_symbol: "prepare".to_owned(),
        input_record: "Request".to_owned(),
        field: "enhance".to_owned(),
        provider: PythonCallableProvider::ExternalContract {
            module: "provider".to_owned(),
            symbol: "enhance".to_owned(),
        },
    };
    let without_overlay = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "consumer.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["prepare".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        cross_language_bindings: Vec::new(),
        python_callable_bindings: vec![binding.clone()],
    };
    let missing = maledictus::analyze_python_frontend(&without_overlay);
    assert!(missing.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "python-callable-binding.external-contract-missing"
    }));

    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef enhance(value: str) -> str:\n    Requires(value != '')\n    ...\n",
    )
    .unwrap();
    let with_precondition = ProofRequest {
        external_contract_overlays: vec![ExternalOverlay {
            adapter_path: "consumer.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: ExternalExceptionPolicy::AssumeNoException,
        }],
        python_callable_bindings: vec![binding],
        ..without_overlay
    };
    let precondition = maledictus::analyze_python_frontend(&with_precondition);
    assert!(precondition.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "python-callable-binding.external-precondition-unsupported"
    }));
}
