use std::fs;

use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofStatus,
    SourceFile,
};

fn source(path: &str, symbols: &[&str]) -> SourceFile {
    SourceFile {
        path: path.to_owned(),
        language: "python".to_owned(),
        symbols: symbols.iter().map(|symbol| (*symbol).to_owned()).collect(),
    }
}

fn overlay(
    adapter_path: &str,
    module: &str,
    stub_path: &str,
    exception_policy: ExternalExceptionPolicy,
) -> ExternalOverlay {
    ExternalOverlay {
        adapter_path: adapter_path.to_owned(),
        module: module.to_owned(),
        stub_path: stub_path.to_owned(),
        exception_policy,
    }
}

fn request(
    root: &std::path::Path,
    files: Vec<SourceFile>,
    external_contract_overlays: Vec<ExternalOverlay>,
) -> ProofRequest {
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: root.display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files,
        external_contract_overlays,
        python_callable_bindings: Vec::new(),
        embedded_external_calls: Vec::new(),
        cross_language_bindings: Vec::new(),
    }
}

#[test]
fn one_worker_composes_multiple_external_adapter_overlays() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("first_adapter.py"),
        "from first_provider import increment\n\ndef first(value: int) -> int:\n    return increment(value)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("second_adapter.py"),
        "from second_provider import double\n\ndef second(value: int) -> int:\n    return double(value)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("worker.py"),
        "from first_adapter import first\nfrom second_adapter import second\n\ndef run(value: int) -> int:\n    return second(first(value))\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("first_contract.py"),
        "from nagini_contracts.contracts import ContractOnly\n\n@ContractOnly\ndef increment(value: int) -> int:\n    ...\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("second_contract.py"),
        "from nagini_contracts.contracts import ContractOnly\n\n@ContractOnly\ndef double(value: int) -> int:\n    ...\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![
            source("first_adapter.py", &["first"]),
            source("second_adapter.py", &["second"]),
            source("worker.py", &["run"]),
        ],
        vec![
            overlay(
                "first_adapter.py",
                "first_provider",
                "first_contract.py",
                ExternalExceptionPolicy::AssumeNoException,
            ),
            overlay(
                "second_adapter.py",
                "second_provider",
                "second_contract.py",
                ExternalExceptionPolicy::AssumeNoException,
            ),
        ],
    ));

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(response.external_contracts.len(), 2, "{response:#?}");
}

#[test]
fn conflicting_reachable_adapter_overlays_remain_fail_closed() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("first_adapter.py"),
        "from shared_provider import read_value\n\ndef first() -> int:\n    return read_value()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("second_adapter.py"),
        "from shared_provider import read_value\n\ndef second() -> int:\n    return read_value()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("worker.py"),
        "from first_adapter import first\nfrom second_adapter import second\n\ndef run() -> int:\n    return first() + second()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("first_contract.py"),
        "from nagini_contracts.contracts import ContractOnly\n\n@ContractOnly\ndef read_value() -> int:\n    ...\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("second_contract.py"),
        "from nagini_contracts.contracts import ContractOnly, Ensures, Result\n\n@ContractOnly\ndef read_value() -> int:\n    Ensures(Result() >= 0)\n    ...\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![
            source("first_adapter.py", &["first"]),
            source("second_adapter.py", &["second"]),
            source("worker.py", &["run"]),
        ],
        vec![
            overlay(
                "first_adapter.py",
                "shared_provider",
                "first_contract.py",
                ExternalExceptionPolicy::AssumeNoException,
            ),
            overlay(
                "second_adapter.py",
                "shared_provider",
                "second_contract.py",
                ExternalExceptionPolicy::AssumeNoException,
            ),
        ],
    ));

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.typecheck.overlay-conflict"
                || diagnostic.code == "frontend.python.heap.external-overlay-context-conflict"
        }),
        "{response:#?}"
    );
}

#[test]
fn generic_heap_exsures_is_caught_without_erasing_the_payload_type() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import Acc, Ensures, Requires\nfrom queue_provider import Full, Queue\n\nclass Job:\n    value: int\n\n    def __init__(self, value: int) -> None:\n        Ensures(Acc(self.value))\n        self.value = value\n\ndef enqueue(destination: Queue[Job], job: Job) -> bool:\n    Requires(Acc(destination.state))\n    try:\n        destination.put_nowait(job)\n        return True\n    except Full:\n        return False\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("queue_contract.py"),
        "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import Acc, ContractOnly, Ensures, Exsures, Requires\n\nT = TypeVar('T')\n\nclass Full(Exception):\n    pass\n\nclass Queue(Generic[T]):\n    state: int\n\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.state))\n        ...\n\n    @ContractOnly\n    def put_nowait(self, item: T) -> None:\n        Requires(Acc(self.state))\n        Ensures(Acc(self.state))\n        Exsures(Full, Acc(self.state))\n        ...\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![source("app.py", &["Job.__init__", "enqueue"])],
        vec![overlay(
            "app.py",
            "queue_provider",
            "queue_contract.py",
            ExternalExceptionPolicy::DeclaredByExsures,
        )],
    ));

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.external_contracts[0].declared_exceptions,
        ["Full"],
        "{response:#?}"
    );
}

#[test]
fn complete_worker_composes_records_state_multiple_providers_and_queue_full() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("records.py"),
        "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Request:\n    prompt: str\n\n@dataclass(frozen=True)\nclass Job:\n    prompt: str\n\n@dataclass(frozen=True)\nclass Response:\n    status: str\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("queue_state.py"),
        "from queue_provider import Queue\nfrom records import Job\n\nprepared: Queue[Job] | None = None\n\ndef configure(value: Queue[Job]) -> None:\n    global prepared\n    prepared = value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("environment_adapter.py"),
        "from dagcert.runtime import external_boundary\nfrom environment_provider import read_value\n\n@external_boundary('environment.model.read')\ndef model_name() -> str:\n    return read_value('MODEL')\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("prompt_adapter.py"),
        "from dagcert.runtime import external_boundary\nfrom prompt_provider import enhance\n\n@external_boundary('provider.prompt.prepare')\ndef prepare(prompt: str, model: str) -> str:\n    return enhance(prompt, model)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("queue_adapter.py"),
        "from dagcert.runtime import external_boundary\nfrom queue_provider import Full\nimport queue_state\nfrom records import Job\n\n@external_boundary('stdlib.queue.prepared-put')\ndef publish(job: Job) -> str:\n    destination = queue_state.prepared\n    if destination is None:\n        return 'unconfigured'\n    try:\n        destination.put_nowait(job)\n        return 'enqueued'\n    except Full:\n        return 'full'\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("worker.py"),
        "from dagcert.runtime import ExternalSuccess, operation\nfrom environment_adapter import model_name\nfrom prompt_adapter import prepare\nfrom queue_adapter import publish\nfrom records import Job, Request, Response\n\n@operation\ndef run(request: Request) -> Response:\n    model = model_name()\n    if not isinstance(model, ExternalSuccess):\n        return Response('environment-failed')\n    enhanced = prepare(request.prompt, model.value)\n    if not isinstance(enhanced, ExternalSuccess):\n        return Response('provider-failed')\n    published = publish(Job(enhanced.value))\n    if not isinstance(published, ExternalSuccess):\n        return Response('queue-failed')\n    return Response(published.value)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("environment_contract.py"),
        "from nagini_contracts.contracts import ContractOnly\n\n@ContractOnly\ndef read_value(name: str) -> str:\n    ...\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("prompt_contract.py"),
        "from nagini_contracts.contracts import ContractOnly\n\n@ContractOnly\ndef enhance(prompt: str, model: str) -> str:\n    ...\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("queue_contract.py"),
        "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import ContractOnly, Exsures\n\nT = TypeVar('T')\n\nclass Full(Exception):\n    pass\n\nclass Queue(Generic[T]):\n    @ContractOnly\n    def put_nowait(self, item: T) -> None:\n        Exsures(Full, True)\n        ...\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![
            source("records.py", &[]),
            source("queue_state.py", &[]),
            source("environment_adapter.py", &["model_name"]),
            source("prompt_adapter.py", &["prepare"]),
            source("queue_adapter.py", &["publish"]),
            source("worker.py", &["run"]),
        ],
        vec![
            overlay(
                "environment_adapter.py",
                "environment_provider",
                "environment_contract.py",
                ExternalExceptionPolicy::AssumeNoException,
            ),
            overlay(
                "prompt_adapter.py",
                "prompt_provider",
                "prompt_contract.py",
                ExternalExceptionPolicy::AssumeNoException,
            ),
            overlay(
                "queue_adapter.py",
                "queue_provider",
                "queue_contract.py",
                ExternalExceptionPolicy::DeclaredByExsures,
            ),
        ],
    ));

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(response.external_contracts.len(), 3, "{response:#?}");
    assert!(
        response
            .source_imports
            .iter()
            .any(|edge| { edge.importer_path == "queue_state.py" && edge.module == "records" })
    );
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "worker.py"
            && edge.module == "queue_adapter"
            && edge.imported_symbols == ["publish"]
    }));
}
