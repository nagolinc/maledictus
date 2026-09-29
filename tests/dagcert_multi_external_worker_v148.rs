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
            diagnostic.code == "external-contract.provider-module-conflict"
                || diagnostic.code == "frontend.python.typecheck.overlay-conflict"
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
        ["queue_provider.Full"],
        "{response:#?}"
    );
}

#[test]
fn scalar_external_exsures_is_caught_inside_one_source_worker() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from os_provider import makedirs\n\ndef ensure_directory(path: str) -> bool:\n    try:\n        makedirs(path, exist_ok=True)\n        return True\n    except Exception:\n        return False\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("os_contract.py"),
        "from nagini_contracts.contracts import ContractOnly, Exsures\n\n@ContractOnly\ndef makedirs(name: str, mode: int = 511, exist_ok: bool = False) -> None:\n    Exsures(Exception, True)\n    ...\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![source("app.py", &["ensure_directory"])],
        vec![overlay(
            "app.py",
            "os_provider",
            "os_contract.py",
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
        ["Exception"],
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

#[test]
fn qualified_module_generic_and_exception_are_proved_without_rewriting_the_app_import() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import Acc, Ensures, Requires\nimport queue_provider as queue\n\nclass Job:\n    value: int\n\n    def __init__(self, value: int) -> None:\n        Ensures(Acc(self.value))\n        self.value = value\n\ndef enqueue(destination: queue.Queue[Job], job: Job) -> bool:\n    Requires(Acc(destination.state))\n    try:\n        queue.Queue.put_nowait(destination, job)\n        return True\n    except queue.Full:\n        return False\n",
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
}

#[test]
fn operation_record_reexport_keeps_the_leaf_nominal_origin() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("records.py"),
        "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Request:\n    value: int\n\n@dataclass(frozen=True)\nclass Response:\n    value: int\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("domain.py"),
        "from dagcert.runtime import operation\nfrom records import Request, Response\n\n@operation\ndef step(request: Request) -> Response:\n    return Response(request.value + 1)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("worker.py"),
        "from dagcert.runtime import operation\nfrom domain import step\nfrom records import Request, Response\n\n@operation\ndef run(request: Request) -> Response:\n    return Response(request.value)\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![
            source("records.py", &[]),
            source("domain.py", &["step"]),
            source("worker.py", &["run"]),
        ],
        Vec::new(),
    ));

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn hidden_sibling_record_layout_does_not_require_constructor_visibility() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("leaf_types.py"),
        "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Used:\n    value: str\n    keys: tuple[str, ...]\n\n@dataclass(frozen=True)\nclass Unused:\n    value: str\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("middle_types.py"),
        "from dataclasses import dataclass\nfrom leaf_types import Used\n\n@dataclass(frozen=True)\nclass Wrapped:\n    item: Used\n    keys: tuple[str, ...]\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("adapter.py"),
        "import os\nfrom dagcert.runtime import external_boundary\nfrom leaf_types import Used\nfrom middle_types import Wrapped\n\n@external_boundary('environment.visibility-probe')\ndef read_environment(request: Wrapped) -> Wrapped:\n    try:\n        item = request.item\n        value = os.getenv(item.value, '')\n    except Exception:\n        return Wrapped(Used('', request.item.keys), request.item.keys)\n    return Wrapped(Used(value, item.keys), item.keys)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("os_contract.py"),
        "from nagini_contracts.contracts import ContractOnly, Exsures\n\n@ContractOnly\ndef getenv(key: str, default: str = '') -> str:\n    Exsures(Exception, True)\n    ...\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![
            source("leaf_types.py", &[]),
            source("middle_types.py", &[]),
            source("adapter.py", &["read_environment"]),
        ],
        vec![overlay(
            "adapter.py",
            "os",
            "os_contract.py",
            ExternalExceptionPolicy::DeclaredByExsures,
        )],
    ));

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn operation_imports_an_ordinary_source_helper_without_making_it_a_dag_task() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("records.py"),
        "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Request:\n    value: str\n\n@dataclass(frozen=True)\nclass Outcome:\n    value: str\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("helper.py"),
        "from records import Outcome, Request\n\ndef transform(request: Request) -> Outcome:\n    return Outcome(request.value)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("worker.py"),
        "from dagcert.runtime import operation\nfrom helper import transform\nfrom records import Outcome, Request\n\n@operation\ndef run(request: Request) -> Outcome:\n    return transform(request)\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![
            source("records.py", &[]),
            source("helper.py", &[]),
            source("worker.py", &["run"]),
        ],
        Vec::new(),
    ));

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn operation_assertion_proves_identity_preserved_by_an_ordinary_source_helper() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("records.py"),
        "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Value:\n    text: str\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("helper.py"),
        "from records import Value\n\ndef preserve(value: Value) -> Value:\n    return value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("worker.py"),
        "from dagcert.runtime import operation\nfrom helper import preserve\nfrom records import Value\n\n@operation\ndef run(value: Value) -> Value:\n    returned = preserve(value)\n    assert returned is value\n    return returned\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![
            source("records.py", &[]),
            source("helper.py", &[]),
            source("worker.py", &["run"]),
        ],
        Vec::new(),
    ));

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(
        response
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains(":assert:")),
        "semantic assertion proof was not retained: {response:#?}"
    );
    assert_eq!(
        response
            .files
            .iter()
            .find(|file| file.path == "worker.py")
            .and_then(|file| file.fragment.as_deref()),
        Some("dagcert-closed-typed-operations+semantic-assertions/v1"),
        "operation assertion did not retain the semantic heap proof fragment: {response:#?}"
    );
}

#[test]
fn operation_assertion_rejects_fresh_record_from_an_ordinary_source_helper() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("records.py"),
        "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Value:\n    text: str\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("helper.py"),
        "from records import Value\n\ndef preserve(value: Value) -> Value:\n    return Value(value.text)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("worker.py"),
        "from dagcert.runtime import operation\nfrom helper import preserve\nfrom records import Value\n\n@operation\ndef run(value: Value) -> Value:\n    returned = preserve(value)\n    assert returned is value\n    return returned\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![
            source("records.py", &[]),
            source("helper.py", &[]),
            source("worker.py", &["run"]),
        ],
        Vec::new(),
    ));

    // The current modular reference summary language exports exact identity helpers, but does not
    // yet export arbitrary allocating record helpers.  That conservative limitation is acceptable
    // here only if the helper itself was proved, its source edge was retained, and the consuming
    // worker was refused by semantic verification.  A parser/import failure would not establish
    // this soundness control.
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .files
            .iter()
            .any(|file| { file.path == "helper.py" && matches!(file.result, ProofStatus::Proved) }),
        "{response:#?}"
    );
    assert!(
        response.files.iter().any(|file| {
            file.path == "worker.py" && matches!(file.result, ProofStatus::Refused)
        }),
        "{response:#?}"
    );
    assert!(
        response
            .source_imports
            .iter()
            .any(|edge| edge.importer_path == "worker.py" && edge.provider_path == "helper.py"),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.path.as_deref() == Some("worker.py")),
        "{response:#?}"
    );
}

#[test]
fn operation_frontend_cannot_launder_a_false_assertion_as_a_type_proof() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("records.py"),
        "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Value:\n    text: str\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("worker.py"),
        "from dagcert.runtime import operation\nfrom records import Value\n\n@operation\ndef run(value: Value) -> Value:\n    assert False\n    return value\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![source("records.py", &[]), source("worker.py", &["run"])],
        Vec::new(),
    ));

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|obligation| obligation.id.contains(":assert:") && !obligation.satisfied()),
        "false assertion was not retained as a refuted proof obligation: {response:#?}"
    );
}

#[test]
fn operation_refuses_an_ordinary_source_helper_with_an_uncaught_exception() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("records.py"),
        "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Request:\n    value: str\n\n@dataclass(frozen=True)\nclass Outcome:\n    value: str\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("helper.py"),
        "from records import Outcome, Request\n\ndef transform(request: Request) -> Outcome:\n    raise ValueError(request.value)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("worker.py"),
        "from dagcert.runtime import operation\nfrom helper import transform\nfrom records import Outcome, Request\n\n@operation\ndef run(request: Request) -> Outcome:\n    return transform(request)\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![
            source("records.py", &[]),
            source("helper.py", &[]),
            source("worker.py", &["run"]),
        ],
        Vec::new(),
    ));

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.path.as_deref() == Some("helper.py")
                && diagnostic.code != "frontend.python.dagcert.marker-import-missing"
        }),
        "{response:#?}"
    );
}

#[test]
fn external_native_handle_survives_records_optional_refinement_and_qualified_method_call() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("records.py"),
        "from dataclasses import dataclass\nfrom io_provider import BytesIO\n\n@dataclass(frozen=True)\nclass Request:\n    content: bytes\n\n@dataclass(frozen=True)\nclass NativeBuffer:\n    buffer: BytesIO\n\n@dataclass(frozen=True)\nclass NativeBufferResult:\n    ok: bool\n    buffer: BytesIO | None\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("create_adapter.py"),
        "import io_provider\nfrom dagcert.runtime import external_boundary\nfrom records import NativeBufferResult, Request\n\n@external_boundary('io.create')\ndef create(request: Request) -> NativeBufferResult:\n    try:\n        return NativeBufferResult(True, io_provider.BytesIO(request.content))\n    except Exception:\n        return NativeBufferResult(False, None)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("read_adapter.py"),
        "import io_provider\nfrom dagcert.runtime import external_boundary\nfrom records import NativeBuffer\n\n@external_boundary('io.read')\ndef read(request: NativeBuffer) -> bytes:\n    try:\n        return io_provider.BytesIO.getvalue(request.buffer)\n    except Exception:\n        return b''\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("io_contract.py"),
        "from nagini_contracts.contracts import Acc, ContractOnly, Ensures, Exsures, Requires\n\nclass BytesIO:\n    state: int\n\n    @ContractOnly\n    def __init__(self, content: bytes) -> None:\n        Ensures(Acc(self.state))\n        Exsures(Exception, True)\n        ...\n\n    @ContractOnly\n    def getvalue(self) -> bytes:\n        Requires(Acc(self.state))\n        Ensures(Acc(self.state))\n        Exsures(Exception, Acc(self.state))\n        ...\n",
    )
    .unwrap();

    let response = maledictus::verify(&request(
        directory.path(),
        vec![
            source("records.py", &[]),
            source("create_adapter.py", &["create"]),
            source("read_adapter.py", &["read"]),
        ],
        vec![
            overlay(
                "create_adapter.py",
                "io_provider",
                "io_contract.py",
                ExternalExceptionPolicy::DeclaredByExsures,
            ),
            overlay(
                "read_adapter.py",
                "io_provider",
                "io_contract.py",
                ExternalExceptionPolicy::DeclaredByExsures,
            ),
        ],
    ));

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
}
