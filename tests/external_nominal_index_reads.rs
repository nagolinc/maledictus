use std::fs;

use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, SourceFile,
};

fn verify(source: &str, module: &str, contract: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("worker.py"), source).unwrap();
    fs::write(directory.path().join("contract.py"), contract).unwrap();
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "worker.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["work".to_owned()],
        }],
        external_contract_overlays: vec![ExternalOverlay {
            adapter_path: "worker.py".to_owned(),
            module: module.to_owned(),
            stub_path: "contract.py".to_owned(),
            exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
        }],
        python_callable_bindings: Vec::new(),
        embedded_external_calls: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

const RECORDS: &str = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\nfrom nagini_contracts.contracts import Ensures, Old, ResultT\n\n@dataclass(frozen=True)\nclass Request:\n    index: int\n    path: str\n\n@dataclass(frozen=True)\nclass Selected:\n    value: int\n\n@dataclass(frozen=True)\nclass Failed:\n    code: int\n";

const STORE_CONTRACT: &str = "from nagini_contracts.contracts import ContractOnly, Ensures, Exsures, Result\n\nclass IndexStore:\n    @ContractOnly\n    def __init__(self) -> None:\n        ...\n\n    @ContractOnly\n    def __getitem__(self, index: int) -> int:\n        Ensures(Result() == index + 1)\n        Exsures(Exception, True)\n        ...\n";

const PATH_CONTRACT: &str = "from nagini_contracts.contracts import ContractOnly, Exsures\n\nclass _PathParents:\n    @ContractOnly\n    def __getitem__(self, index: int) -> 'Path':\n        Exsures(Exception, True)\n        ...\n\nclass Path:\n    @ContractOnly\n    def __init__(self, value: str) -> None:\n        Exsures(Exception, True)\n        ...\n\n    @ContractOnly\n    def resolve(self) -> 'Path':\n        Exsures(Exception, True)\n        ...\n\n    @property\n    @ContractOnly\n    def parents(self) -> _PathParents:\n        Exsures(Exception, True)\n        ...\n";

fn assert_proved(response: &ProofResponse) {
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().all(|item| item.satisfied()),
        "{response:#?}"
    );
    assert!(
        response.files[0]
            .fragment
            .as_deref()
            .is_some_and(|fragment| fragment.starts_with("dagcert-closed-typed-operations")),
        "{response:#?}"
    );
}

fn store_source(delta: i32, expression: &str) -> String {
    format!(
        "from index_provider import IndexStore\n{RECORDS}\n@operation\ndef work(request: Request) -> Selected | Failed:\n    Ensures(not isinstance(ResultT(Selected), Selected) or ResultT(Selected).value == Old(request.index) + {delta})\n    try:\n        store = IndexStore()\n        value = {expression}\n        return Selected(value)\n    except Exception:\n        return Failed(0)\n"
    )
}

#[test]
fn external_index_result_contract_proves_and_false_relation_is_refuted() {
    assert_proved(&verify(
        &store_source(1, "store[request.index]"),
        "index_provider",
        STORE_CONTRACT,
    ));
    let response = verify(
        &store_source(2, "store[request.index]"),
        "index_provider",
        STORE_CONTRACT,
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|item| item.id.contains(":postcondition:") && !item.satisfied()),
        "{response:#?}"
    );
}

#[test]
fn uncaught_index_exception_is_a_semantic_failure() {
    let source = format!(
        "from index_provider import IndexStore\n{RECORDS}\n@operation\ndef work(request: Request) -> Selected:\n    store = IndexStore()\n    value = store[request.index]\n    return Selected(value)\n"
    );
    let response = verify(&source, "index_provider", STORE_CONTRACT);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|item| item.id.contains("exception-undeclared") && !item.satisfied()),
        "{response:#?}"
    );
}

#[test]
fn actual_pathlib_parent_sequence_supports_inline_receiver_chain() {
    for (import, body) in [
        (
            "from pathlib import Path",
            "        selected = Path(request.path).parents[1]",
        ),
        (
            "from pathlib import Path",
            "        selected = Path(request.path).resolve().parents[1]",
        ),
    ] {
        let source = format!(
            "{import}\n{RECORDS}\n@operation\ndef work(request: Request) -> Selected | Failed:\n    try:\n{body}\n        return Selected(request.index)\n    except Exception:\n        return Failed(0)\n"
        );
        assert_proved(&verify(&source, "pathlib", PATH_CONTRACT));
    }
}

#[test]
fn canonical_native_import_requirement_remains_explicit() {
    let source = format!(
        "from pathlib import Path as NativePath\n{RECORDS}\n@operation\ndef work(request: Request) -> Selected | Failed:\n    try:\n        path = NativePath(request.path)\n        selected = path.parents[request.index]\n        return Selected(request.index)\n    except Exception:\n        return Failed(0)\n"
    );
    let response = verify(&source, "pathlib", PATH_CONTRACT);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|item| item.code == "frontend.python.heap.import-alias-unsupported"),
        "{response:#?}"
    );
}

#[test]
fn native_base_contract_cannot_hide_a_source_subclass_override() {
    let contract = STORE_CONTRACT.replace("        Exsures(Exception, True)\n", "");
    let provider = maledictus::python_heap_contracts::parse_external_heap_contract_module(
        &contract,
        "contract.py",
        "index_provider",
    )
    .unwrap();
    for hierarchy in [
        "class Evil(IndexStore):\n    def __getitem__(self, index: int) -> int:\n        return -1\n",
        "class Intermediate(IndexStore):\n    pass\n\nclass Evil(Intermediate):\n    def __getitem__(self, index: int) -> int:\n        return -1\n",
    ] {
        let source = format!(
            "from index_provider import IndexStore\n\n{hierarchy}\ndef work(store: IndexStore) -> IndexStore:\n    value = store[0]\n    assert value == 1\n    return store\n"
        );
        let full = maledictus::python_heap_contracts::verify_heap_module_with_imports(
            &source,
            "worker.py",
            &["work".to_owned()],
            std::slice::from_ref(&provider),
        );
        assert!(
            !full.as_ref().is_ok_and(|result| result.passed),
            "full: {full:#?}"
        );
        let selected = maledictus::python_heap_contracts::verify_heap_module_selection_with_imports_for_conformance(
            &source, "worker.py", std::slice::from_ref(&provider), &["work".to_owned()].into_iter().collect(),
        );
        let failure = selected.unwrap_err();
        assert_eq!(
            failure.code, "frontend.python.heap.external-index-dispatch-unsupported",
            "{failure:#?}"
        );
        let joint_source = format!(
            "from index_provider import IndexStore\n{RECORDS}\n{hierarchy}\n@operation\ndef work(store: IndexStore) -> Selected:\n    return Selected(store[0])\n"
        );
        let joint = verify(&joint_source, "index_provider", &contract);
        assert!(
            !matches!(joint.status, ProofStatus::Proved),
            "joint: {joint:#?}"
        );
    }
}

#[test]
fn exact_native_construction_does_not_dispatch_to_an_unrelated_source_override() {
    let contract = STORE_CONTRACT.replace("        Exsures(Exception, True)\n", "");
    let source = "from index_provider import IndexStore\n\nclass Evil(IndexStore):\n    def __getitem__(self, index: int) -> int:\n        return -1\n\ndef work(store: IndexStore) -> IndexStore:\n    native = IndexStore()\n    value = native[0]\n    assert value == 1\n    return store\n";
    let provider = maledictus::python_heap_contracts::parse_external_heap_contract_module(
        &contract,
        "contract.py",
        "index_provider",
    )
    .unwrap();
    let result = maledictus::python_heap_contracts::verify_heap_module_selection_with_imports_for_conformance(
        source, "worker.py", &[provider], &["work".to_owned()].into_iter().collect(),
    ).unwrap();
    assert!(result.passed, "{result:#?}");
}

#[test]
fn native_base_indexing_does_not_borrow_a_contract_through_special_method_shadows() {
    let contract = STORE_CONTRACT.replace("        Exsures(Exception, True)\n", "");
    let provider = maledictus::python_heap_contracts::parse_external_heap_contract_module(
        &contract,
        "contract.py",
        "index_provider",
    )
    .unwrap();
    for (kind, body) in [
        (
            "property",
            "    @property\n    def __getitem__(self) -> int:\n        return -1\n",
        ),
        ("constant", "    __getitem__ = 3\n"),
        ("field", "    __getitem__: int\n"),
        (
            "staticmethod",
            "    @staticmethod\n    def __getitem__(index: int) -> int:\n        return -1\n",
        ),
        (
            "classmethod",
            "    @classmethod\n    def __getitem__(cls, index: int) -> int:\n        return -1\n",
        ),
    ] {
        let source = format!(
            "from index_provider import IndexStore\n\nclass Shadow(IndexStore):\n{body}\ndef work(store: IndexStore) -> IndexStore:\n    value = store[0]\n    assert value == 1\n    return store\n"
        );
        let result = maledictus::python_heap_contracts::verify_heap_module_selection_with_imports_for_conformance(
            &source, "worker.py", std::slice::from_ref(&provider), &["work".to_owned()].into_iter().collect(),
        );
        let failure = result.unwrap_err();
        eprintln!("{kind}: {}: {}", failure.code, failure.message);
    }
}

#[test]
fn wrong_index_type_and_slices_are_not_reinterpreted_as_integer_lookup() {
    for expression in ["store['bad']", "store[1:3]"] {
        let response = verify(
            &store_source(1, expression),
            "index_provider",
            STORE_CONTRACT,
        );
        assert!(
            !matches!(response.status, ProofStatus::Proved),
            "{expression}: {response:#?}"
        );
        assert!(
            response
                .diagnostics
                .iter()
                .any(|item| item.code.starts_with("frontend.python.typecheck.")
                    || item.code == "frontend.python.heap.external-index-shape-unsupported"),
            "{expression}: {response:#?}"
        );
    }
}

#[test]
fn nominal_indexing_does_not_enable_store_or_delete() {
    for statement in ["store[request.index] = 3", "del store[request.index]"] {
        let source = store_source(1, "store[request.index]").replace(
            "        value = store[request.index]",
            &format!("        {statement}\n        value = store[request.index]"),
        );
        let response = verify(&source, "index_provider", STORE_CONTRACT);
        assert!(
            !matches!(response.status, ProofStatus::Proved),
            "{statement}: {response:#?}"
        );
    }
}

#[test]
fn source_owned_magic_method_cannot_borrow_the_external_registry_entry() {
    let source = format!(
        "from index_provider import IndexStore\n{RECORDS}\n@dataclass(frozen=True)\nclass IndexStore:\n    value: int\n\n    def __getitem__(self, index: int) -> int:\n        raise ValueError('source-owned failure')\n\n@operation\ndef work(request: Request) -> Selected:\n    store = IndexStore(request.index)\n    return Selected(store[request.index])\n"
    );
    let response = verify(&source, "index_provider", STORE_CONTRACT);
    assert!(
        !matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|item| item.code == "frontend.python.typecheck.no-redef"),
        "{response:#?}"
    );
}

#[test]
fn unshadowed_source_owned_indexing_does_not_become_an_external_call() {
    let source = "from index_provider import IndexStore\n\nclass SourceStore:\n    def __getitem__(self, index: int) -> int:\n        return -1\n\ndef work(store: SourceStore) -> SourceStore:\n    value = store[0]\n    assert value == 1\n    return store\n";
    let provider = maledictus::python_heap_contracts::parse_external_heap_contract_module(
        STORE_CONTRACT,
        "contract.py",
        "index_provider",
    )
    .unwrap();
    let failure = maledictus::python_heap_contracts::verify_heap_module_with_imports(
        source,
        "worker.py",
        &["work".to_owned()],
        &[provider],
    )
    .unwrap_err();
    assert_eq!(
        failure.code, "frontend.python.heap.subscript-type-unsupported",
        "{failure:#?}"
    );
}

#[test]
fn receiver_and_index_effects_execute_once_in_order_and_stop_on_each_exception() {
    let contract = r#"from nagini_contracts.contracts import Acc, ContractOnly, Ensures, Exsures, Old, Requires, Result

class ReceiverFailure(Exception):
    pass

class IndexFailure(Exception):
    pass

class Machine:
    state: int

    @ContractOnly
    def __init__(self) -> None:
        Ensures(Acc(self.state) and self.state == 0)
        ...

    @ContractOnly
    def receiver(self) -> 'Machine':
        Requires(Acc(self.state) and self.state == 0)
        Ensures(Acc(self.state) and self.state == 1)
        Ensures(Result() is self)
        Exsures(ReceiverFailure, Acc(self.state) and self.state == 1)
        ...

    @ContractOnly
    def index(self) -> int:
        Requires(Acc(self.state) and self.state == 1)
        Ensures(Acc(self.state) and self.state == 2 and Result() == 4)
        Exsures(IndexFailure, Acc(self.state) and self.state == 2)
        ...

    @ContractOnly
    def __getitem__(self, index: int) -> int:
        Requires(Acc(self.state) and self.state == 2)
        Ensures(Acc(self.state) and self.state == 3 and Result() == index + 1)
        ...
"#;
    let source = format!(
        "from index_provider import Machine, ReceiverFailure, IndexFailure\n{RECORDS}\n@operation\ndef work(request: Request) -> Selected | Failed:\n    machine = Machine()\n    try:\n        value = machine.receiver()[machine.index()]\n        assert machine.state == 3\n        assert value == 5\n        return Selected(value)\n    except ReceiverFailure:\n        assert machine.state == 1\n        return Failed(1)\n    except IndexFailure:\n        assert machine.state == 2\n        return Failed(2)\n"
    );
    assert_proved(&verify(&source, "index_provider", contract));
    let response = verify(
        &source.replace("assert machine.state == 2", "assert machine.state == 3"),
        "index_provider",
        contract,
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|item| !item.satisfied()),
        "{response:#?}"
    );
}

#[test]
fn builtin_indexed_values_keep_their_existing_semantics() {
    for (annotation, value, expected) in [
        ("tuple[int, int]", "(4, 8)", 8),
        ("list[int]", "[4, 8]", 8),
        ("bytes", "b'AB'", 66),
        ("dict[int, int]", "{0: 4, 1: 8}", 8),
    ] {
        let source = format!(
            "from nagini_contracts.contracts import Ensures, Result\n\ndef work() -> int:\n    Ensures(Result() == {expected})\n    values: {annotation} = {value}\n    return values[1]\n"
        );
        let result = maledictus::python_heap_contracts::verify_heap_module(
            &source,
            "builtins.py",
            &["work".to_owned()],
        )
        .unwrap_or_else(|error| panic!("{annotation}: {error:#?}"));
        assert!(result.passed, "{annotation}: {result:#?}");
    }
}
