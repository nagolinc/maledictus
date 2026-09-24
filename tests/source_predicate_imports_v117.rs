use std::fs;

use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofResponse, ProofStatus, SourceFile};

fn verify_sources(files: &[(&str, &str, &[&str])]) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    for (path, source, _) in files {
        let destination = directory.path().join(path);
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(destination, source).unwrap();
    }
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: files
            .iter()
            .map(|(path, _, symbols)| SourceFile {
                path: (*path).to_owned(),
                language: "python".to_owned(),
                symbols: symbols.iter().map(|symbol| (*symbol).to_owned()).collect(),
            })
            .collect(),
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

const PROVIDER: &str = r#"from nagini_contracts.contracts import *

class Cell:
    value: int

    def __init__(self) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == 1)
        self.value = 1

@Predicate
def state(cell: Cell) -> bool:
    return Acc(cell.value) and cell.value == 1
"#;

const CONSUMER: &str = r#"from nagini_contracts.contracts import *
from provider import Cell, state

def run() -> None:
    cell = Cell()
    Fold(state(cell))
    Unfold(state(cell))
    Assert(cell.value == 1)
"#;

#[test]
fn public_verifier_accepts_an_exact_predicate_export_from_verified_source() {
    let response = verify_sources(&[
        ("provider.py", PROVIDER, &["Cell.__init__", "state"]),
        ("app.py", CONSUMER, &["run"]),
    ]);

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("run:predicate-fold-body:state:") && obligation.satisfied()
    }));
}

#[test]
fn public_verifier_preserves_predicate_identity_through_a_named_source_reexport() {
    let bridge = "from provider import Cell as Cell, state as state\n";
    let consumer = CONSUMER.replace("from provider import", "from bridge import");
    let response = verify_sources(&[
        ("provider.py", PROVIDER, &["Cell.__init__", "state"]),
        ("bridge.py", bridge, &[]),
        ("app.py", &consumer, &["run"]),
    ]);

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "app.py"
            && edge.provider_path == "bridge.py"
            && edge.imported_symbols.iter().any(|symbol| symbol == "state")
    }));
}

#[test]
fn public_verifier_does_not_relabel_an_ordinary_source_export_as_a_predicate() {
    let ordinary_provider = PROVIDER.replace(
        "@Predicate\ndef state(cell: Cell) -> bool:\n    return Acc(cell.value) and cell.value == 1",
        "def state(cell: Cell) -> bool:\n    return True",
    );
    let response = verify_sources(&[
        (
            "provider.py",
            &ordinary_provider,
            &["Cell.__init__", "state"],
        ),
        ("app.py", CONSUMER, &["run"]),
    ]);

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    let diagnostic = response
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.path.as_deref() == Some("app.py"))
        .unwrap_or_else(|| panic!("consumer refusal must identify its source file: {response:#?}"));
    assert_eq!(diagnostic.code, "invalid.program:invalid.contract.call");
    assert_eq!(diagnostic.line, Some(6));
}

#[test]
fn public_verifier_does_not_trust_a_predicate_import_that_is_rebound() {
    let consumer = r#"from nagini_contracts.contracts import *
from provider import Cell, state

def ordinary(cell: Cell) -> bool:
    return True

state = ordinary

def run() -> None:
    cell = Cell()
    Fold(state(cell))
"#;
    let response = verify_sources(&[
        ("provider.py", PROVIDER, &["Cell.__init__", "state"]),
        ("app.py", consumer, &["run"]),
    ]);

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "invalid.program:invalid.contract.call"
            && diagnostic.path.as_deref() == Some("app.py")
            && diagnostic.line == Some(11)
    }));
}
