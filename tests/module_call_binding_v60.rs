use std::fs;

use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};
use maledictus::{FrontendAnalysis, FrontendDisposition, analyze_python_frontend};

fn verify_source_modules(app: &str, provider: &str) -> maledictus::protocol::ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("app.py"), app).unwrap();
    fs::write(directory.path().join("provider.py"), provider).unwrap();
    maledictus::verify(&ProofRequest {
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
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["encode".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

fn analyze_source_modules(app: &str, provider: &str) -> FrontendAnalysis {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("app.py"), app).unwrap();
    fs::write(directory.path().join("provider.py"), provider).unwrap();
    analyze_python_frontend(&ProofRequest {
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
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["encode".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

const PROVIDER: &str = r#"from nagini_contracts.contracts import *

def encode(first: int, second: int = 7, *, offset: int = 11) -> int:
    Ensures(Result() == first * 100 + second * 10 + offset)
    return first * 100 + second * 10 + offset
"#;

#[test]
fn module_initializer_provider_calls_use_canonical_named_default_and_star_binding() {
    let response = verify_source_modules(
        r#"from nagini_contracts.contracts import *
from provider import encode

NAMED = encode(second=3, first=1, offset=4)
DEFAULTED = encode(2)
STARRED = encode(*(2, 3), offset=4)

assert NAMED == 134
Assert(DEFAULTED == 281)
Assert(STARRED == 234)

def run() -> None:
    pass
"#,
        PROVIDER,
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(
                |obligation| obligation.id.starts_with("module:assert:") && obligation.satisfied()
            )
            .count(),
        3,
        "{response:#?}"
    );
}

#[test]
fn module_initializer_provider_calls_fail_closed_for_dynamic_expansions() {
    for (initializer, diagnostic) in [
        (
            "COUNT = 1\nVALUE = encode(*COUNT)",
            "frontend.python.heap.call-star-dynamic-unsupported",
        ),
        (
            "COUNT = 1\nVALUE = encode(**COUNT)",
            "frontend.python.heap.call-keyword-star-dynamic-unsupported",
        ),
    ] {
        let analysis = analyze_source_modules(
            &format!(
                "from provider import encode\n\n{initializer}\n\ndef run() -> None:\n    pass\n"
            ),
            PROVIDER,
        );
        assert!(
            matches!(analysis.disposition, FrontendDisposition::Unsupported),
            "{analysis:#?}"
        );
        assert_eq!(analysis.diagnostics[0].code, diagnostic, "{analysis:#?}");
        assert!(analysis.files[0].fragment.is_none(), "{analysis:#?}");
        assert!(
            !analysis
                .obligations
                .iter()
                .any(|obligation| obligation.id.starts_with("run:")),
            "{analysis:#?}"
        );
    }
}
