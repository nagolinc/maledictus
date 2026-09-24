use std::fs;

use maledictus::protocol::{
    CrossLanguageBinding, CrossLanguageParameter, CrossLanguagePrimitive, PROTOCOL_SCHEMA,
    ProofRequest, ProofStatus, SourceFile,
};

fn request(
    directory: &tempfile::TempDir,
    python: &str,
    provider: &str,
    provider_language: &str,
    provider_symbols: &[&str],
    parameters: Vec<CrossLanguageParameter>,
    return_type: CrossLanguagePrimitive,
) -> ProofRequest {
    fs::write(directory.path().join("caller.py"), python).unwrap();
    let extension = if provider_language == "javascript" {
        "js"
    } else {
        "ts"
    };
    let provider_path = format!("provider.{extension}");
    fs::write(directory.path().join(&provider_path), provider).unwrap();
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "caller.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
            SourceFile {
                path: provider_path.clone(),
                language: provider_language.to_owned(),
                symbols: provider_symbols
                    .iter()
                    .map(|symbol| (*symbol).to_owned())
                    .collect(),
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: vec![CrossLanguageBinding {
            id: "primary_bridge".to_owned(),
            caller_path: "caller.py".to_owned(),
            python_module: "bridge_api".to_owned(),
            python_symbol: "identity".to_owned(),
            provider_path,
            provider_export: "identity".to_owned(),
            parameters,
            return_type,
        }],
    }
}

fn bool_parameter() -> Vec<CrossLanguageParameter> {
    vec![CrossLanguageParameter {
        name: "value".to_owned(),
        type_name: CrossLanguagePrimitive::Bool,
    }]
}

fn assert_public_mixed_proof(provider: &str, language: &str) {
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(
        &directory,
        "from bridge_api import identity\n\ndef run(value: bool) -> bool:\n    return identity(value)\n",
        provider,
        language,
        &["identity"],
        bool_parameter(),
        CrossLanguagePrimitive::Bool,
    ));
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(response.typescript_toolchain.is_some(), "{response:#?}");
    assert!(response.verifier_identity.is_some(), "{response:#?}");
    assert_eq!(response.cross_language_bindings.len(), 1, "{response:#?}");
    let binding = &response.cross_language_bindings[0];
    assert_eq!(binding.provider_language, language);
    assert_eq!(binding.caller_sha256.len(), 64);
    assert_eq!(binding.provider_sha256.len(), 64);
    assert_eq!(binding.interface_sha256.len(), 64);
    assert_eq!(
        response
            .files
            .iter()
            .map(|file| file.fragment.as_deref())
            .collect::<Vec<_>>(),
        vec![
            Some(maledictus::mixed_language::MIXED_LANGUAGE_FRAGMENT),
            Some(maledictus::mixed_language::MIXED_LANGUAGE_FRAGMENT),
        ]
    );
}

#[test]
fn public_issuance_proves_real_python_to_typescript_call_edge() {
    assert_public_mixed_proof(
        "export function identity(value: boolean): boolean { return value; }\n",
        "typescript",
    );
}

#[test]
fn mixed_v1_preserves_its_direct_provider_gate_for_source_class_calls() {
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(
        &directory,
        "from bridge_api import identity\n\ndef run(value: bool) -> bool:\n    return identity(value)\n",
        concat!(
            "class Negator {\n",
            "  readonly enabled: boolean;\n",
            "  constructor(enabled: boolean) { this.enabled = enabled; }\n",
            "  apply(value: boolean): boolean { return this.enabled ? !value : value; }\n",
            "}\n",
            "export function identity(value: boolean): boolean {\n",
            "  const negator = new Negator(false);\n",
            "  return negator.apply(value);\n",
            "}\n",
        ),
        "typescript",
        &["identity"],
        bool_parameter(),
        CrossLanguagePrimitive::Bool,
    ));
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.cross-language.provider-call-unsupported"
    );
}

#[test]
fn public_issuance_proves_real_python_to_checkjs_call_edge() {
    assert_public_mixed_proof(
        "/** @param {boolean} value @returns {boolean} */\nexport function identity(value) { return value; }\n",
        "javascript",
    );
}

#[test]
fn mixed_v1_refuses_async_provider_instead_of_relabeling_promise_as_total_return() {
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(
        &directory,
        "from bridge_api import identity\n\ndef run(value: bool) -> bool:\n    return identity(value)\n",
        "export async function identity(value: boolean): Promise<boolean> { return value; }\n",
        "typescript",
        &["identity"],
        bool_parameter(),
        CrossLanguagePrimitive::Bool,
    ));
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.cross-language.provider-async-unsupported"
    );
}

#[test]
fn public_issuance_supports_string_and_none_primitives() {
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(
        &directory,
        "from bridge_api import identity\n\ndef run(value: str) -> str:\n    return identity(value)\n",
        "export function identity(value: string): string { return value; }\n",
        "typescript",
        &["identity"],
        vec![CrossLanguageParameter {
            name: "value".to_owned(),
            type_name: CrossLanguagePrimitive::Str,
        }],
        CrossLanguagePrimitive::Str,
    ));
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );

    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(
        &directory,
        "from bridge_api import identity\n\ndef run(value: str) -> None:\n    identity(value)\n",
        "export function identity(value: string): void { return; }\n",
        "typescript",
        &["identity"],
        vec![CrossLanguageParameter {
            name: "value".to_owned(),
            type_name: CrossLanguagePrimitive::Str,
        }],
        CrossLanguagePrimitive::None,
    ));
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
}

#[test]
fn mixed_binding_refuses_missing_ambiguous_and_unrequested_exports() {
    let directory = tempfile::tempdir().unwrap();
    let mut missing = request(
        &directory,
        "from bridge_api import identity\ndef run(value: bool) -> bool:\n    return identity(value)\n",
        "export function other(value: boolean): boolean { return value; }\n",
        "typescript",
        &["identity"],
        bool_parameter(),
        CrossLanguagePrimitive::Bool,
    );
    let response = maledictus::verify(&missing);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.cross-language.provider-refused"
    );

    missing.files.push(missing.files[1].clone());
    let response = maledictus::verify(&missing);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.cross-language.request-file"
    );

    let mut unrequested = missing;
    unrequested.files.pop();
    unrequested.files[1].symbols.clear();
    let response = maledictus::verify(&unrequested);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.cross-language.provider-request"
    );

    let directory = tempfile::tempdir().unwrap();
    let extra_export = request(
        &directory,
        "from bridge_api import identity\ndef run(value: bool) -> bool:\n    return identity(value)\n",
        "export function identity(value: boolean): boolean { return value; }\nexport function other(value: boolean): boolean { return value; }\n",
        "typescript",
        &["identity"],
        bool_parameter(),
        CrossLanguagePrimitive::Bool,
    );
    let response = maledictus::verify(&extra_export);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.cross-language.provider-export-set"
    );
}

#[test]
fn mixed_binding_refuses_signature_and_argument_mismatch() {
    let directory = tempfile::tempdir().unwrap();
    let mismatch = request(
        &directory,
        "from bridge_api import identity\ndef run(value: bool) -> bool:\n    return identity(value)\n",
        "export function identity(value: string): string { return value; }\n",
        "typescript",
        &["identity"],
        bool_parameter(),
        CrossLanguagePrimitive::Bool,
    );
    let response = maledictus::verify(&mismatch);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.cross-language.signature-mismatch"
    );

    let directory = tempfile::tempdir().unwrap();
    let bad_argument = request(
        &directory,
        "from bridge_api import identity\ndef run(value: str) -> bool:\n    return identity(value)\n",
        "export function identity(value: boolean): boolean { return value; }\n",
        "typescript",
        &["identity"],
        bool_parameter(),
        CrossLanguagePrimitive::Bool,
    );
    let response = maledictus::verify(&bad_argument);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(
        response.diagnostics[0]
            .code
            .starts_with("frontend.python.typecheck."),
        "{response:#?}"
    );
}

#[test]
fn mixed_binding_refuses_cycles_exceptions_and_mutating_bodies() {
    let cases = [
        "export function identity(value: boolean): boolean { return identity(value); }\n",
        "export function identity(value: boolean): boolean { throw \"bad\"; }\n",
        "export function identity(value: boolean): boolean { value = !value; return value; }\n",
        "export function identity(value: boolean): boolean { Math.random(); return value; }\n",
    ];
    for provider in cases {
        let directory = tempfile::tempdir().unwrap();
        let response = maledictus::verify(&request(
            &directory,
            "from bridge_api import identity\ndef run(value: bool) -> bool:\n    return identity(value)\n",
            provider,
            "typescript",
            &["identity"],
            bool_parameter(),
            CrossLanguagePrimitive::Bool,
        ));
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{response:#?}"
        );
        assert!(
            response.diagnostics[0]
                .code
                .starts_with("frontend.cross-language."),
            "{response:#?}"
        );
    }
}

#[test]
fn mixed_binding_refuses_missing_call_and_binding_escape() {
    for caller in [
        "from bridge_api import identity\ndef run(value: bool) -> bool:\n    return value\n",
        "from bridge_api import identity\nalias = identity\ndef run(value: bool) -> bool:\n    return identity(value)\n",
        "from bridge_api import identity\ndef run(identity: bool) -> bool:\n    return identity(True)\n",
    ] {
        let directory = tempfile::tempdir().unwrap();
        let response = maledictus::verify(&request(
            &directory,
            caller,
            "export function identity(value: boolean): boolean { return value; }\n",
            "typescript",
            &["identity"],
            bool_parameter(),
            CrossLanguagePrimitive::Bool,
        ));
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{response:#?}"
        );
        assert!(
            matches!(
                response.diagnostics[0].code.as_str(),
                "frontend.python.cross-language.call-missing"
                    | "frontend.python.cross-language.binding-escape"
                    | "frontend.python.cross-language.binding-shadowed"
            ),
            "{response:#?}"
        );
    }
}

#[test]
fn mixed_binding_refuses_javascript_number_as_python_int() {
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(
        &directory,
        "from bridge_api import identity\ndef run(value: bool) -> bool:\n    return identity(value)\n",
        "export function identity(value: number): number { return value; }\n",
        "typescript",
        &["identity"],
        bool_parameter(),
        CrossLanguagePrimitive::Bool,
    ));
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.cross-language.number-unsupported"
    );
}
