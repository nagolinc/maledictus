use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofStatus,
    SourceFile,
};
use std::fs;

const CONTRACT: &str = "from nagini_contracts.contracts import ContractOnly, Ensures, Result\n\n@ContractOnly\ndef read(value: int) -> int:\n    Ensures(Result() == value + 1)\n    ...\n";

#[test]
fn repeated_provider_overlays_do_not_reuse_stubgen_output_directories() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("one_contract.py"), CONTRACT).unwrap();
    fs::write(directory.path().join("two_contract.py"), CONTRACT).unwrap();
    fs::write(directory.path().join("app.py"),
        "from native_one import read\n\ndef run() -> int:\n    value = read(4)\n    assert value == 5\n    return value\n").unwrap();
    let helper = "from native_one import read\nfrom native_two import read as other\n\ndef helper() -> int:\n    first = read(2)\n    second = other(first)\n    assert second == 4\n    return second\n";
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: [("app.py", "run"), ("helper.py", "helper")]
            .into_iter()
            .map(|(path, symbol)| SourceFile {
                path: path.to_owned(),
                language: "python".to_owned(),
                symbols: vec![symbol.to_owned()],
            })
            .collect(),
        external_contract_overlays: [
            ("app.py", "native_one", "one_contract.py"),
            ("helper.py", "native_one", "one_contract.py"),
            ("helper.py", "native_two", "two_contract.py"),
        ]
        .into_iter()
        .map(|(adapter_path, module, stub_path)| ExternalOverlay {
            adapter_path: adapter_path.to_owned(),
            module: module.to_owned(),
            stub_path: stub_path.to_owned(),
            exception_policy: ExternalExceptionPolicy::AssumeNoException,
        })
        .collect(),
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    };
    fs::write(directory.path().join("helper.py"), helper).unwrap();
    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(response.external_contracts.len(), 3);
    fs::write(
        directory.path().join("helper.py"),
        helper.replace("other(first)", "other('wrong')"),
    )
    .unwrap();
    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|d| d.code == "frontend.python.typecheck.arg-type"
                && d.path.as_deref() == Some("helper.py")),
        "{response:#?}"
    );
}

fn request(root: &std::path::Path, modules: &[&str]) -> ProofRequest {
    fs::write(root.join("contract.py"), CONTRACT).unwrap();
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: root.display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        external_contract_overlays: modules
            .iter()
            .map(|module| ExternalOverlay {
                adapter_path: "app.py".to_owned(),
                module: (*module).to_owned(),
                stub_path: "contract.py".to_owned(),
                exception_policy: ExternalExceptionPolicy::AssumeNoException,
            })
            .collect(),
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    }
}

#[test]
fn nested_native_namespaces_preserve_types_and_contract_failures() {
    for module in ["nativepkg.client", "nativepkg.transport.client"] {
        let dir = tempfile::tempdir().unwrap();
        let request = request(dir.path(), &[module]);
        for (expected, status) in [(5, ProofStatus::Proved), (9, ProofStatus::Refuted)] {
            fs::write(dir.path().join("app.py"), format!(
                "from {module} import read\n\ndef run() -> int:\n    value = read(4)\n    assert value == {expected}\n    return value\n"
            )).unwrap();
            let response = maledictus::verify(&request);
            assert!(
                matches!(
                    (&response.status, &status),
                    (ProofStatus::Proved, ProofStatus::Proved)
                        | (ProofStatus::Refuted, ProofStatus::Refuted)
                ),
                "{response:#?}"
            );
        }
    }
}

#[test]
fn explicit_parent_api_is_preserved_beside_child_overlay() {
    let dir = tempfile::tempdir().unwrap();
    let request = request(dir.path(), &["nativepkg", "nativepkg.client"]);
    fs::write(dir.path().join("app.py"),
        "from nativepkg import read as parent_read\nfrom nativepkg.client import read\n\ndef run() -> int:\n    first = parent_read(4)\n    second = read(5)\n    assert first == 5\n    assert second == 6\n    return second\n"
    ).unwrap();
    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
}

#[test]
fn native_submodule_cannot_hide_owned_parent_initialization() {
    for path in [
        "nativepkg.py",
        "nativepkg/__init__.py",
        "nativepkg/transport/__init__.py",
    ] {
        let dir = tempfile::tempdir().unwrap();
        let request = request(dir.path(), &["nativepkg.transport.client"]);
        let shadow = dir.path().join(path);
        fs::create_dir_all(shadow.parent().unwrap()).unwrap();
        fs::write(shadow, "raise RuntimeError('owned initialization')\n").unwrap();
        fs::write(dir.path().join("app.py"),
            "from nativepkg.transport.client import read\n\ndef run() -> int:\n    return read(4)\n"
        ).unwrap();
        let response = maledictus::verify(&request);
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{response:#?}"
        );
        assert!(
            response
                .diagnostics
                .iter()
                .any(|d| d.code == "frontend.python.typecheck.overlay-source-conflict"),
            "{response:#?}"
        );
    }
}

#[test]
fn namespace_does_not_admit_unsupplied_siblings() {
    let dir = tempfile::tempdir().unwrap();
    let request = request(dir.path(), &["nativepkg.client"]);
    fs::write(dir.path().join("app.py"),
        "from nativepkg.client import read\nfrom nativepkg.other import mystery\n\ndef run() -> int:\n    return read(mystery())\n"
    ).unwrap();
    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
}

#[test]
fn a_stdlib_parent_keeps_its_full_pinned_interface() {
    let dir = tempfile::tempdir().unwrap();
    let request = request(dir.path(), &["collections.native_extension"]);
    fs::write(dir.path().join("app.py"),
        "from collections import deque\nfrom collections.native_extension import read\n\ndef run() -> int:\n    values: deque[int] = deque()\n    values.append(read(4))\n    return values[0]\n"
    ).unwrap();
    let result = maledictus::python_typecheck::typecheck_request_sources(
        dir.path(),
        &request.files,
        &request.external_contract_overlays,
    )
    .unwrap()
    .unwrap();
    assert!(result.passed(), "{result:#?}");
}
