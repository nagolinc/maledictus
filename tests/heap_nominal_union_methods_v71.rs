use std::fs;
use std::path::PathBuf;

use maledictus::conformance::{check_heap_source, check_pinned_heap_fixture};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};

#[test]
fn exact_nominal_union_method_fixtures_match() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for fixture in [
        "tests/functional/translation/issues/00117.py",
        "tests/functional/translation/issues/00124.py",
    ] {
        let result = check_pinned_heap_fixture(
            &repository.join(".upstream/nagini"),
            &repository.join("conformance/nagini-v1.3.1.json"),
            fixture,
        )
        .unwrap_or_else(|error| panic!("exact upstream fixture {fixture} was refused: {error}"));
        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(result.expected, result.actual, "{fixture}: {result:#?}");
    }
}

#[test]
fn every_union_arm_uses_the_shared_call_binder() {
    let error = check_heap_source(
        "from typing import Union\nclass Left:\n    def emit(self) -> int:\n        return 1\nclass Right:\n    def emit(self, value: int) -> int:\n        return value\ndef run(item: Union[Left, Right]) -> int:\n    return item.emit()\n",
        "union_binding.py",
    )
    .unwrap_err();
    assert!(
        error.contains("frontend.python.heap.call-argument-missing"),
        "{error}"
    );
}

#[test]
fn missing_dynamic_or_effectful_union_arms_fail_closed() {
    for source in [
        "from typing import Union\nclass Left:\n    def ready(self) -> int:\n        return 1\nclass Right:\n    pass\ndef run(item: Union[Left, Right]) -> int:\n    return item.ready()\n",
        "from typing import Union\nclass Left:\n    def ready(self) -> int:\n        return 1\nclass Right:\n    def ready(self) -> int:\n        return 2\n    def __getattribute__(self, name: str) -> object:\n        return object()\ndef run(item: Union[Left, Right]) -> int:\n    return item.ready()\n",
        "from typing import Union\nfrom nagini_contracts.contracts import Exsures\nclass Left:\n    def ready(self) -> int:\n        return 1\nclass Right:\n    def ready(self) -> int:\n        Exsures(Exception, True)\n        return 2\ndef run(item: Union[Left, Right]) -> int:\n    return item.ready()\n",
    ] {
        let result = check_heap_source(source, "unsafe_union_dispatch.py");
        assert!(result.is_err(), "{source}\n{result:#?}");
    }
}

#[test]
fn heterogeneous_union_results_are_only_validated_at_a_matching_return_boundary() {
    let accepted = check_heap_source(
        "from typing import Union\nclass Text:\n    def value(self) -> str:\n        return 'ready'\nclass Count:\n    def value(self) -> int:\n        return 1\ndef run(item: Union[Text, Count]) -> Union[int, str]:\n    return item.value()\n",
        "union_return.py",
    )
    .unwrap();
    assert!(accepted.passed, "{accepted:#?}");

    let rejected = check_heap_source(
        "from typing import Union\nclass Text:\n    def value(self) -> str:\n        return 'ready'\nclass Count:\n    def value(self) -> int:\n        return 1\ndef run(item: Union[Text, Count]) -> object:\n    value = item.value()\n    return value\n",
        "escaped_union_result.py",
    );
    assert!(rejected.is_err(), "{rejected:#?}");
}

#[test]
fn public_issuance_advertises_the_union_dispatch_fragment() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from typing import Union\nclass Left:\n    def value(self) -> int:\n        return 1\nclass Right:\n    def value(self) -> int:\n        return 2\ndef run(item: Union[Left, Right]) -> int:\n    return item.value()\n",
    )
    .unwrap();

    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
}

#[test]
fn transitive_source_issuance_preserves_union_dispatch() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "class Left:\n    def value(self) -> int:\n        return 1\nclass Right:\n    def value(self) -> int:\n        return 2\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from typing import Union\nfrom provider import Left, Right\ndef run(item: Union[Left, Right]) -> int:\n    return item.value()\n",
    )
    .unwrap();

    let response = maledictus::verify(&ProofRequest {
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
                symbols: Vec::new(),
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
}
