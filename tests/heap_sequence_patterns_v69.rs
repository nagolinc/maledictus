use std::fs;
use std::path::PathBuf;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_heap_fixture};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn request(directory: &tempfile::TempDir, source: &str) -> ProofRequest {
    fs::write(directory.path().join("sequence_match.py"), source).unwrap();
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "sequence_match.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    }
}

#[test]
fn fixed_and_starred_primitive_list_patterns_execute_real_match_paths() {
    let verification = verify(
        "from typing import List\n\ndef fixed(values: List[int]) -> int:\n    match values:\n        case [left, right]:\n            return left + right\n        case _:\n            return 0\n\ndef starred(values: List[int]) -> int:\n    match values:\n        case [head, *tail]:\n            return head\n        case _:\n            return 0\n\ndef suffix(values: List[int]) -> int:\n    match values:\n        case [first, *middle, last]:\n            return first + last\n        case _:\n            return 0\n",
        "sequence_match.py",
    );
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn starred_tail_is_a_sound_overapproximation_not_an_invented_slice_fact() {
    let verification = verify(
        "from typing import List\n\ndef inspect(values: List[int]) -> None:\n    match values:\n        case [head, *tail]:\n            assert len(tail) == len(values) - 1\n        case _:\n            pass\n",
        "unconstrained_star_tail.py",
    );
    assert!(!verification.passed, "{verification:#?}");
    assert!(
        verification
            .obligations
            .iter()
            .any(|obligation| !obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn nonlist_nonprimitive_and_nested_sequence_patterns_fail_closed() {
    for (source, expected_code) in [
        (
            "from typing import Tuple\ndef run(value: Tuple[int, int]) -> int:\n    match value:\n        case [left, right]:\n            return left\n        case _:\n            return 0\n",
            "frontend.python.heap.match-sequence-subject-unsupported",
        ),
        (
            "from typing import List\nclass Cell:\n    pass\ndef run(value: List[Cell]) -> int:\n    match value:\n        case [first]:\n            return 1\n        case _:\n            return 0\n",
            "frontend.python.heap.match-sequence-element-unsupported",
        ),
        (
            "from typing import List\ndef run(value: List[int]) -> int:\n    match value:\n        case [[inner]]:\n            return inner\n        case _:\n            return 0\n",
            "frontend.python.heap.match-sequence-nested-unsupported",
        ),
    ] {
        let failure = verify_heap_module(source, "unsupported_sequence.py", &[]).unwrap_err();
        assert_eq!(failure.code, expected_code, "{failure:#?}");
    }
}

#[test]
fn pinned_upstream_unsupported_expectations_are_preserved_as_superseded_not_exact() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_match_sequence.py",
        "tests/functional/translation/test_match_sequence_star.py",
    ] {
        let result = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("{fixture}: {error}"));
        assert!(!result.passed, "must not relabel as exact: {result:#?}");
        assert!(result.semantic_verified, "{result:#?}");
        assert_eq!(
            result.analysis_kind,
            ConformanceMatchKind::SupersededUpstreamUnsupported,
            "{result:#?}"
        );
        assert!(!result.expected.is_empty(), "{result:#?}");
        assert!(result.actual.is_empty(), "{result:#?}");
        assert!(result.python_typechecker.is_some(), "{result:#?}");
    }
}

#[test]
fn true_public_issuance_runs_strict_typecheck_and_proves_sequence_matching() {
    let directory = tempfile::tempdir().unwrap();
    let response = maledictus::verify(&request(
        &directory,
        "from typing import List\n\ndef run(values: List[int]) -> int:\n    match values:\n        case [head, *tail]:\n            return head\n        case _:\n            return 0\n",
    ));
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(response.verifier_identity.is_some(), "{response:#?}");
}
