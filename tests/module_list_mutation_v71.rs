use std::{fs, path::Path};

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, ProofStatus, SourceFile};
use maledictus::python_contracts::verify_contract_module;
use maledictus::python_typecheck::{MYPY_VERSION, PYTHON_TYPECHECK_PROFILE};

fn issue(source: &str) -> maledictus::protocol::ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("module.py"), source).unwrap();
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "module.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

#[test]
fn exact_pinned_finite_list_augmented_assignment_is_semantically_verified() {
    let suite = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/.upstream/nagini"));
    let pin = Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/conformance/nagini-v1.3.1.json"
    ));
    let result =
        check_pinned_scalar_fixture(suite, pin, "tests/functional/translation/issues/00237.py")
            .unwrap();
    assert!(result.passed, "{result:#?}");
    assert!(result.expected.is_empty());
    assert!(result.actual.is_empty());
}

#[test]
fn production_issuance_proves_exact_finite_list_augmented_assignment() {
    let response = issue("from typing import List\n\na: List[int] = [1]\na[0] += 1\n");
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let typechecker = response
        .python_typechecker
        .as_ref()
        .expect("production issuance must retain the strict checker identity");
    assert_eq!(typechecker.checker, "mypy");
    assert_eq!(typechecker.checker_version, MYPY_VERSION);
    assert_eq!(typechecker.profile, PYTHON_TYPECHECK_PROFILE);
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert_eq!(
        response.solver.as_ref().unwrap().vc_ir,
        "maledictus-scalar-vc/v27"
    );
}

#[test]
fn production_issuance_refuses_typechecked_dynamic_index_and_alias_escape() {
    let cases = [
        (
            "from typing import List\n\nindex: int = 0\nvalues: List[int] = [1]\nvalues[index] += 1\n",
            "frontend.python.contracts.module-list-mutation-index",
        ),
        (
            "from typing import List\n\nvalues: List[int] = [1]\nalias: List[int] = values\nvalues[0] += 1\n",
            "frontend.python.contracts.module-list-mutation-alias",
        ),
    ];
    for (source, _semantic_boundary_code) in cases {
        let response = issue(source);
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{response:#?}"
        );
        assert!(response.python_typechecker.is_some(), "{response:#?}");
        assert!(response.solver.is_none(), "{response:#?}");
        assert!(response.obligations.is_empty(), "{response:#?}");
        assert!(!response.diagnostics.is_empty(), "{response:#?}");
        assert!(
            response
                .files
                .iter()
                .all(|file| matches!(file.result, ProofStatus::Refused)),
            "{response:#?}"
        );
    }
}

#[test]
fn finite_int_list_mutation_supports_exact_primitive_operators() {
    for (operator, path) in [("+=", "add.py"), ("-=", "sub.py"), ("*=", "multiply.py")] {
        let source = format!(
            "from typing import List\n\nvalues: List[int] = [2, 3]\nvalues[1] {operator} 4\n"
        );
        let verification = verify_contract_module(&source, path, &[]).unwrap();
        assert!(verification.passed, "{operator}: {verification:#?}");
    }
}

#[test]
fn finite_list_mutation_rejects_dynamic_negative_and_out_of_range_indices() {
    let cases = [
        (
            "from typing import List\nindex = 0\nvalues: List[int] = [1]\nvalues[index] += 1\n",
            "dynamic.py",
        ),
        (
            "from typing import List\nvalues: List[int] = [1]\nvalues[-1] += 1\n",
            "negative.py",
        ),
        (
            "from typing import List\nvalues: List[int] = [1]\nvalues[1] += 1\n",
            "out_of_range.py",
        ),
    ];
    for (source, path) in cases {
        let error = verify_contract_module(source, path, &[]).unwrap_err();
        assert_eq!(
            error.code, "frontend.python.contracts.module-list-mutation-index",
            "{path}: {error:#?}"
        );
    }
}

#[test]
fn finite_list_mutation_rejects_bool_elements_and_non_int_rhs() {
    let bool_elements = verify_contract_module(
        "from typing import List\nvalues: List[bool] = [True]\nvalues[0] += 1\n",
        "bool_elements.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        bool_elements.code,
        "frontend.python.contracts.module-list-mutation-element-type"
    );

    let bool_rhs = verify_contract_module(
        "from typing import List\nvalues: List[int] = [1]\nvalues[0] += True\n",
        "bool_rhs.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        bool_rhs.code,
        "frontend.python.contracts.module-list-mutation-rhs"
    );
}

#[test]
fn finite_list_mutation_rejects_aliases_callable_escape_and_second_mutation() {
    let alias = verify_contract_module(
        "from typing import List\nvalues: List[int] = [1]\nalias = values\nvalues[0] += 1\n",
        "alias.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        alias.code,
        "frontend.python.contracts.module-list-mutation-alias"
    );

    let callable = verify_contract_module(
        "from typing import List\nvalues: List[int] = [1]\nvalues[0] += 1\n\ndef read() -> int:\n    return 0\n",
        "callable.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        callable.code,
        "frontend.python.contracts.module-list-mutation-escape"
    );

    let repeated = verify_contract_module(
        "from typing import List\nvalues: List[int] = [1]\nvalues[0] += 1\nvalues[0] += 1\n",
        "repeated.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        repeated.code,
        "frontend.python.contracts.module-list-mutation-count"
    );
}

#[test]
fn finite_list_mutation_rejects_custom_dispatch_and_effectful_rhs() {
    let custom = verify_contract_module(
        "class Values:\n    pass\n\nvalues = Values()\nvalues[0] += 1\n",
        "custom.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        custom.code,
        "frontend.python.contracts.module-list-mutation-escape"
    );

    let effectful = verify_contract_module(
        "from typing import List\nvalues: List[int] = [1]\nvalues[0] += int('1')\n",
        "effectful.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        effectful.code,
        "frontend.python.contracts.module-list-mutation-rhs"
    );
}
