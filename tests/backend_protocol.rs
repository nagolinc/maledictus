use std::fs;

use maledictus::protocol::{
    FileResult, PROTOCOL_SCHEMA, ProofRequest, ProofResponse, ProofStatus, SourceFile,
};
use maledictus::{FrontendDisposition, analyze_python_frontend};

fn analyze_frontend_request(request: &ProofRequest) -> ProofResponse {
    let analysis = analyze_python_frontend(request);
    let mut response = ProofResponse::refused(request);
    response.status = match analysis.disposition {
        FrontendDisposition::Supported => ProofStatus::Proved,
        FrontendDisposition::Refuted => ProofStatus::Refuted,
        FrontendDisposition::Unsupported => ProofStatus::Refused,
    };
    response.files = analysis
        .files
        .into_iter()
        .map(|file| FileResult {
            path: file.path,
            sha256: file.sha256,
            symbols: file.symbols,
            scope: file.scope,
            result: match file.disposition {
                FrontendDisposition::Supported => ProofStatus::Proved,
                FrontendDisposition::Refuted => ProofStatus::Refuted,
                FrontendDisposition::Unsupported => ProofStatus::Refused,
            },
            fragment: file.fragment,
            verified_interfaces: Vec::new(),
        })
        .collect();
    response.source_imports = analysis.source_imports;
    response.external_contracts = analysis.external_contracts;
    response.python_callable_bindings = analysis.python_callable_bindings;
    response.obligations = analysis.obligations;
    response.solver = analysis.solver;
    response.diagnostics = analysis.diagnostics;
    response
}

fn verify_predicate_program(source: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("predicate.py"), source).unwrap();
    analyze_frontend_request(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "predicate.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

#[test]
fn heap_conformance_matches_exact_upstream_operators_fixture() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/verification/test_operators.py";
    let result = maledictus::conformance::check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.fixture, fixture);
    assert_eq!(result.expected, result.actual, "{result:#?}");
    assert_eq!(result.actual.len(), 5, "{result:#?}");
}

#[test]
fn verifier_proves_upstream_pure_identity_argument_and_nested_calls2_prefix() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    def __init__(self) -> None:\n        Ensures(Acc(self.c2) and isinstance(self.c2, Class2))\n        Ensures(Acc(self.c2.c1) and self.c2.c1 is self)\n        self.c2 = Class2(self)\n    @Pure\n    def get_c2(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        return self.c2\n\nclass Class2:\n    def __init__(self, c1: Class1) -> None:\n        Ensures(Acc(self.c1) and self.c1 is c1)\n        self.c1 = c1\n    @Pure\n    def get_c1(self) -> Class1:\n        Requires(Acc(self.c1))\n        return self.c1\n    def get_c1_impure(self) -> Class1:\n        Requires(Acc(self.c1))\n        Ensures(Acc(self.c1))\n        Ensures(self.c1 is Old(self.c1))\n        Ensures(Result() is self.c1)\n        return self.c1\n    def set_c1(self, c1: Class1) -> None:\n        Requires(Acc(self.c1))\n        Ensures(Acc(self.c1))\n        Ensures(self.c1 is c1)\n        self.c1 = c1\n\n@Pure\ndef id(c1: Class1) -> Class1:\n    return c1\n\ndef nested_calls2() -> None:\n    c1_1 = Class1()\n    c1_2 = Class1()\n    c1_2.get_c2().set_c1(c1_1.c2.get_c1_impure())\n    c1_1.get_c2().get_c1().c2.set_c1(id(c1_2))\n    Assert(c1_2.c2.c1 == c1_1)\n    Assert(c1_1.c2.c1.c2.c1 == c1_1)\n",
        &[
            "Class1.__init__",
            "Class1.get_c2",
            "Class2.__init__",
            "Class2.get_c1",
            "Class2.get_c1_impure",
            "Class2.set_c1",
            "id",
            "nested_calls2",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "id:reference-identity-function-complete" && obligation.satisfied()
    }));
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| {
                obligation.id.starts_with("nested_calls2:assert:") && obligation.satisfied()
            })
            .count(),
        2,
        "{response:#?}"
    );
}

#[test]
fn verifier_proves_a_selected_pure_nominal_identity_function() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import Pure\n\nclass Item:\n    pass\n\n@Pure\ndef id(value: Item) -> Item:\n    return value\n",
        &["id"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "id:reference-identity-function-complete" && obligation.satisfied()
    }));
}

#[test]
fn verifier_preserves_actual_subtype_and_unrelated_heap_state_through_identity_argument() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Derived(Base):\n    pass\n\nclass Stable:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    value: Base\n    stable: Stable\n    def __init__(self, value: Base, stable: Stable) -> None:\n        Ensures(Acc(self.value))\n        Ensures(Acc(self.stable))\n        Ensures(self.value is value)\n        Ensures(self.stable is stable)\n        self.value = value\n        self.stable = stable\n    def set_value(self, value: Base) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(self.value is value)\n        self.value = value\n\n@Pure\ndef id(value: Base) -> Base:\n    return value\n\ndef run() -> None:\n    derived = Derived()\n    stable = Stable()\n    holder = Holder(derived, stable)\n    holder.set_value(id(derived))\n    Assert(holder.value == derived)\n    Assert(holder.stable == stable)\n",
        &[
            "Base.__init__",
            "Stable.__init__",
            "Holder.__init__",
            "Holder.set_value",
            "id",
            "run",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| obligation.id.starts_with("run:assert:") && obligation.satisfied())
            .count(),
        2,
        "{response:#?}"
    );
}

fn verify_heap_program(source: &str, symbols: &[&str]) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("heap_program.py"), source).unwrap();
    analyze_frontend_request(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "heap_program.py".to_owned(),
            language: "python".to_owned(),
            symbols: symbols.iter().map(|symbol| (*symbol).to_owned()).collect(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

fn assert_heap_refusal_without_exported_proof(response: &ProofResponse, diagnostic_code: &str) {
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == diagnostic_code),
        "{response:#?}"
    );
    assert!(
        response.files.iter().all(|file| file.fragment.is_none()),
        "{response:#?}"
    );
    assert!(
        !response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        }),
        "{response:#?}"
    );
}

fn assert_heap_refusal_without_any_proof(response: &ProofResponse, diagnostic_code: &str) {
    assert_heap_refusal_without_exported_proof(response, diagnostic_code);
    assert!(response.obligations.is_empty(), "{response:#?}");
}

#[test]
fn verifier_proves_a_source_ordered_builtin_type_object_alias() {
    let response = verify_heap_program("TextIO = int\n", &[]);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(response.files[0].fragment.is_some(), "{response:#?}");
}

#[test]
fn verifier_proves_real_source_in_closed_total_fragment() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "def run() -> int:\n    return 1\n",
    )
    .unwrap();
    let request = ProofRequest {
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
    };

    let response = maledictus::verify(&request);

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(response.files.len(), 1);
    assert_eq!(
        response.files[0].sha256,
        "daded4711c501d4162062f0c3116c999ce11a09bfb95a474bb55161003bc46ed"
    );
    assert!(response.diagnostics.is_empty());
    assert!(matches!(response.files[0].result, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("closed-total-functions+safe-builtin-slices/v1")
    );
    assert!(response.solver.is_none());
}

#[test]
fn verifier_refuses_an_unresolved_call() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "def run(value: str) -> str:\n    return value.strip()\n",
    )
    .unwrap();
    let request = ProofRequest {
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
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.python.fragment.expression-unsupported"
    );
}

#[test]
fn verifier_proves_exhaustively_caught_callable_dataclass_boundary() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from dataclasses import dataclass\nfrom typing import Callable\n\n@dataclass\nclass Runner:\n    callback: Callable[[str], bool]\n\n    def run(self, value: str) -> bool:\n        try:\n            return self.callback(value)\n        except:\n            return False\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["Runner.run".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("caught-callable-dataclass-boundaries/v1")
    );
    assert_eq!(response.files[0].scope, "all-source-symbol-bodies");
    assert!(response.solver.is_none());
}

#[test]
fn verifier_refuses_non_exhaustive_callable_exception_handler() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from dataclasses import dataclass\nfrom typing import Callable\n\n@dataclass\nclass Runner:\n    callback: Callable[[str], bool]\n\n    def run(self, value: str) -> bool:\n        try:\n            return self.callback(value)\n        except Exception:\n            return False\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["Runner.run".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.python.callable-boundary.handler-not-exhaustive"
    );
}

#[test]
fn verifier_proves_scalar_nagini_contracts_with_smt() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\n\ndef successor(value: int) -> int:\n    Requires(value > 0)\n    Ensures(Result() > value)\n    next_value = value + 1\n    assert next_value > 0\n    return next_value\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["successor".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(response.obligations.len(), 2);
    assert!(response.diagnostics.is_empty());
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    let solver = response
        .solver
        .as_ref()
        .expect("SMT proof must name its solver");
    assert_eq!(solver.solver, "z3");
    assert!(!solver.solver_version.is_empty());
    assert_eq!(solver.rust_binding, "z3-rs/0.21.0");
    assert_eq!(solver.vc_ir, "maledictus-scalar-vc/v27");
}

#[test]
fn verifier_proves_finite_iteration_and_membership_through_json_backend() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "def total() -> int:\n    result = 0\n    for value in range(1, 4):\n        result += value\n    assert 2 in range(1, 4)\n    assert 5 not in range(1, 4)\n    return result\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["total".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert!(response.solver.is_some());
}

#[test]
fn verifier_proves_static_slices_through_json_backend() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\n\ndef slices() -> None:\n    values = [1, 2, 3, 4]\n    assert values[::-1] == [4, 3, 2, 1]\n    data = b'1234'\n    assert data[1:3] == b'23'\n    numbers = range(1, 5)\n    assert numbers[1:] == range(2, 5)\n    assert ToSeq(numbers[:2]) == ToSeq(range(1, 3))\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["slices".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert_eq!(response.solver.unwrap().vc_ir, "maledictus-scalar-vc/v27");
}

#[test]
fn verifier_proves_symbolic_bytes_operations_through_json_backend() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\n\ndef combine(left: bytes, right: bytes) -> bytes:\n    Ensures(Result() == left + right)\n    Ensures(len(Result()) == len(left) + len(right))\n    return left + right\n\ndef joined(left: bytes, right: bytes) -> bytes:\n    values = [left, right]\n    return b'-'.join(values)\n\ndef first(value: bytes) -> int:\n    Requires(len(value) > 0)\n    return value[0]\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec![
                "combine".to_owned(),
                "joined".to_owned(),
                "first".to_owned(),
            ],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert_eq!(response.solver.unwrap().vc_ir, "maledictus-scalar-vc/v27");
}

#[test]
fn verifier_proves_integer_builtins_through_json_backend() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\n\ndef builtin_math(value: int, other: int) -> int:\n    Ensures(Result() >= 0)\n    magnitude = abs(value)\n    assert value ** 2 == value * value\n    assert min(value, other) <= value\n    assert max(value, other) >= other\n    return magnitude\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["builtin_math".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert_eq!(response.solver.unwrap().vc_ir, "maledictus-scalar-vc/v27");
}

#[test]
fn verifier_proves_typed_lambda_postcondition_and_guarded_tuple_index() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef choose(values: Tuple[int, int, int], index: int) -> int:\n    Requires(0 <= index and index < 3)\n    Requires(values[0] >= 0 and values[1] >= 0 and values[2] >= 0)\n    Ensures(int, lambda returned: returned >= 5)\n    return values[index] + 5\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["choose".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert_eq!(response.solver.unwrap().vc_ir, "maledictus-scalar-vc/v27");
}

#[test]
fn verifier_reports_uncaught_sequence_index_error_as_application_precondition() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "def broken() -> None:\n    values = b'12'\n    item = values[2]\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["broken".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.diagnostics[0].code,
        "application.precondition:assertion.false"
    );
}

#[test]
fn verifier_reports_zero_step_range_as_a_typed_application_precondition() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "def broken() -> None:\n    values = range(0, 3, 0)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["broken".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.diagnostics[0].code,
        "application.precondition:assertion.false"
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains(":exception-undeclared:ValueError:application-precondition:")
    }));

    fs::write(
        directory.path().join("app.py"),
        "def broken() -> None:\n    raise ValueError()\n",
    )
    .unwrap();
    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.diagnostics[0].code,
        "exhale.failed:assertion.false"
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains(":exception-undeclared:ValueError:")
            && !obligation.id.contains(":application-precondition:")
    }));
}

#[test]
fn verifier_selects_scalar_fragment_semantically_without_contract_text() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import Pure\n\n@Pure\ndef identity(value: int) -> int:\n    return value\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["identity".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert!(response.solver.is_some());
}

#[test]
fn verifier_serializes_refute_polarity_and_reports_a_provable_refutation() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\n\ndef check(value: int) -> None:\n    Requires(value > 0)\n    Refute(value > 0)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["check".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.obligations[0].expectation,
        maledictus::vc::ObligationExpectation::Refute
    );
    assert_eq!(
        response.diagnostics[0].code,
        "refute.failed:refutation.true"
    );
}

#[test]
fn verifier_distinguishes_refutation_from_unsupported_source() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\n\ndef positive(value: int) -> int:\n    assert value > 0\n    return value\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["positive".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert!(matches!(response.files[0].result, ProofStatus::Refuted));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert!(response.solver.is_some());
    assert_eq!(
        response.diagnostics[0].code,
        "assert.failed:assertion.false"
    );
    assert!(response.obligations[0].counterexample.is_some());
}

#[test]
fn verifier_rejects_path_escape() {
    let directory = tempfile::tempdir().unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "../outside.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.python.typecheck.source-path"
    );
}

#[test]
fn empty_request_is_not_a_vacuous_proof() {
    let directory = tempfile::tempdir().unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: Vec::new(),
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(response.diagnostics[0].code, "source.files.empty");
}

#[test]
fn checked_external_contract_proves_adapter_and_records_assumption() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import positive\nfrom nagini_contracts.contracts import *\n\ndef run() -> int:\n    Ensures(Result() == 2)\n    value = positive(1)\n    return value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef positive(value: int) -> int:\n    Requires(value > 0)\n    Ensures(int, lambda returned: returned == value + 1)\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty());
    assert_eq!(response.external_contracts.len(), 1);
    assert_eq!(response.external_contracts[0].module, "provider");
    assert_eq!(response.external_contracts[0].functions, ["positive"]);
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("checked-external-scalar-contracts/v26")
    );
    let identity = response.verifier_identity.as_ref().unwrap();
    assert_eq!(identity.executable_sha256.len(), 64);
    assert_eq!(identity.frontend_bundle_sha256.len(), 64);
    assert_eq!(identity.kernel_bundle_sha256.len(), 64);
}

#[test]
fn checked_external_contract_preserves_fixed_tuple_element_types() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import flip\nfrom typing import Tuple\n\ndef run() -> Tuple[str, int]:\n    return flip((1, 'value'))\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\n@ContractOnly\ndef flip(value: Tuple[int, str]) -> Tuple[str, int]:\n    Ensures(Result()[0] == value[1])\n    Ensures(Result()[1] == value[0])\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert!(response.diagnostics.is_empty());
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("checked-external-scalar-contracts/v26")
    );
}

#[test]
fn checked_external_contract_preserves_variadic_tuple_types_and_length() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import preserve\nfrom nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef run(values: Tuple[int, ...]) -> Tuple[int, ...]:\n    Ensures(len(Result()) == len(values))\n    return preserve(values)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\n@ContractOnly\ndef preserve(values: Tuple[int, ...]) -> Tuple[int, ...]:\n    Ensures(len(Result()) == len(values))\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty());
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("checked-external-scalar-contracts/v26")
    );
}

#[test]
fn checked_external_contract_preserves_homogeneous_list_types_and_length() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import first_two\nfrom nagini_contracts.contracts import *\nfrom typing import List\n\ndef run() -> List[int]:\n    Ensures(len(Result()) == 2)\n    return first_two()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\nfrom typing import List\n\n@ContractOnly\ndef first_two() -> List[int]:\n    Ensures(len(Result()) == 2)\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert!(response.diagnostics.is_empty());
    assert_eq!(response.solver.unwrap().vc_ir, "maledictus-scalar-vc/v27");
}

#[test]
fn checked_external_contract_refutes_violated_call_precondition() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import positive\n\ndef run() -> int:\n    return positive(0)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef positive(value: int) -> int:\n    Requires(value > 0)\n    Ensures(Result() > 0)\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.diagnostics[0].code,
        "call.precondition:assertion.false"
    );
    assert_eq!(response.external_contracts.len(), 1);
}

#[test]
fn checked_external_contract_refuses_an_unused_or_mismatched_overlay() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "def run() -> int:\n    return 1\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef positive(value: int) -> int:\n    Ensures(Result() > 0)\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.python.contract-import.module-unused"
    );
}

#[test]
fn checked_external_contract_propagates_declared_exsures_outcomes() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import maybe_value\nfrom nagini_contracts.contracts import *\n\ndef run(flag: bool) -> int:\n    Ensures(Result() == 1)\n    Exsures(ValueError, flag)\n    return maybe_value(flag)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef maybe_value(flag: bool) -> int:\n    Ensures(Result() == 1)\n    Exsures(ValueError, flag)\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::DeclaredByExsures,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.external_contracts[0].declared_exceptions,
        ["ValueError"]
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|item| { item.id.contains("run:exception-postcondition:") && item.satisfied() })
    );
}

#[test]
fn external_exsures_requires_explicit_declared_outcome_policy() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import maybe_value\n\ndef run(flag: bool) -> int:\n    return maybe_value(flag)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef maybe_value(flag: bool) -> int:\n    Exsures(ValueError, flag)\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "external-contract.exception-policy-mismatch"
    );
}

#[test]
fn adapter_can_exhaustively_handle_external_typed_exception() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import maybe_value\nfrom nagini_contracts.contracts import *\n\ndef run(flag: bool) -> int:\n    Ensures(Implies(flag, Result() == 2))\n    Ensures(Implies(not flag, Result() == 1))\n    try:\n        return maybe_value(flag)\n    except ValueError:\n        return 2\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef maybe_value(flag: bool) -> int:\n    Ensures(not flag and Result() == 1)\n    Exsures(ValueError, flag)\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::DeclaredByExsures,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert!(response.diagnostics.is_empty());
    assert!(
        !response
            .obligations
            .iter()
            .any(|item| item.id.contains("run:exception-"))
    );
}

#[test]
fn adapter_catches_external_custom_subclass_through_checked_base_type() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import maybe_value, ProviderError, SpecificProviderError\nfrom nagini_contracts.contracts import *\n\ndef run(flag: bool) -> int:\n    Ensures(Implies(flag, Result() == 2))\n    Ensures(Implies(not flag, Result() == 1))\n    try:\n        return maybe_value(flag)\n    except ProviderError as error:\n        Assert(isinstance(error, SpecificProviderError))\n        return 2\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass ProviderError(Exception):\n    pass\n\nclass SpecificProviderError(ProviderError):\n    pass\n\n@ContractOnly\ndef maybe_value(flag: bool) -> int:\n    Ensures(not flag and Result() == 1)\n    Exsures(SpecificProviderError, flag)\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::DeclaredByExsures,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.external_contracts[0].exception_types,
        ["provider.ProviderError", "provider.SpecificProviderError"]
    );
    assert_eq!(
        response.external_contracts[0].declared_exceptions,
        ["provider.SpecificProviderError"]
    );
}

#[test]
fn checked_external_nominal_reference_contract_reaches_json_backend() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import Assert\nfrom provider import Widget, make, consume\n\ndef run() -> None:\n    value = make()\n    Assert(value is not None)\n    consume(value)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import ContractOnly\n\nclass Widget:\n    pass\n\n@ContractOnly\ndef make() -> Widget:\n    ...\n\n@ContractOnly\ndef consume(value: Widget) -> None:\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("checked-external-nominal-reference-contracts/v4")
    );
    assert_eq!(
        response.external_contracts[0].nominal_types,
        ["provider.Widget"]
    );
    assert!(response.external_contracts[0].exception_types.is_empty());
    assert!(
        response.external_contracts[0]
            .scope
            .contains("nominal-return-types-assumed")
    );
}

#[test]
fn optional_external_nominal_return_is_refuted_by_nonnull_assertion() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import Assert\nfrom provider import Widget, maybe\n\ndef run() -> None:\n    value = maybe()\n    Assert(value is not None)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from typing import Optional\nfrom nagini_contracts.contracts import ContractOnly\n\nclass Widget:\n    pass\n\n@ContractOnly\ndef maybe() -> Optional[Widget]:\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("checked-external-nominal-reference-contracts/v4")
    );
    assert_eq!(
        response.diagnostics[0].code,
        "assert.failed:assertion.false"
    );
}

#[test]
fn verifier_composes_transitive_source_nominal_reference_contracts() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "class Widget:\n    pass\n\ndef identity(value: Widget) -> Widget:\n    return value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("adapter.py"),
        "from provider import Widget, identity\n\ndef passthrough(value: Widget) -> Widget:\n    return identity(value)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import Assert\nfrom provider import Widget\nfrom adapter import passthrough\n\ndef run(value: Widget) -> None:\n    returned = passthrough(value)\n    Assert(returned is not None)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["identity".to_owned()],
            },
            SourceFile {
                path: "adapter.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["passthrough".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(response.source_imports.len(), 3);
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-nominal-reference-contracts/v4")
    );
    assert_eq!(
        response.files[2].fragment.as_deref(),
        Some("transitive-source-nominal-reference-contracts/v4")
    );
}

#[test]
fn verifier_composes_transitive_source_heap_permission_contracts() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def __init__(self, initial: int) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == initial)\n        self.value = initial\n\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import Cell\n\nclass NamedCell(Cell):\n    pass\n\ndef run(initial: int) -> None:\n    cell = NamedCell(initial)\n    observed = cell.get()\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Cell.__init__".to_owned(), "Cell.get".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(response.source_imports.len(), 1);
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|item| { item.id.contains(":method-call-precondition:get:") && item.satisfied() })
    );
}

fn create_protocol_package_heap_sources(initializer: &str) -> tempfile::TempDir {
    let directory = tempfile::tempdir().unwrap();
    fs::create_dir(directory.path().join("pkg")).unwrap();
    fs::write(directory.path().join("pkg/__init__.py"), initializer).unwrap();
    fs::write(
        directory.path().join("pkg/provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def __init__(self, initial: int) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == initial)\n        self.value = initial\n\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from pkg.provider import Cell\n\ndef run() -> None:\n    cell = Cell(7)\n    observed = cell.get()\n    assert observed == 7\n",
    )
    .unwrap();
    directory
}

fn protocol_package_heap_request(
    source_root: &std::path::Path,
    include_initializer: bool,
) -> ProofRequest {
    let mut files = Vec::new();
    if include_initializer {
        files.push(SourceFile {
            path: "pkg/__init__.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        });
    }
    files.extend([
        SourceFile {
            path: "pkg/provider.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["Cell.__init__".to_owned(), "Cell.get".to_owned()],
        },
        SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        },
    ]);
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: source_root.display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files,
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    }
}

#[test]
fn verifier_refuses_an_existing_package_initializer_omitted_from_source_closure() {
    let directory = create_protocol_package_heap_sources("__author__ = 'Maledictus Tests'\n");
    let response = maledictus::verify(&protocol_package_heap_request(directory.path(), false));

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.typecheck.misc"
                && diagnostic.path.as_deref() == Some("pkg/provider.py")
                && diagnostic.line.is_none()
        }),
        "{response:#?}"
    );
    assert!(
        !response
            .files
            .iter()
            .any(|file| file.path == "app.py" && matches!(file.result, ProofStatus::Proved)),
        "{response:#?}"
    );
}

#[test]
fn verifier_proves_explicit_empty_and_passive_package_initializers() {
    for initializer in ["", "__author__ = 'Maledictus Tests'\nPACKAGE_VERSION = 1\n"] {
        let directory = create_protocol_package_heap_sources(initializer);
        let response = maledictus::verify(&protocol_package_heap_request(directory.path(), true));

        assert!(
            matches!(response.status, ProofStatus::Proved),
            "initializer {initializer:?}: {response:#?}"
        );
        assert!(response.diagnostics.is_empty(), "{response:#?}");
        let package = response
            .files
            .iter()
            .find(|file| file.path == "pkg/__init__.py")
            .unwrap();
        assert!(
            matches!(package.result, ProofStatus::Proved),
            "{response:#?}"
        );
        assert_eq!(
            package.fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
        assert!(response.files.iter().any(|file| {
            file.path == "app.py"
                && matches!(file.result, ProofStatus::Proved)
                && file.fragment.as_deref() == Some("transitive-source-heap-contracts/v64")
        }));
    }
}

#[test]
fn verifier_refuses_consumers_of_an_explicitly_refuted_package_initializer() {
    let directory = create_protocol_package_heap_sources(
        "class Broken:\n    value: int\n\n    def get(self) -> int:\n        return self.value\n",
    );
    let response = maledictus::verify(&protocol_package_heap_request(directory.path(), true));

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.heap.package-initializer-refuted"
                && diagnostic.path.as_deref() == Some("app.py")
        }),
        "{response:#?}"
    );
    assert!(
        !response
            .files
            .iter()
            .any(|file| file.path == "app.py" && matches!(file.result, ProofStatus::Proved)),
        "{response:#?}"
    );
}

#[test]
fn verifier_composes_properties_and_pure_results_across_a_source_heap_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Item:\n    _value: int\n\n    def __init__(self, value: int) -> None:\n        Ensures(Acc(self._value))\n        Ensures(self.value == value * 2)\n        self._value = value\n\n    @property\n    def value(self) -> int:\n        Requires(Acc(self._value))\n        return self._value * 2\n\n    @value.setter\n    def value(self, doubled: int) -> None:\n        Requires(Acc(self._value))\n        Ensures(Acc(self._value))\n        Ensures(self._value == doubled // 2)\n        self._value = doubled // 2\n\n    @Pure\n    def non_zero(self) -> bool:\n        Requires(Acc(self._value))\n        return self.value != 0\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import Item\n\ndef run() -> None:\n    item = Item(5)\n    item.value = 8\n    assert item.value == 8\n    assert item.non_zero()\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: Vec::new(),
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(response.source_imports.len(), 1);
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains(":property-setter-precondition:value:")
            && obligation.satisfied()
    }));
}

#[test]
fn verifier_transfers_non_neutral_permissions_across_a_source_heap_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def __init__(self, initial: int) -> None:\n        Ensures(Acc(self.value))\n        self.value = initial\n\n    def diminish(self) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value, 1 / 2))\n        return\n\n    def consume(self) -> None:\n        Requires(Acc(self.value))\n        return\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("good.py"),
        "from provider import Cell\n\ndef run(initial: int) -> None:\n    cell = Cell(initial)\n    cell.diminish()\n    observed: int = cell.value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("bad.py"),
        "from provider import Cell\n\ndef run(initial: int) -> None:\n    cell = Cell(initial)\n    cell.consume()\n    observed: int = cell.value\n",
    )
    .unwrap();
    let source_file = SourceFile {
        path: "provider.py".to_owned(),
        language: "python".to_owned(),
        symbols: vec![
            "Cell.__init__".to_owned(),
            "Cell.diminish".to_owned(),
            "Cell.consume".to_owned(),
        ],
    };
    let request = |adapter: &str| ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            source_file.clone(),
            SourceFile {
                path: adapter.to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let good = maledictus::verify(&request("good.py"));
    assert!(matches!(good.status, ProofStatus::Proved), "{good:#?}");
    assert_eq!(
        good.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(good.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("run:method-call-permission-mask-valid:diminish")
            && obligation.satisfied()
    }));

    let bad = maledictus::verify(&request("bad.py"));
    assert!(matches!(bad.status, ProofStatus::Refuted), "{bad:#?}");
    assert!(bad.obligations.iter().any(|obligation| {
        obligation.id.contains("run:field-permission:value")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_composes_nominal_method_variance_across_a_source_heap_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Base:\n    pass\n\nclass Derived(Base):\n    pass\n\nclass Consumer:\n    marker: int\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\n    def accept(self, value: Derived, result: Derived) -> Base:\n        Requires(Acc(self.marker))\n        Ensures(Acc(self.marker))\n        return result\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Base, Derived, Consumer\n\nclass FlexibleConsumer(Consumer):\n    def accept(self, value: Base, result: Derived) -> Derived:\n        Requires(Acc(self.marker))\n        Ensures(Acc(self.marker))\n        return result\n\ndef run() -> None:\n    consumer = FlexibleConsumer()\n    value = Base()\n    result = Derived()\n    observed = consumer.accept(value, result)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: Vec::new(),
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{:#?}",
        response.diagnostics
    );
    assert_eq!(response.source_imports.len(), 1);
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("override:FlexibleConsumer.accept:Consumer:precondition-not-strengthened")
            && obligation.satisfied()
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("run:method-call-precondition:accept:")
            && obligation.satisfied()
    }));
}

#[test]
fn checked_external_heap_contract_reaches_json_backend_with_permission_effects() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import Cell\n\ndef run(initial: int) -> None:\n    cell = Cell(initial)\n    observed = cell.get()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    @ContractOnly\n    def __init__(self, initial: int) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == initial)\n        ...\n\n    @ContractOnly\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("checked-external-heap-contracts/v5")
    );
    assert_eq!(response.external_contracts[0].heap_types, ["provider.Cell"]);
    assert!(response.external_contracts[0].nominal_types.is_empty());
    assert!(
        response.external_contracts[0]
            .scope
            .contains("permission-effects-checked")
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|item| { item.id.contains(":method-call-precondition:get:") && item.satisfied() })
    );
}

#[test]
fn verifier_composes_source_and_external_heap_contracts_in_one_adapter() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass SourceCell:\n    value: int\n\n    def __init__(self, initial: int) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == initial)\n        self.value = initial\n\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import SourceCell\nfrom external_provider import ExternalCell\n\nclass NamedSourceCell(SourceCell):\n    pass\n\nclass NamedExternalCell(ExternalCell):\n    pass\n\ndef run(initial: int) -> None:\n    source_cell = NamedSourceCell(initial)\n    source_value = source_cell.get()\n    external_cell = NamedExternalCell(initial)\n    external_value = external_cell.get()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass ExternalCell:\n    value: int\n\n    @ContractOnly\n    def __init__(self, initial: int) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == initial)\n        ...\n\n    @ContractOnly\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec![
                    "SourceCell.__init__".to_owned(),
                    "SourceCell.get".to_owned(),
                ],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "external_provider".to_owned(),
            stub_path: "external_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source+checked-external-heap-contracts/v64")
    );
    assert_eq!(response.source_imports.len(), 1);
    assert_eq!(response.external_contracts.len(), 1);
}

#[test]
fn verifier_composes_source_and_external_scalar_contracts_in_one_adapter() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\ndef increment(value: int) -> int:\n    Ensures(Result() == value + 1)\n    return value + 1\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import increment\nfrom external_provider import double\n\ndef run(value: int) -> int:\n    Ensures(Result() == (value + 1) * 2)\n    incremented = increment(value)\n    return double(incremented)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_contract.py"),
        "from nagini_contracts.contracts import *\n\n@ContractOnly\ndef double(value: int) -> int:\n    Ensures(Result() == value * 2)\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["increment".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "external_provider".to_owned(),
            stub_path: "external_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty());
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source+checked-external-scalar-contracts/v33")
    );
    assert_eq!(response.source_imports.len(), 1);
    assert_eq!(response.external_contracts.len(), 1);
}

#[test]
fn verifier_composes_source_and_external_nominal_reference_contracts_in_one_adapter() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "class SourceWidget:\n    pass\n\ndef identity(value: SourceWidget) -> SourceWidget:\n    return value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import Assert\nfrom provider import SourceWidget, identity\nfrom external_provider import ExternalWidget, external_identity\n\ndef run(source: SourceWidget, external: ExternalWidget) -> None:\n    source_result = identity(source)\n    external_result = external_identity(external)\n    Assert(source_result is not None)\n    Assert(external_result is not None)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_contract.py"),
        "from nagini_contracts.contracts import ContractOnly\n\nclass ExternalWidget:\n    pass\n\n@ContractOnly\ndef external_identity(value: ExternalWidget) -> ExternalWidget:\n    ...\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["identity".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "external_provider".to_owned(),
            stub_path: "external_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty());
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source+checked-external-nominal-reference-contracts/v4")
    );
    assert_eq!(response.source_imports.len(), 1);
    assert_eq!(response.external_contracts.len(), 1);
}

#[test]
fn verifier_uses_real_strict_typescript_compiler_for_closed_functions() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("choose.ts"),
        "function selected(values: readonly number[], index: number, fail: boolean): number { if (fail) { throw \"bad\"; } return values[index] ?? values.length; }\nexport function choose(values: readonly number[], index: number, fail: boolean): number { try { return selected(values, index, fail); } catch { return values.length; } }\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "choose.ts".to_owned(),
            language: "typescript".to_owned(),
            symbols: vec!["choose".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("strict-typescript-closed-total-functions/v11")
    );
}

#[test]
fn verifier_returns_the_compiler_derived_primitive_leaf_interface() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("present.ts"),
        "export function present(value: string): string { return value; }\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "present.ts".to_owned(),
            language: "typescript".to_owned(),
            symbols: vec!["present".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(response.files[0].verified_interfaces.len(), 1);
    let interface = &response.files[0].verified_interfaces[0];
    assert_eq!(interface.symbol, "present");
    assert_eq!(interface.execution, "synchronous");
    assert_eq!(interface.parameters[0].name, "value");
    assert_eq!(interface.parameters[0].type_name, "string");
    assert_eq!(interface.return_type, "string");
}

#[test]
fn verifier_uses_real_check_js_compiler_for_closed_javascript_functions() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("choose.js"),
        "/** @param {boolean} fail @param {number} value @returns {number} */\nfunction selected(fail, value) { if (fail) { throw false; } return value; }\n/** @param {boolean} fail @param {number} value @returns {number} */\nexport function choose(fail, value) { try { return selected(fail, value); } catch (error) { return 0; } }\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "choose.js".to_owned(),
            language: "javascript".to_owned(),
            symbols: vec!["choose".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("strict-javascript-jsdoc-closed-total-functions/v11")
    );
    assert_eq!(
        response
            .typescript_toolchain
            .as_ref()
            .expect("checkJs proof must bind the compiler")
            .compiler_version,
        "5.9.3"
    );
}

#[test]
fn verifier_refuses_recursive_typescript_call_graph() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("recursive.ts"),
        "function left(value: number): number { return right(value); }\nfunction right(value: number): number { return left(value); }\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "recursive.ts".to_owned(),
            language: "typescript".to_owned(),
            symbols: vec!["left".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.typescript.call-cycle-unsupported"
    );
}

#[test]
fn verifier_proves_symbolic_python_string_contracts_through_z3() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("strings.py"),
        "from nagini_contracts.contracts import *\n\ndef append(left: str, right: str) -> str:\n    Ensures(Result() == left + right)\n    Ensures(len(Result()) == len(left) + len(right))\n    return left + right\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "strings.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["append".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert_eq!(response.solver.unwrap().vc_ir, "maledictus-scalar-vc/v27");
}

#[test]
fn verifier_proves_fixed_typed_python_tuple_contracts_through_z3() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("tuples.py"),
        "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef pair(number: int, text: str) -> Tuple[int, str]:\n    Ensures(Result()[0] == number)\n    Ensures(Result()[1] == text)\n    return number, text\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "tuples.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["pair".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert_eq!(response.solver.unwrap().vc_ir, "maledictus-scalar-vc/v27");
}

#[test]
fn verifier_proves_homogeneous_typed_python_list_contracts_through_z3() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("lists.py"),
        "from nagini_contracts.contracts import *\nfrom typing import List\n\ndef preserve(values: List[int]) -> List[int]:\n    Ensures(Result() == values)\n    Ensures(len(Result()) == len(values))\n    return values\n\ndef first(values: List[int]) -> int:\n    Requires(len(values) > 0)\n    return values[0]\n\ndef first_or_default(values: List[int]) -> int:\n    try:\n        return values[0]\n    except IndexError:\n        return -1\n\ndef run() -> int:\n    values: List[int] = [3, 8]\n    assert len(values) == 2\n    assert values[-1] == 8\n    return values[0]\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "lists.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec![
                "preserve".to_owned(),
                "first".to_owned(),
                "first_or_default".to_owned(),
                "run".to_owned(),
            ],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert!(response.diagnostics.is_empty());
    assert_eq!(response.solver.unwrap().vc_ir, "maledictus-scalar-vc/v27");
}

#[test]
fn verifier_refutes_an_unbounded_list_index_as_undeclared_index_error() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("lists.py"),
        "from typing import List\n\ndef broken(values: List[int]) -> int:\n    return values[0]\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "lists.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["broken".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert!(response.obligations.iter().any(|item| {
        item.id.contains(":exception-undeclared:IndexError:")
            && item.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_refuses_typescript_compiler_error() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("invalid.ts"),
        "function invalid(value: number): string { return value; }\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "invalid.ts".to_owned(),
            language: "typescript".to_owned(),
            symbols: vec!["invalid".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.typescript.strict-typecheck"
    );
}

#[test]
fn verifier_refuses_javascript_check_js_compiler_error() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("invalid.js"),
        "/** @param {number} value @returns {string} */\nfunction invalid(value) { return value; }\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "invalid.js".to_owned(),
            language: "javascript".to_owned(),
            symbols: vec!["invalid".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.javascript.strict-typecheck"
    );
}

#[test]
fn verifier_proves_heap_read_from_real_acc_contract() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("cell.py"),
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "cell.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["Cell.get".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.solver.is_some());
}

#[test]
fn verifier_exposes_constructor_nullability_as_heap_obligations() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("constructor_nullability.py"),
        "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass B:\n    pass\n\nclass C:\n    pass\n\nclass OptionalHolder:\n    def __init__(self) -> None:\n        self.b = None  # type: Optional[B]\n        self.c = None  # type: Optional[C]\n\n    def compare(self) -> None:\n        Requires(Acc(self.b) and Acc(self.c))\n        Assert(self.b is not self.c)\n\nclass RequiredHolder:\n    def __init__(self) -> None:\n        Ensures(Acc(self.b))\n        self.b = None  # type: B\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "constructor_nullability.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec![
                "OptionalHolder.compare".to_owned(),
                "RequiredHolder.__init__".to_owned(),
            ],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = analyze_frontend_request(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("OptionalHolder.compare:assert:") && !obligation.satisfied()
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "RequiredHolder.__init__:postcondition:implicit-non-null-fields"
            && !obligation.satisfied()
    }));
}

#[test]
fn verifier_composes_inherited_properties_and_pure_method_bodies() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("property.py"),
        "from nagini_contracts.contracts import *\n\nclass A:\n    _field: int\n\n    def __init__(self, val: int) -> None:\n        Ensures(Acc(self._field))\n        Ensures(self.field == val)\n        self._field = val\n\n    @property\n    def field(self) -> int:\n        Requires(Acc(self._field))\n        return self._field\n\nclass B(A):\n    def __init__(self, val: int) -> None:\n        Ensures(Acc(self._field))\n        Ensures(self.field == val)\n        super().__init__(val)\n\n    @Pure\n    def non_zero(self) -> bool:\n        Requires(Acc(self._field))\n        return self.field != 0\n\ndef test() -> None:\n    b = B(5)\n    assert b.non_zero()\n\nclass C(A):\n    def __init__(self, val: int) -> None:\n        Ensures(Acc(self._field))\n        Ensures(self.field == val + 1)\n        super().__init__(val)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "property.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("test:assert:") && obligation.satisfied()
        })
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "C.__init__:postcondition:1" && !obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_computed_property_getters_setters_and_chained_receivers() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("computed_property.py"),
        "from nagini_contracts.contracts import *\n\nclass A:\n    value: int\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        self.value = 12\n\n    @property\n    def doubled(self) -> int:\n        Requires(Acc(self.value))\n        return self.value * 2\n\n    @doubled.setter\n    def doubled(self, doubled: int) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(self.value == doubled // 2)\n        self.value = doubled // 2\n\n    @property\n    def slf(self) -> 'A':\n        return self\n\ndef exercise(a: A) -> None:\n    Requires(Acc(a.value))\n    Ensures(Acc(a.value))\n    a.slf.slf.doubled = 8\n    assert a.slf.slf.doubled == 8\n    assert a.value == 4\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "computed_property.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains(":property-setter-precondition:doubled:")
            && obligation.satisfied()
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains(":property-precondition:doubled:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_class_typed_heap_function_contracts() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("cell.py"),
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n\ndef inspect(cell: Cell, expected: int) -> None:\n    Requires(Acc(cell.value))\n    Requires(cell.value == expected)\n    observed = cell.get()\n    copied: int = cell.value\n    Assert(cell.value == observed)\n    Assert(cell.value == copied)\n    Ensures(Acc(cell.value))\n    Ensures(cell.value == expected)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "cell.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["inspect".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains(":method-call-precondition:get:") && obligation.satisfied()
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("inspect:postcondition:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_inherited_constructor_field_and_method_contracts() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("inheritance.py"),
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def __init__(self, initial: int) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == initial)\n        self.value = initial\n\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n\nclass NamedCell(Cell):\n    pass\n\ndef build(initial: int) -> None:\n    cell = NamedCell(initial)\n    observed = cell.get()\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "inheritance.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["build".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains(":method-call-precondition:get:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_a_direct_super_constructor_call() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("super_constructor.py"),
        "from nagini_contracts.contracts import *\n\nclass Base:\n    base_value: int\n\n    def __init__(self, value: int) -> None:\n        Ensures(Acc(self.base_value))\n        Ensures(self.base_value == value)\n        self.base_value = value\n\nclass Derived(Base):\n    own_value: int\n\n    def __init__(self, base_value: int, own_value: int) -> None:\n        Ensures(Acc(self.base_value))\n        Ensures(Acc(self.own_value))\n        Ensures(self.base_value == base_value)\n        Ensures(self.own_value == own_value)\n        super().__init__(base_value)\n        self.own_value = own_value\n\ndef build(base_value: int, own_value: int) -> None:\n    item = Derived(base_value, own_value)\n    Assert(item.base_value == base_value)\n    Assert(item.own_value == own_value)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "super_constructor.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["build".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("Derived.__init__:postcondition:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_refutes_a_behaviorally_incompatible_override() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("override.py"),
        "from nagini_contracts.contracts import *\n\nclass Base:\n    value: int\n\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        return self.value\n\nclass Derived(Base):\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Requires(self.value > 0)\n        Ensures(Acc(self.value))\n        return self.value\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "override.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    let override_obligation = response
        .obligations
        .iter()
        .find(|obligation| {
            obligation.id == "override:Derived.get:Base:precondition-not-strengthened"
        })
        .expect("behavioral override obligation");
    assert_eq!(
        override_obligation.status,
        maledictus::vc::ObligationStatus::Refuted
    );
    assert_eq!(override_obligation.line, 12);
    assert_eq!(override_obligation.column, 5);
}

#[test]
fn verifier_reports_typed_permission_and_default_override_failures() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("override_effects.py"),
        "from nagini_contracts.contracts import *\n\nclass Data:\n    value: int\n\nclass Base:\n    def read(self, item: Data) -> int:\n        Requires(Acc(item.value, 1 / 2))\n        Ensures(Acc(item.value, 1 / 4))\n        return item.value\n\n    def choose(self, value: int = 23) -> int:\n        return value\n\nclass BadPermission(Base):\n    def read(self, item: Data) -> int:\n        Requires(Acc(item.value, 2 / 3))\n        Ensures(Acc(item.value, 2 / 3))\n        return item.value\n\nclass BadDefault(Base):\n    def choose(self, value: int = 56) -> int:\n        return value\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "override_effects.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "call.precondition:insufficient.permission"
            && diagnostic.line == Some(16)
    }));
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "assert.failed:assertion.false" && diagnostic.line == Some(22)
    }));
}

#[test]
fn verifier_proves_nominal_variance_and_parameter_field_contracts() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("nominal_variance.py"),
        "from nagini_contracts.contracts import *\n\nclass CellBase:\n    value: int\n\n    def __init__(self, initial: int) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == initial)\n        self.value = initial\n\nclass Cell(CellBase):\n    pass\n\nclass ReaderBase:\n    def read(self, cell: Cell, result: Cell) -> CellBase:\n        Requires(Acc(cell.value))\n        Ensures(Acc(cell.value))\n        return result\n\nclass Reader(ReaderBase):\n    def read(self, cell: CellBase, result: Cell) -> Cell:\n        Requires(Acc(cell.value))\n        Ensures(Acc(cell.value))\n        return result\n\ndef run(initial: int) -> None:\n    cell = CellBase(initial)\n    result = Cell(initial)\n    reader = Reader()\n    observed = reader.read(cell, result)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "nominal_variance.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{:#?}",
        response.diagnostics
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("override:Reader.read:ReaderBase:precondition-not-strengthened")
            && obligation.satisfied()
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("run:method-call-precondition:read:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_refuses_nominal_override_variance_violations() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("bad_variance.py"),
        "from nagini_contracts.contracts import *\n\nclass Base:\n    pass\n\nclass Derived(Base):\n    pass\n\nclass MoreDerived(Derived):\n    pass\n\nclass HandlerBase:\n    marker: int\n\n    def choose(self, value: Derived, result: MoreDerived) -> Derived:\n        Requires(Acc(self.marker))\n        Ensures(Acc(self.marker))\n        return result\n\nclass HandlerBad(HandlerBase):\n    def choose(self, value: MoreDerived, result: MoreDerived) -> Base:\n        Requires(Acc(self.marker))\n        Ensures(Acc(self.marker))\n        return result\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "bad_variance.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = analyze_frontend_request(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.python.heap.override-signature-incompatible"
    );
    assert_eq!(
        response.diagnostics[0].path.as_deref(),
        Some("bad_variance.py")
    );
    assert!(
        response.diagnostics[0]
            .message
            .contains("violates contravariant parameter or covariant return typing")
    );
}

#[test]
fn verifier_refuses_an_unrelated_nominal_method_argument() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("bad_call.py"),
        "from nagini_contracts.contracts import *\n\nclass Expected:\n    pass\n\nclass Unrelated:\n    pass\n\nclass Consumer:\n    marker: int\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\n    def accept(self, value: Expected) -> None:\n        Requires(Acc(self.marker))\n        Ensures(Acc(self.marker))\n\ndef run() -> None:\n    consumer = Consumer()\n    value = Unrelated()\n    ignored = consumer.accept(value)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "bad_call.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = analyze_frontend_request(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.python.heap.method-call-nominal-argument-mismatch"
    );
}

#[test]
fn verifier_refutes_a_source_order_undefined_base_class() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("unresolved.py"),
        "class Child(Missing):\n    value: int\n\n    def get(self) -> int:\n        return self.value\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "unresolved.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = analyze_frontend_request(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.diagnostics[0].code,
        "assert.failed:assertion.false"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|obligation| obligation.id == "module:undefined-base:Child")
    );
}

#[test]
fn verifier_proves_real_dagcert_operation_module() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass WorkInput:\n    value: int\n\n@dataclass(frozen=True)\nclass WorkCompleted:\n    value: int\n\n@operation\ndef work(request: WorkInput) -> WorkCompleted:\n    return WorkCompleted(request.value + 1)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["work".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("dagcert-closed-typed-operations/v3")
    );
}

#[test]
fn verifier_refuses_partial_expression_inside_dagcert_operation() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass WorkInput:\n    value: int\n\n@dataclass(frozen=True)\nclass WorkCompleted:\n    value: int\n\n@operation\ndef work(request: WorkInput) -> WorkCompleted:\n    return WorkCompleted(10 // request.value)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["work".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert_eq!(
        response.diagnostics[0].code,
        "frontend.python.dagcert.partial-or-unsupported-operator"
    );
    assert_eq!(response.diagnostics[0].line, Some(14));
    assert_eq!(response.diagnostics[0].column, Some(26));
}

#[test]
fn verifier_proves_inferred_constructor_field_and_module_call_path() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\n\nclass A:\n    def __init__(self, a: int) -> None:\n        Ensures(Acc(self.a))  # type: ignore\n        Ensures(self.a == a)  # type: ignore\n        self.a = a\n\n    def m1(self, x: int) -> int:\n        Ensures(Result() == x)\n        return x\n\ndef main() -> None:\n    c = A(2).m1(5)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec![
                "A.__init__".to_owned(),
                "A.m1".to_owned(),
                "main".to_owned(),
            ],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.diagnostics.is_empty());
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "main:heap-function-complete" && obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_nested_constructor_result_retains_parent_identity() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class2:\n    def __init__(self, parent: 'Class1') -> None:\n        Ensures(Acc(self.parent))\n        Ensures(self.parent is parent)\n        self.parent = parent\n\nclass Class1:\n    def __init__(self) -> None:\n        Ensures(Acc(self.child))\n        Ensures(Acc(self.child.parent))\n        Ensures(self.child.parent is self)\n        self.child = Class2(self)\n\ndef run() -> None:\n    parent = Class1()\n    Assert(parent.child.parent is parent)\n",
        &["Class1.__init__", "Class2.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty());
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_proves_contextual_conjunction_of_nested_acc_and_reference_identity() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Child:\n    def __init__(self, parent: 'Parent') -> None:\n        Ensures(Acc(self.parent))\n        Ensures(self.parent is parent)\n        self.parent = parent\n\nclass Parent:\n    def __init__(self) -> None:\n        Ensures(Acc(self.child))\n        Ensures(Acc(self.child.parent) and self.child.parent is self)\n        self.child = Child(self)\n\ndef run() -> None:\n    parent = Parent()\n    Assert(parent.child.parent is parent)\n",
        &["Child.__init__", "Parent.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refutes_contextual_disjunction_without_inventing_nested_permission() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Child:\n    def __init__(self, parent: 'Parent') -> None:\n        self.parent = parent\n\nclass Parent:\n    def __init__(self) -> None:\n        Ensures(Acc(self.child))\n        Ensures(Acc(self.child.parent) or self.child.parent is self)\n        self.child = Child(self)\n\ndef run() -> None:\n    parent = Parent()\n    Assert(parent.child.parent is parent)\n",
        &["Child.__init__", "Parent.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "field.read:insufficient.permission"
            || diagnostic.code == "postcondition.violated:assertion.false"
    }));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("field-permission:parent") && !obligation.satisfied()
    }));
}

#[test]
fn verifier_refuses_non_boolean_contextual_conjunct_without_exporting_a_heap_proof() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Child:\n    def __init__(self, parent: 'Parent') -> None:\n        self.parent = parent\n\nclass Parent:\n    def __init__(self) -> None:\n        Ensures(Acc(self.child))\n        Ensures(Acc(self.child.parent) and self.child.parent)\n        self.child = Child(self)\n\ndef run() -> None:\n    parent = Parent()\n    Assert(parent.child.parent is parent)\n",
        &["Child.__init__", "Parent.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "frontend.python.heap.contextual-boolop-operand-type-mismatch"
    }));
    assert!(response.files[0].fragment.is_none());
    assert!(
        !response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refuses_effectful_contextual_conjunct_without_exporting_a_heap_proof() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Child:\n    def __init__(self, parent: 'Parent') -> None:\n        self.parent = parent\n\nclass Parent:\n    def helper(self) -> bool:\n        return True\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.child))\n        Ensures(Acc(self.child.parent) and self.helper())\n        self.child = Child(self)\n\ndef run() -> None:\n    parent = Parent()\n    Assert(parent.child.parent is parent)\n",
        &["Child.__init__", "Parent.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "frontend.python.heap.contextual-boolop-operand-unsupported"
    }));
    assert!(response.files[0].fragment.is_none());
    assert!(
        !response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refuses_mixed_nominal_contextual_identity_without_exporting_a_heap_proof() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Other:\n    pass\n\nclass Child:\n    def __init__(self, parent: 'Parent') -> None:\n        self.parent = parent\n\nclass Parent:\n    def __init__(self, other: Other) -> None:\n        Ensures(Acc(self.child))\n        Ensures(Acc(self.child.parent) and self.child.parent is other)\n        self.child = Child(self)\n\ndef run(other: Other) -> None:\n    parent = Parent(other)\n    Assert(parent.child.parent is parent)\n",
        &["Child.__init__", "Parent.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "frontend.python.heap.contextual-boolop-operand-type-mismatch"
    }));
    assert!(response.files[0].fragment.is_none());
    assert!(
        !response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_proves_inferred_and_declared_nominal_field_returns() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass InferredHolder:\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        self.value = Leaf()\n\n    @Pure\n    def get(self) -> Leaf:\n        Requires(Acc(self.value))\n        return self.value\n\nclass DeclaredHolder:\n    value: Leaf\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        self.value = Leaf()\n\n    @Pure\n    def get(self) -> Leaf:\n        Requires(Acc(self.value))\n        return self.value\n",
        &[
            "InferredHolder.__init__",
            "InferredHolder.get",
            "DeclaredHolder.__init__",
            "DeclaredHolder.get",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("InferredHolder.get:")
            && obligation.id.contains(":field-permission:")
            && obligation.satisfied()
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("DeclaredHolder.get:")
            && obligation.id.contains(":field-permission:")
            && obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_nested_nominal_field_chain_return() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Parent:\n    pass\n\nclass Child:\n    parent: Parent\n\n    def __init__(self, parent: Parent) -> None:\n        Ensures(Acc(self.parent))\n        Ensures(self.parent is parent)\n        self.parent = parent\n\nclass Holder:\n    child: Child\n\n    def __init__(self, parent: Parent) -> None:\n        Ensures(Acc(self.child))\n        Ensures(Acc(self.child.parent))\n        self.child = Child(parent)\n\n    @Pure\n    def get_parent(self) -> Parent:\n        Requires(Acc(self.child))\n        Requires(Acc(self.child.parent))\n        return self.child.parent\n",
        &["Child.__init__", "Holder.__init__", "Holder.get_parent"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("Holder.get_parent:")
            && obligation.id.contains(":field-permission:")
            && obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_subtype_field_returned_as_base_type() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Base:\n    pass\n\nclass Derived(Base):\n    pass\n\nclass Holder:\n    value: Derived\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        self.value = Derived()\n\n    @Pure\n    def get_base(self) -> Base:\n        Requires(Acc(self.value))\n        return self.value\n",
        &["Holder.__init__", "Holder.get_base"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("Holder.get_base:")
            && obligation.id.contains(":field-permission:")
            && obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_inherited_and_property_nominal_field_returns() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass BaseHolder:\n    value: Leaf\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        self.value = Leaf()\n\nclass DerivedHolder(BaseHolder):\n    @Pure\n    def inherited_value(self) -> Leaf:\n        Requires(Acc(self.value))\n        return self.value\n\n    @property\n    def selected(self) -> Leaf:\n        Requires(Acc(self.value))\n        return self.value\n\n    @Pure\n    def property_value(self) -> Leaf:\n        Requires(Acc(self.value))\n        return self.selected\n",
        &[
            "BaseHolder.__init__",
            "DerivedHolder.inherited_value",
            "DerivedHolder.selected@property",
            "DerivedHolder.property_value",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("DerivedHolder.inherited_value:")
            && obligation.id.contains(":field-permission:")
            && obligation.satisfied()
    }));
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("DerivedHolder.property_value:")
                && obligation.id.contains(":property-precondition:selected:")
                && obligation.satisfied()
        }),
        "{response:#?}"
    );
}

#[test]
fn verifier_refuses_wrong_nominal_field_return_without_exporting_a_proof() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Expected:\n    pass\n\nclass Wrong:\n    pass\n\nclass Holder:\n    value: Wrong\n\n    @Pure\n    def get(self) -> Expected:\n        Requires(Acc(self.value))\n        return self.value\n\ndef run(holder: Holder) -> None:\n    value = holder.get()\n    Assert(isinstance(value, Expected))\n",
        &["Holder.get", "run"],
    );
    assert_heap_refusal_without_exported_proof(
        &response,
        "frontend.python.heap.return-nominal-type-mismatch",
    );
}

#[test]
fn verifier_refuses_optional_field_as_nonoptional_return_without_exporting_a_proof() {
    let response = verify_heap_program(
        "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    value: Optional[Leaf]\n\n    @Pure\n    def get(self) -> Leaf:\n        Requires(Acc(self.value))\n        return self.value  # type: ignore\n\ndef run(holder: Holder) -> None:\n    value = holder.get()\n    Assert(value is not None)\n",
        &["Holder.get", "run"],
    );
    assert_heap_refusal_without_exported_proof(
        &response,
        "frontend.python.heap.return-nominal-type-optional",
    );
}

#[test]
fn verifier_refuses_optional_intermediate_return_receiver_without_exporting_a_proof() {
    let response = verify_heap_program(
        "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Parent:\n    pass\n\nclass Child:\n    parent: Parent\n\nclass Holder:\n    child: Optional[Child]\n\n    @Pure\n    def get_parent(self) -> Parent:\n        Requires(Acc(self.child))\n        return self.child.parent  # type: ignore\n\ndef run(holder: Holder) -> None:\n    parent = holder.get_parent()\n    Assert(parent is not None)\n",
        &["Holder.get_parent", "run"],
    );
    assert_heap_refusal_without_exported_proof(
        &response,
        "frontend.python.heap.return-nominal-type-optional-receiver",
    );
}

#[test]
fn verifier_refuses_scalar_field_as_nominal_return_without_exporting_a_proof() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    value: int\n\n    @Pure\n    def get(self) -> Leaf:\n        Requires(Acc(self.value))\n        return self.value  # type: ignore\n\ndef run(holder: Holder) -> None:\n    value = holder.get()\n    Assert(isinstance(value, Leaf))\n",
        &["Holder.get", "run"],
    );
    assert_heap_refusal_without_exported_proof(
        &response,
        "frontend.python.heap.return-nominal-type-unresolved",
    );
}

#[test]
fn verifier_composes_pure_call_expression_as_nominal_return() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    leaf: Leaf\n\n    @Pure\n    def build(self) -> Leaf:\n        Requires(Acc(self.leaf))\n        return self.leaf\n\n    @Pure\n    def get(self) -> Leaf:\n        Requires(Acc(self.leaf))\n        return self.build()\n\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.leaf))\n    value = holder.get()\n    Assert(isinstance(value, Leaf))\n",
        &["Holder.build", "Holder.get", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|obligation| obligation.id.starts_with("run:assert:") && obligation.satisfied()),
        "{response:#?}"
    );
}

#[test]
fn verifier_refuses_scalar_property_as_nominal_return_without_exporting_a_proof() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    count: int\n\n    @property\n    def selected(self) -> int:\n        Requires(Acc(self.count))\n        return self.count\n\n    @Pure\n    def get(self) -> Leaf:\n        Requires(Acc(self.count))\n        return self.selected  # type: ignore\n\ndef run(holder: Holder) -> None:\n    value = holder.get()\n    Assert(isinstance(value, Leaf))\n",
        &["Holder.selected", "Holder.get", "run"],
    );
    assert_heap_refusal_without_exported_proof(
        &response,
        "frontend.python.heap.return-nominal-type-unresolved",
    );
}

#[test]
fn verifier_refuses_multi_hop_property_return_chains_without_exporting_a_proof() {
    let intermediate_property = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Child:\n    leaf: Leaf\n\nclass Holder:\n    child: Child\n\n    @property\n    def selected(self) -> Child:\n        Requires(Acc(self.child))\n        return self.child\n\n    @Pure\n    def get(self) -> Leaf:\n        Requires(Acc(self.child))\n        Requires(Acc(self.child.leaf))\n        return self.selected.leaf\n",
        &["Holder.get"],
    );
    assert_heap_refusal_without_exported_proof(
        &intermediate_property,
        "frontend.python.heap.return-nominal-property-chain-unsupported",
    );

    let property_after_field = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Child:\n    leaf: Leaf\n\n    @property\n    def selected(self) -> Leaf:\n        Requires(Acc(self.leaf))\n        return self.leaf\n\nclass Holder:\n    child: Child\n\n    @Pure\n    def get(self) -> Leaf:\n        Requires(Acc(self.child))\n        Requires(Acc(self.child.leaf))\n        return self.child.selected\n",
        &["Holder.get"],
    );
    assert_heap_refusal_without_exported_proof(
        &property_after_field,
        "frontend.python.heap.return-nominal-property-chain-unsupported",
    );
}

#[test]
fn verifier_proves_old_identity_for_exact_reference_field() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class2:\n    pass\n\nclass Class1:\n    c2: Class2\n\n    def get_c2_impure(self) -> Class2:\n        Requires(Acc(self.c2))\n        Ensures(Acc(self.c2))\n        Ensures(self.c2 is Old(self.c2))\n        return self.c2\n",
        &["Class1.get_c2_impure"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("Class1.get_c2_impure:")
            && obligation.id.contains(":old-field-permission:")
            && obligation.satisfied()
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("Class1.get_c2_impure:postcondition:")
            && obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_old_identity_while_writing_an_unrelated_framed_field() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    counter: int\n\n    def touch_counter(self) -> Leaf:\n        Requires(Acc(self.f))\n        Requires(Acc(self.counter))\n        Ensures(Acc(self.f))\n        Ensures(Acc(self.counter))\n        Ensures(self.f is Old(self.f))\n        self.counter = self.counter + 1\n        return self.f\n",
        &["Holder.touch_counter"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("Holder.touch_counter:postcondition:")
            && obligation.satisfied()
    }));
}

#[test]
fn verifier_composes_old_identity_across_a_source_module_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n\n    def stable(self) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(self.f is Old(self.f))\n        return self.f\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Holder\n\nclass Caller(Holder):\n    def run(self) -> None:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(self.f is Old(self.f))\n        observed = self.stable()\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Holder.stable".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Caller.run".to_owned()],
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
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("Caller.run:")
            && obligation.id.contains(":old-field-permission:")
            && obligation.satisfied()
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("Caller.run:postcondition:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_refuses_old_identity_when_the_same_field_is_modified() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n\n    def replace(self, replacement: Leaf) -> None:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(self.f is Old(self.f))\n        self.f = replacement\n",
        &["Holder.replace"],
    );
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.old-field-modified-unsupported",
    );
}

#[test]
fn verifier_refutes_old_identity_without_entry_permission() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n\n    def stable(self) -> None:\n        Ensures(self.f is Old(self.f))\n",
        &["Holder.stable"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("Holder.stable:")
            && obligation.id.contains(":old-field-permission:")
            && matches!(obligation.status, maledictus::vc::ObligationStatus::Refuted)
    }));
}

#[test]
fn verifier_refutes_false_old_nonidentity_for_an_unchanged_field() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n\n    def stable(self) -> None:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(self.f is not Old(self.f))\n",
        &["Holder.stable"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("Holder.stable:postcondition:")
            && matches!(obligation.status, maledictus::vc::ObligationStatus::Refuted)
    }));
}

#[test]
fn verifier_proves_direct_scalar_old_field_equality_for_an_unchanged_field() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Holder:\n    f: int\n    def stable(self) -> None:\n        Requires(Acc(self.f))\n        Ensures(self.f == Old(self.f))\n",
        &["Holder.stable"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("Holder.stable:postcondition:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_refuses_unsupported_old_expression_shapes_without_exporting_a_proof() {
    let fixtures = [
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    def stable(self) -> None:\n        Requires(Acc(self.f))\n        Ensures(Old())\n",
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    def stable(self) -> None:\n        Requires(Acc(self.f))\n        Ensures(self.f is Old(Old(self.f)))\n",
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    g: Leaf\n    def stable(self) -> None:\n        Requires(Acc(self.f))\n        Requires(Acc(self.g))\n        Ensures(self.f is Old(self.g))\n",
        "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Optional[Leaf]\n    def stable(self) -> None:\n        Requires(Acc(self.f))\n        Ensures(self.f is Old(self.f))\n",
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Child:\n    f: Leaf\n\nclass Holder:\n    child: Child\n    def stable(self) -> None:\n        Requires(Acc(self.child))\n        Requires(Acc(self.child.f))\n        Ensures(self.child.f is Old(self.child.f))\n",
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    @property\n    def selected(self) -> Leaf:\n        Requires(Acc(self.f))\n        return self.f\n    def stable(self) -> None:\n        Requires(Acc(self.f))\n        Ensures(self.selected is Old(self.selected))\n",
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    @Pure\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        return self.f\n    def stable(self) -> None:\n        Requires(Acc(self.f))\n        Ensures(self.get() is Old(self.get()))\n",
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    selected: Leaf\n    backing: Leaf\n    @property\n    def selected(self) -> Leaf:\n        Requires(Acc(self.backing))\n        return self.backing\n    def stable(self) -> None:\n        Ensures(self.selected is Old(self.selected))\n",
    ];
    for source in fixtures {
        let response = verify_heap_program(source, &["Holder.stable"]);
        assert_heap_refusal_without_any_proof(
            &response,
            "frontend.python.heap.old-expression-unsupported",
        );
    }
}

#[test]
fn verifier_refuses_old_in_constructor_or_exceptional_postcondition() {
    let constructor = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    def __init__(self, f: Leaf) -> None:\n        Ensures(self.f is Old(self.f))\n        self.f = f\n",
        &["Holder.__init__"],
    );
    assert_heap_refusal_without_any_proof(
        &constructor,
        "frontend.python.heap.old-constructor-unsupported",
    );

    let exceptional = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Failure(Exception):\n    pass\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    def stable(self) -> None:\n        Requires(Acc(self.f))\n        Exsures(Failure, self.f is Old(self.f))\n",
        &["Holder.stable"],
    );
    assert_heap_refusal_without_any_proof(
        &exceptional,
        "frontend.python.heap.old-exception-postcondition-unsupported",
    );
}

#[test]
fn verifier_refuses_old_in_external_contract_without_exporting_a_proof() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import Holder\n\ndef run(holder: Holder) -> None:\n    holder.stable()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass Holder:\n    f: Holder\n\n    @ContractOnly\n    def stable(self) -> None:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(self.f is Old(self.f))\n        ...\n",
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
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.external-old-unsupported",
    );
}

#[test]
fn verifier_proves_direct_and_inherited_result_field_identity() {
    let direct = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(Result() is self.f)\n        return self.f\n",
        &["Holder.get"],
    );
    assert!(matches!(direct.status, ProofStatus::Proved), "{direct:#?}");
    assert_eq!(
        direct.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(direct.obligations.iter().any(|obligation| {
        obligation.id.contains("Holder.get:postcondition:") && obligation.satisfied()
    }));

    let inherited = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Base:\n    f: Leaf\n\nclass Derived(Base):\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(Result() is self.f)\n        return self.f\n",
        &["Derived.get"],
    );
    assert!(
        matches!(inherited.status, ProofStatus::Proved),
        "{inherited:#?}"
    );
    assert_eq!(
        inherited.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(inherited.obligations.iter().any(|obligation| {
        obligation.id.contains("Derived.get:postcondition:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_refutes_false_result_field_identity_claims() {
    let false_nonidentity = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(Result() is not self.f)\n        return self.f\n",
        &["Holder.get"],
    );
    assert!(
        matches!(false_nonidentity.status, ProofStatus::Refuted),
        "{false_nonidentity:#?}"
    );
    assert_eq!(
        false_nonidentity.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(false_nonidentity.obligations.iter().any(|obligation| {
        obligation.id.contains("Holder.get:postcondition:")
            && matches!(obligation.status, maledictus::vc::ObligationStatus::Refuted)
    }));

    let wrong_compatible_field = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    g: Leaf\n\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Requires(Acc(self.g))\n        Ensures(Acc(self.f))\n        Ensures(Acc(self.g))\n        Ensures(Result() is self.f)\n        return self.g\n",
        &["Holder.get"],
    );
    assert!(
        matches!(wrong_compatible_field.status, ProofStatus::Refuted),
        "{wrong_compatible_field:#?}"
    );
    assert_eq!(
        wrong_compatible_field.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(wrong_compatible_field.obligations.iter().any(|obligation| {
        obligation.id.contains("Holder.get:postcondition:")
            && matches!(obligation.status, maledictus::vc::ObligationStatus::Refuted)
    }));

    let arbitrary_parameter = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    def get(self, other: Leaf) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Result() is self.f)\n        return other\n",
        &["Holder.get"],
    );
    assert!(
        matches!(arbitrary_parameter.status, ProofStatus::Refuted),
        "{arbitrary_parameter:#?}"
    );
    assert_eq!(
        arbitrary_parameter.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(arbitrary_parameter.obligations.iter().any(|obligation| {
        obligation.id.contains("Holder.get:postcondition:")
            && matches!(obligation.status, maledictus::vc::ObligationStatus::Refuted)
    }));
}

#[test]
fn verifier_composes_result_field_identity_across_a_source_module_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(Result() is self.f)\n        return self.f\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Holder\n\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.f))\n    observed = holder.get()\n    Assert(observed is holder.f)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Holder.get".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refuses_unsupported_result_identity_shapes_without_exporting_a_proof() {
    let cases = [
        (
            "from nagini_contracts.contracts import *\n\nclass Holder:\n    f: int\n    def get(self) -> int:\n        Requires(Acc(self.f))\n        Ensures(Result() is self.f)\n        return self.f\n",
            "frontend.python.heap.result-identity-expression-unsupported",
        ),
        (
            "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Optional[Leaf]\n    fallback: Leaf\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Requires(Acc(self.fallback))\n        Ensures(Result() is self.f)\n        return self.fallback\n",
            "frontend.python.heap.result-identity-expression-unsupported",
        ),
        (
            "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    value: Leaf\n    def get(self) -> Optional[Leaf]:\n        Requires(Acc(self.value))\n        Ensures(Result() is self.value)\n        return self.value\n",
            "frontend.python.heap.type-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Child:\n    f: Leaf\n\nclass Holder:\n    child: Child\n    fallback: Leaf\n    def get(self) -> Leaf:\n        Requires(Acc(self.fallback))\n        Ensures(Result() is self.child.f)\n        return self.fallback\n",
            "frontend.python.heap.result-identity-expression-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    @property\n    def selected(self) -> Leaf:\n        Requires(Acc(self.f))\n        return self.f\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Result() is self.selected)\n        return self.f\n",
            "frontend.python.heap.result-identity-expression-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    selected: Leaf\n    backing: Leaf\n    @property\n    def selected(self) -> Leaf:\n        Requires(Acc(self.backing))\n        return self.backing\n    def get(self) -> Leaf:\n        Requires(Acc(self.backing))\n        Ensures(Result() is self.selected)\n        return self.backing\n",
            "frontend.python.heap.result-identity-expression-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    @Pure\n    def selected(self) -> Leaf:\n        Requires(Acc(self.f))\n        return self.f\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Result() is self.selected())\n        return self.f\n",
            "frontend.python.heap.result-identity-expression-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Result() is self.f is self.f)\n        return self.f\n",
            "frontend.python.heap.result-identity-expression-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Expected:\n    pass\n\nclass Wrong:\n    pass\n\nclass Holder:\n    f: Expected\n    g: Wrong\n    def get(self) -> Wrong:\n        Requires(Acc(self.f))\n        Requires(Acc(self.g))\n        Ensures(Result() is self.f)\n        return self.g\n",
            "frontend.python.heap.result-identity-type-mismatch",
        ),
    ];

    for (_, (source, diagnostic)) in cases
        .into_iter()
        .enumerate()
        .filter(|(index, _)| *index != 2)
    {
        let response = verify_heap_program(source, &["Holder.get"]);
        assert_heap_refusal_without_any_proof(&response, diagnostic);
    }
}

#[test]
fn verifier_proves_an_optional_reference_return_from_a_nonoptional_field() {
    let response = verify_heap_program(
        "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    value: Leaf\n    def get(self) -> Optional[Leaf]:\n        Requires(Acc(self.value))\n        Ensures(Result() is self.value)\n        return self.value\n",
        &["Holder.get"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
}

#[test]
fn verifier_refuses_result_identity_in_constructor_or_exceptional_postcondition() {
    let constructor = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    def __init__(self, f: Leaf) -> None:\n        Ensures(Result() is self.f)\n        self.f = f\n",
        &["Holder.__init__"],
    );
    assert_heap_refusal_without_any_proof(&constructor, "invalid.program:invalid.result");

    let exceptional = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Failure(Exception):\n    pass\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Exsures(Failure, Result() is self.f)\n        return self.f\n",
        &["Holder.get"],
    );
    assert_heap_refusal_without_any_proof(
        &exceptional,
        "frontend.python.heap.result-identity-exception-postcondition-unsupported",
    );
}

#[test]
fn verifier_refuses_result_identity_in_external_contract_without_exporting_a_proof() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import Holder\n\ndef run(holder: Holder) -> Holder:\n    return holder.get()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass Holder:\n    f: Holder\n\n    @ContractOnly\n    def get(self) -> Holder:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(Result() is self.f)\n        ...\n",
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
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.result-identity-external-unsupported",
    );
}

#[test]
fn verifier_refuses_statements_after_every_supported_terminal_return() {
    let field_return = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    a: Leaf\n    b: Leaf\n    def get(self) -> Leaf:\n        Requires(Acc(self.a))\n        Requires(Acc(self.b))\n        Ensures(Result() is self.b)\n        return self.a\n        return self.b\n",
        &["Holder.get"],
    );
    assert_heap_refusal_without_any_proof(&field_return, "type.error:dead.code");

    let method_call_return = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    pass\n\nclass Holder:\n    f: Leaf\n    @Pure\n    def selected(self) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(Result() is self.f)\n        return self.f\n    def get(self) -> Leaf:\n        Requires(Acc(self.f))\n        Ensures(Acc(self.f))\n        Ensures(Result() is self.f)\n        return self.selected()\n        return self.f\n",
        &["Holder.selected", "Holder.get"],
    );
    assert_heap_refusal_without_any_proof(&method_call_return, "type.error:dead.code");
}

#[test]
fn verifier_does_not_hide_bound_source_dead_code_behind_symbol_selection() {
    let response = verify_heap_program(
        "def target() -> int:\n    return 1\n\ndef unselected() -> None:\n    raise Exception()\n    value = 1\n",
        &["target"],
    );

    assert_heap_refusal_without_any_proof(&response, "type.error:dead.code");
}

#[test]
fn verifier_late_binds_source_classes_for_calls_after_module_initialization() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    def __init__(self) -> None:\n        Ensures(Acc(self.c2) and isinstance(self.c2, Class2))\n        Ensures(Acc(self.c2.c1) and self.c2.c1 is self)\n        self.c2 = Class2(self)\n\nclass Class2:\n    def __init__(self, c1: Class1) -> None:\n        Ensures(Acc(self.c1) and self.c1 is c1)\n        self.c1 = c1\n\ndef run() -> None:\n    parent = Class1()\n    Assert(isinstance(parent.c2, Class2))\n    Assert(parent.c2.c1 is parent)\n",
        &["Class1.__init__", "Class2.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| {
                obligation.id.starts_with("run:assert:") && obligation.satisfied()
            })
            .count(),
        2,
        "{response:#?}"
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "Class1.__init__:postcondition:0" && obligation.satisfied()
    }));
}

#[test]
fn verifier_does_not_late_bind_a_class_for_an_earlier_module_initializer_call() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    def __init__(self) -> None:\n        Ensures(Acc(self.c2) and isinstance(self.c2, Class2))\n        self.c2 = Class2(self)\n\nClass1()\n\nclass Class2:\n    def __init__(self, c1: Class1) -> None:\n        Ensures(Acc(self.c1) and self.c1 is c1)\n        self.c1 = c1\n",
        &["Class1.__init__", "Class2.__init__"],
    );

    assert_heap_refusal_without_any_proof(&response, "frontend.python.heap.late-class-before-call");
}

#[test]
fn verifier_refuses_never_defined_or_lexically_shadowed_late_class_names() {
    let never_defined = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    c2: Class1\n    def stable(self) -> None:\n        Requires(Acc(self.c2))\n        Ensures(isinstance(self.c2, Missing))\n",
        &["Class1.stable"],
    );
    assert_heap_refusal_without_any_proof(
        &never_defined,
        "frontend.python.heap.late-class-unresolved",
    );

    let shadowed = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    c2: Class2\n    def stable(self, Class2: int) -> None:\n        Requires(Acc(self.c2))\n        Ensures(isinstance(self.c2, Class2))\n\nclass Class2:\n    pass\n",
        &["Class1.stable"],
    );
    assert_heap_refusal_without_any_proof(&shadowed, "frontend.python.heap.class-name-shadowed");
}

#[test]
fn verifier_composes_late_bound_class_identity_from_a_fully_initialized_provider() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    c2: Class2\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.c2) and isinstance(self.c2, Class2))\n        Ensures(Acc(self.c2.c1) and self.c2.c1 is self)\n        self.c2 = Class2(self)\n\nclass Class2:\n    c1: Class1\n\n    def __init__(self, c1: Class1) -> None:\n        Ensures(Acc(self.c1) and self.c1 is c1)\n        self.c1 = c1\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Class1, Class2\n\ndef run() -> None:\n    parent = Class1()\n    Assert(isinstance(parent.c2, Class2))\n    Assert(parent.c2.c1 is parent)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Class1.__init__".to_owned(), "Class2.__init__".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| {
                obligation.id.starts_with("run:assert:") && obligation.satisfied()
            })
            .count(),
        2,
        "{response:#?}"
    );
}

#[test]
fn verifier_imports_a_class_with_an_internal_completed_provider_dependency() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    c2: 'Class2'\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.c2))\n        Ensures(Acc(self.c2.c1) and self.c2.c1 is self)\n        self.c2 = Class2(self)\n\nclass Class2:\n    c1: Class1\n\n    def __init__(self, c1: Class1) -> None:\n        Ensures(Acc(self.c1) and self.c1 is c1)\n        self.c1 = c1\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Class1\n\ndef run() -> None:\n    parent = Class1()\n    Assert(parent.c2.c1 is parent)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Class1.__init__".to_owned(), "Class2.__init__".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert_eq!(
        response.source_imports[0].imported_symbols,
        ["Class1"],
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_preserves_canonical_class_identity_across_two_source_provider_edges() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("a.py"),
        "from nagini_contracts.contracts import *\n\nclass X:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        Ensures(self.marker == 1)\n        self.marker = 1\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("b.py"),
        "from nagini_contracts.contracts import *\nfrom a import X\n\nclass BHolder(X):\n    item: X\n    def __init__(self, item: X) -> None:\n        Requires(Acc(item.marker))\n        Ensures(Acc(self.marker))\n        Ensures(self.marker == 1)\n        Ensures(Acc(self.item))\n        Ensures(Acc(self.item.marker))\n        super().__init__()\n        self.item = item\n    def get(self) -> X:\n        Requires(Acc(self.item))\n        Ensures(Acc(self.item))\n        Ensures(Result() is self.item)\n        return self.item\n    def replace(self, value: X) -> X:\n        Requires(Acc(self.item))\n        Ensures(Acc(self.item))\n        Ensures(Result() is self.item)\n        self.item = value\n        return self.item\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("c.py"),
        "from nagini_contracts.contracts import *\nfrom b import BHolder\n\ndef run(holder: BHolder) -> None:\n    Requires(Acc(holder.item))\n    Requires(Acc(holder.item.marker))\n    observed = holder.get()\n    Assert(observed is holder.item)\n    Assert(observed.marker == holder.item.marker)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "a.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["X.__init__".to_owned()],
            },
            SourceFile {
                path: "b.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec![
                    "BHolder.__init__".to_owned(),
                    "BHolder.get".to_owned(),
                    "BHolder.replace".to_owned(),
                ],
            },
            SourceFile {
                path: "c.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
        response.files[2].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "b.py"
            && edge.provider_path == "a.py"
            && edge.imported_symbols == ["X"]
    }));
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "c.py"
            && edge.provider_path == "b.py"
            && edge.imported_symbols == ["BHolder"]
    }));
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| {
                obligation.id.starts_with("run:assert:") && obligation.satisfied()
            })
            .count(),
        2,
        "{response:#?}"
    );
}

#[test]
fn verifier_reexports_an_explicit_source_class_with_its_leaf_canonical_identity() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("a.py"),
        "from nagini_contracts.contracts import *\n\nclass X:\n    value: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == 1)\n        self.value = 1\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("b.py"),
        "from nagini_contracts.contracts import *\nfrom a import X as X\n\nclass BHolder:\n    item: X\n    def get(self) -> X:\n        Requires(Acc(self.item))\n        Ensures(Acc(self.item))\n        Ensures(Result() is self.item)\n        return self.item\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("c.py"),
        "from nagini_contracts.contracts import *\nfrom b import X\n\ndef run() -> None:\n    value = X()\n    Assert(value.value == 1)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "a.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["X.__init__".to_owned()],
            },
            SourceFile {
                path: "b.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["BHolder.get".to_owned()],
            },
            SourceFile {
                path: "c.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[2].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        }),
        "{response:#?}"
    );
}

#[test]
fn verifier_does_not_canonicalize_an_external_class_as_a_source_provider_class() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("b.py"),
        "from nagini_contracts.contracts import *\nfrom external_provider import X\n\nclass BHolder:\n    item: X\n    def __init__(self, item: X) -> None:\n        Ensures(Acc(self.item))\n        Ensures(isinstance(self.item, X))\n        self.item = item\n    def get(self) -> X:\n        Requires(Acc(self.item))\n        Ensures(Acc(self.item))\n        Ensures(Result() is self.item)\n        return self.item\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("c.py"),
        "from nagini_contracts.contracts import *\nfrom b import BHolder\n\ndef run(holder: BHolder) -> None:\n    Requires(Acc(holder.item))\n    observed = holder.get()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass X:\n    marker: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        ...\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "b.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["BHolder.__init__".to_owned(), "BHolder.get".to_owned()],
            },
            SourceFile {
                path: "c.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "b.py".to_owned(),
            module: "external_provider".to_owned(),
            stub_path: "external_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });

    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.late-class-external-unsupported",
    );
    assert_eq!(response.external_contracts.len(), 1, "{response:#?}");
    assert_eq!(
        response.external_contracts[0].module, "external_provider",
        "{response:#?}"
    );
    assert!(
        response
            .source_imports
            .iter()
            .all(|edge| { !edge.imported_symbols.iter().any(|symbol| symbol == "X") }),
        "{response:#?}"
    );
}

#[test]
fn verifier_does_not_reexport_an_external_runtime_class_as_source_owned_completion() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("source.py"),
        "from nagini_contracts.contracts import *\nfrom external_provider import External\n\nclass Source:\n    item: External\n    def __init__(self) -> None:\n        Ensures(Acc(self.item))\n        Ensures(Acc(self.item.marker))\n        self.item = External()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("consumer.py"),
        "from source import Source\n\ndef run() -> None:\n    item = Source()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass External:\n    marker: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        Ensures(self.marker == 1)\n        ...\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "source.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Source.__init__".to_owned()],
            },
            SourceFile {
                path: "consumer.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "source.py".to_owned(),
            module: "external_provider".to_owned(),
            stub_path: "external_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });

    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.late-class-external-unsupported",
    );
    assert_eq!(response.external_contracts.len(), 1, "{response:#?}");
    assert_eq!(
        response.external_contracts[0].module, "external_provider",
        "{response:#?}"
    );
}

#[test]
fn verifier_refuses_late_class_dependencies_in_property_getters_and_setters() {
    let getter = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Backing:\n    pass\n\nclass Holder:\n    f: Backing\n    @property\n    def selected(self) -> Backing:\n        Requires(Acc(self.f))\n        Ensures(isinstance(self.f, Later))\n        return self.f\n\nclass Later:\n    pass\n",
        &["Holder.selected"],
    );
    assert_heap_refusal_without_any_proof(
        &getter,
        "frontend.python.heap.late-class-property-unsupported",
    );

    let setter = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Backing:\n    pass\n\nclass Holder:\n    f: Backing\n    @property\n    def selected(self) -> Backing:\n        Requires(Acc(self.f))\n        return self.f\n    @selected.setter\n    def selected(self, value: Backing) -> None:\n        Requires(Acc(self.f))\n        Ensures(isinstance(self.f, Later))\n        self.f = value\n\nclass Later:\n    pass\n",
        &["Holder.selected"],
    );
    assert_heap_refusal_without_any_proof(
        &setter,
        "frontend.python.heap.late-class-property-unsupported",
    );
}

#[test]
fn verifier_keeps_base_decorator_and_class_body_names_eager() {
    let base = verify_heap_program(
        "class Derived(Later):\n    pass\n\nclass Later:\n    pass\n",
        &[],
    );
    assert!(matches!(base.status, ProofStatus::Refuted), "{base:#?}");
    assert!(base.obligations.iter().any(|obligation| {
        obligation.id == "module:undefined-base:Derived"
            && matches!(obligation.status, maledictus::vc::ObligationStatus::Refuted)
    }));

    let class_body = verify_heap_program(
        "class Holder:\n    selected = Later\n\nclass Later:\n    pass\n",
        &[],
    );
    assert!(
        matches!(class_body.status, ProofStatus::Refuted),
        "{class_body:#?}"
    );
    assert!(class_body.obligations.iter().any(|obligation| {
        obligation.id == "module:undefined-global:Holder"
            && matches!(obligation.status, maledictus::vc::ObligationStatus::Refuted)
    }));

    let decorator = verify_heap_program(
        "@Later\nclass Decorated:\n    value: int\n    def get(self) -> int:\n        return self.value\n\nclass Later:\n    pass\n",
        &["Decorated.get"],
    );
    assert_heap_refusal_without_any_proof(
        &decorator,
        "frontend.python.heap.class-shape-unsupported",
    );
}

#[test]
fn verifier_refuses_constructor_result_assigned_to_wrong_nominal_field() {
    let response = verify_heap_program(
        "class Expected:\n    pass\n\nclass Wrong:\n    pass\n\nclass Holder:\n    value: Expected\n\n    def __init__(self) -> None:\n        self.value = Wrong()\n\ndef run() -> None:\n    holder = Holder()\n",
        &["Holder.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.heap.constructor-field-nominal-mismatch"
        }),
        "{response:#?}"
    );
    assert!(response.files[0].fragment.is_none());
}

#[test]
fn verifier_refuses_recursive_nested_constructor_cycle() {
    let response = verify_heap_program(
        "class Left:\n    right: Right\n\n    def __init__(self) -> None:\n        self.right = Right()\n\nclass Right:\n    left: Left\n\n    def __init__(self) -> None:\n        self.left = Left()\n\ndef run() -> None:\n    value = Left()\n",
        &["Left.__init__", "Right.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.heap.constructor-field-cycle-unsupported"
        }),
        "{response:#?}"
    );
    assert!(response.files[0].fragment.is_none());
    assert!(
        !response
            .obligations
            .iter()
            .any(|obligation| { obligation.id.starts_with("run:") && obligation.satisfied() })
    );
}

#[test]
fn verifier_refuses_custom_new_before_assuming_constructor_freshness() {
    let response = verify_heap_program(
        "class Custom:\n    def __new__(cls) -> 'Custom':\n        return Custom()\n\nclass Holder:\n    item: Custom\n\n    def __init__(self) -> None:\n        self.item = Custom()\n\ndef run() -> None:\n    first = Holder()\n    second = Holder()\n    assert first.item is not second.item\n",
        &["Holder.__init__", "run"],
    );

    assert_heap_refusal_without_any_proof(&response, "invalid.program:illegal.magic.method");
}

#[test]
fn verifier_refuses_inherited_custom_new_before_assuming_constructor_freshness() {
    let response = verify_heap_program(
        "class Base:\n    def __new__(cls) -> 'Base':\n        return Base()\n\nclass Derived(Base):\n    pass\n\nclass Holder:\n    item: Derived\n\n    def __init__(self) -> None:\n        self.item = Derived()\n\ndef run() -> None:\n    first = Holder()\n    second = Holder()\n    assert first.item is not second.item\n",
        &["Holder.__init__", "run"],
    );

    assert_heap_refusal_without_any_proof(&response, "invalid.program:illegal.magic.method");
}

#[test]
fn verifier_refuses_inherited_constructor_exsures_before_assuming_freshness() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass ConstructionError(Exception):\n    pass\n\nclass Base:\n    def __init__(self) -> None:\n        Exsures(ConstructionError, True)\n\nclass Derived(Base):\n    pass\n\nclass Holder:\n    item: Derived\n\n    def __init__(self) -> None:\n        self.item = Derived()\n\ndef run() -> None:\n    first = Holder()\n    second = Holder()\n    Assert(first.item is not second.item)\n",
        &["Base.__init__", "Holder.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.heap.constructor-field-exceptional-unsupported"
        }),
        "{response:#?}"
    );
    assert!(response.files[0].fragment.is_none());
    assert!(
        !response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refuses_effective_super_constructor_recursion_before_assuming_freshness() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Base:\n    child: Derived\n\n    def __init__(self) -> None:\n        self.child = Derived()\n\nclass Derived(Base):\n    def __init__(self) -> None:\n        super().__init__()\n\nclass Holder:\n    item: Derived\n\n    def __init__(self) -> None:\n        self.item = Derived()\n\ndef run() -> None:\n    first = Holder()\n    second = Holder()\n    Assert(first.item is not second.item)\n",
        &[
            "Base.__init__",
            "Derived.__init__",
            "Holder.__init__",
            "run",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.heap.constructor-field-cycle-unsupported"
        }),
        "{response:#?}"
    );
    assert!(response.files[0].fragment.is_none());
    assert!(
        !response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refuses_external_base_allocator_before_assuming_subclass_freshness() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom external_provider import ExternalBase\n\nclass Derived(ExternalBase):\n    pass\n\nclass Holder:\n    item: Derived\n\n    def __init__(self) -> None:\n        self.item = Derived()\n\ndef run() -> None:\n    first = Holder()\n    second = Holder()\n    Assert(first.item is not second.item)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass ExternalBase:\n    marker: int\n\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        Ensures(self.marker == 0)\n        ...\n",
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
            symbols: vec!["Holder.__init__".to_owned(), "run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "external_provider".to_owned(),
            stub_path: "external_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code
                == "frontend.python.heap.constructor-field-external-allocator-unsupported"
        }),
        "{response:#?}"
    );
    assert!(response.files[0].fragment.is_none());
    assert!(
        !response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refuses_metaclass_construction_before_assuming_freshness() {
    let response = verify_heap_program(
        "class Meta:\n    pass\n\nclass Custom(metaclass=Meta):\n    pass\n\ndef run() -> None:\n    first = Custom()\n    second = Custom()\n    assert first is not second\n",
        &["run"],
    );

    assert_heap_refusal_without_any_proof(&response, "unsupported:Unsupported metaclass");
}

#[test]
fn failed_nested_constructor_does_not_export_a_fresh_field_result() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Expected:\n    pass\n\nclass Wrong:\n    pass\n\nclass Outer:\n    child: Expected\n\n    def __init__(self) -> None:\n        self.child = Wrong()\n\ndef run() -> None:\n    first = Outer()\n    second = Outer()\n    Assert(first.child is not second.child)\n",
        &["Outer.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.heap.constructor-field-nominal-mismatch"
        }),
        "{response:#?}"
    );
    assert!(response.files[0].fragment.is_none());
    assert!(
        !response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_proves_class_qualified_and_inherited_static_calls() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\n\nclass Base:\n    @staticmethod\n    def increment(value: int) -> int:\n        Ensures(Result() == value + 1)\n        return value + 1\n\nclass Derived(Base):\n    pass\n\ndef main() -> None:\n    direct = Base.increment(4)\n    inherited = Derived.increment(direct)\n    Assert(inherited == 6)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["Base.increment".to_owned(), "main".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.diagnostics.is_empty());
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "main:heap-function-complete" && obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_dynamic_classmethod_construction_and_dispatch() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\n\nclass Base:\n    @classmethod\n    def construct(cls) -> 'Base':\n        Ensures(type(Result()) is cls)\n        return cls()\n\nclass Derived(Base):\n    pass\n\ndef main() -> None:\n    value = Derived.construct()\n    Assert(isinstance(value, Derived))\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["Base.construct".to_owned(), "main".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.diagnostics.is_empty());
}

#[test]
fn verifier_proves_predicate_fold_unfold_and_framed_state() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def __init__(self) -> None:\n        Ensures(self.state())\n        self.value = 1\n        Fold(self.state())\n\n    @Predicate\n    def state(self) -> bool:\n        return Acc(self.value) and self.value == 1\n\ndef main() -> None:\n    cell = Cell()\n    Unfold(cell.state())\n    cell.value = 2\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["Cell.__init__".to_owned(), "main".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.diagnostics.is_empty());
}

#[test]
fn verifier_matches_upstream_predicate_fixture_exactly() {
    let source =
        include_str!("../.upstream/nagini/tests/functional/verification/test_predicate.py");
    let response = verify_predicate_program(source);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );

    let refuted = response
        .obligations
        .iter()
        .filter(|obligation| !obligation.satisfied())
        .collect::<Vec<_>>();
    assert_eq!(refuted.len(), 5, "{:#?}", response.obligations);
    for (line, id_fragment) in [
        (38, ":field-permission:"),
        (51, ":predicate-fold-body:"),
        (60, ":postcondition:"),
        (69, ":predicate-unfolding-permission:"),
        (79, ":predicate-unfold-permission-not-positive:"),
    ] {
        assert!(
            refuted.iter().any(|obligation| {
                obligation.line == line && obligation.id.contains(id_fragment)
            }),
            "missing upstream diagnostic category {id_fragment:?} at line {line}: {refuted:#?}"
        );
    }
}

#[test]
fn module_predicate_rejects_a_wrong_nominal_argument() {
    let response = verify_predicate_program(
        "from nagini_contracts.contracts import *\n\nclass Expected:\n    value: int\n\nclass Other:\n    value: int\n\n@Predicate\ndef state(item: Expected) -> bool:\n    return Acc(item.value)\n\ndef main(other: Other) -> None:\n    Fold(state(other))\n",
    );
    assert!(matches!(response.status, ProofStatus::Refused));
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.heap.module-predicate-call-nominal-mismatch"
        }),
        "{response:#?}"
    );
}

#[test]
fn module_predicate_rejects_zero_and_invalid_body_fractions() {
    let zero = verify_predicate_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n@Predicate\ndef state(cell: Cell) -> bool:\n    return Acc(cell.value, 0/1)\n",
    );
    assert!(matches!(zero.status, ProofStatus::Refused));
    assert!(
        zero.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.heap.module-predicate-permission-not-positive"
        }),
        "{zero:#?}"
    );

    let invalid = verify_predicate_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n@Predicate\ndef state(cell: Cell) -> bool:\n    return Acc(cell.value, 2/1)\n",
    );
    assert!(matches!(invalid.status, ProofStatus::Refused));
    assert!(
        invalid.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.heap.permission-fraction-invalid"
        }),
        "{invalid:#?}"
    );
}

#[test]
fn wrong_predicate_arguments_cannot_unfold_an_existing_token() {
    let response = verify_predicate_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == 1)\n        self.value = 1\n\n@Predicate\ndef state(cell: Cell, expected: int) -> bool:\n    return Acc(cell.value) and cell.value == expected\n\ndef main() -> None:\n    cell = Cell()\n    Fold(state(cell, 1))\n    Unfold(state(cell, 2))\n",
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    let refuted = response
        .obligations
        .iter()
        .filter(|obligation| !obligation.satisfied())
        .collect::<Vec<_>>();
    assert_eq!(refuted.len(), 1, "{:#?}", response.obligations);
    assert!(
        refuted[0]
            .id
            .contains(":predicate-unfold-permission:state:"),
        "{refuted:#?}"
    );
}

#[test]
fn duplicate_full_predicate_fold_is_rejected() {
    let response = verify_predicate_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == 1)\n        self.value = 1\n\n@Predicate\ndef state(cell: Cell) -> bool:\n    return Acc(cell.value) and cell.value == 1\n\ndef main() -> None:\n    cell = Cell()\n    Fold(state(cell))\n    Fold(state(cell))\n",
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    let refuted = response
        .obligations
        .iter()
        .filter(|obligation| !obligation.satisfied())
        .collect::<Vec<_>>();
    assert!(!refuted.is_empty(), "{:#?}", response.obligations);
    assert!(
        refuted.iter().all(|obligation| obligation.line == 18),
        "duplicate-fold failures escaped the second Fold statement: {refuted:#?}"
    );
    assert!(
        refuted
            .iter()
            .any(|obligation| obligation.id.contains(":predicate-fold-body:state:")),
        "{refuted:#?}"
    );
}

#[test]
fn fractional_predicate_fold_preserves_the_ambient_complement() {
    let response = verify_predicate_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == 1)\n        self.value = 1\n\n@Predicate\ndef half_state(cell: Cell) -> bool:\n    return Acc(cell.value, 1/2) and cell.value == 1\n\ndef main() -> None:\n    cell = Cell()\n    Fold(half_state(cell))\n    Assert(cell.value == 1)\n    Unfold(half_state(cell))\n    cell.value = 2\n",
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn unfolding_refolds_and_preserves_ambient_fractional_state() {
    let response = verify_predicate_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == 1)\n        self.value = 1\n\n@Predicate\ndef half_state(cell: Cell) -> bool:\n    return Acc(cell.value, 1/2) and cell.value == 1\n\ndef read() -> int:\n    Ensures(Result() == 1)\n    cell = Cell()\n    Fold(half_state(cell))\n    Assert(cell.value == 1)\n    return Unfolding(half_state(cell), cell.value)\n",
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation
                .id
                .contains(":predicate-unfolding-permission:half_state:")
                && obligation.satisfied()
        }),
        "{:#?}",
        response.obligations
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.contains(":predicate-fold-result:half_state:") && obligation.satisfied()
        }),
        "{:#?}",
        response.obligations
    );
}

#[test]
fn verifier_matches_nominal_reference_identity_and_call_preconditions() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("references.py"),
        "from nagini_contracts.contracts import Assert\nfrom typing import Optional\n\nclass B:\n    pass\n\nclass C:\n    pass\n\ndef maybe(b: Optional[B], c: Optional[C]) -> None:\n    Assert(b is not c)\n\ndef distinct(b: B, c: C) -> None:\n    Assert(b is not c)\n\ndef caller() -> None:\n    maybe(None, None)\n    distinct(None, None)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "references.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec![],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = analyze_frontend_request(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("nominal-reference-contracts/v4")
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "call.precondition:assertion.false" })
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "assert.failed:assertion.false" })
    );
}

#[test]
fn verifier_refutes_heap_read_without_permission() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("cell.py"),
        "class Cell:\n    value: int\n\n    def get(self) -> int:\n        return self.value\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "cell.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["Cell.get".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.diagnostics[0].code,
        "field.read:insufficient.permission"
    );
}

#[test]
fn verifier_refutes_heap_write_without_permission() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("cell.py"),
        "class Cell:\n    value: int\n\n    def set(self, value: int) -> None:\n        self.value = value\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "cell.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["Cell.set".to_owned()],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert_eq!(
        response.diagnostics[0].code,
        "field.write:insufficient.permission"
    );
}

#[test]
fn verifier_reports_missing_method_call_permission() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("cell.py"),
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n\n    def get(self) -> int:\n        Requires(Acc(self.value, 1/2))\n        Ensures(Acc(self.value, 1/2))\n        return self.value\n\n    def invalid(self) -> int:\n        return self.get()\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "cell.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert!(
        response
            .diagnostics
            .iter()
            .any(|item| item.code == "call.precondition:insufficient.permission")
    );
}

#[test]
fn verifier_composes_transitive_source_module_contracts() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("leaf.py"),
        "from nagini_contracts.contracts import *\n\nOFFSET = 1\n\ndef increment(value: int) -> int:\n    Requires(value > 0)\n    Ensures(int, lambda returned: returned == value + OFFSET)\n    return value + OFFSET\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("middle.py"),
        "from leaf import increment\nfrom nagini_contracts.contracts import *\n\ndef add_two(value: int) -> int:\n    Requires(value > 0)\n    Ensures(int, lambda returned: returned == value + 2)\n    first = increment(value)\n    return increment(first)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from middle import add_two\nfrom nagini_contracts.contracts import *\n\nOFFSET = 100\n\ndef run() -> int:\n    Ensures(Result() == 3)\n    return add_two(1)\n",
    )
    .unwrap();
    let request = ProofRequest {
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
                path: "middle.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["add_two".to_owned()],
            },
            SourceFile {
                path: "leaf.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["increment".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert!(response.diagnostics.is_empty());
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("transitive-source-scalar-contracts/v33")
    );
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-scalar-contracts/v33")
    );
    assert_eq!(
        response.files[2].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert_eq!(response.source_imports.len(), 2);
    assert_eq!(response.source_imports[0].importer_path, "app.py");
    assert_eq!(response.source_imports[0].provider_path, "middle.py");
    assert_eq!(response.source_imports[0].imported_symbols, ["add_two"]);
    assert_eq!(response.source_imports[1].importer_path, "middle.py");
    assert_eq!(response.source_imports[1].provider_path, "leaf.py");
    assert_eq!(response.source_imports[1].imported_symbols, ["increment"]);
    assert!(
        response
            .source_imports
            .iter()
            .all(|edge| edge.provider_sha256.len() == 64)
    );
}

#[test]
fn verifier_composes_typed_tuples_across_source_module_edges() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("pairs.py"),
        "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef pair(number: int, text: str) -> Tuple[int, str]:\n    Ensures(Result()[0] == number)\n    Ensures(Result()[1] == text)\n    return number, text\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from pairs import pair\nfrom nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef run() -> Tuple[int, str]:\n    Ensures(Result()[0] == 4)\n    Ensures(Result()[1] == 'value')\n    return pair(4, 'value')\n",
    )
    .unwrap();
    let request = ProofRequest {
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
                path: "pairs.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["pair".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert!(response.diagnostics.is_empty());
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("transitive-source-scalar-contracts/v33")
    );
    assert_eq!(response.source_imports.len(), 1);
}

#[test]
fn verifier_composes_variadic_tuples_across_source_module_edges() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("tuples.py"),
        "from nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef preserve(values: Tuple[int, ...]) -> Tuple[int, ...]:\n    Ensures(len(Result()) == len(values))\n    return values\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from tuples import preserve\nfrom nagini_contracts.contracts import *\nfrom typing import Tuple\n\ndef run() -> Tuple[int, ...]:\n    Ensures(len(Result()) == 3)\n    return preserve((1, 2, 3))\n",
    )
    .unwrap();
    let request = ProofRequest {
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
                path: "tuples.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["preserve".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty());
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("transitive-source-scalar-contracts/v33")
    );
    assert_eq!(response.source_imports.len(), 1);
}

#[test]
fn verifier_composes_typed_lists_across_source_module_edges() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("values.py"),
        "from nagini_contracts.contracts import *\nfrom typing import List\n\ndef pair() -> List[int]:\n    Ensures(len(Result()) == 2)\n    return [4, 7]\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from values import pair\nfrom nagini_contracts.contracts import *\nfrom typing import List\n\ndef run() -> List[int]:\n    Ensures(len(Result()) == 2)\n    return pair()\n",
    )
    .unwrap();
    let request = ProofRequest {
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
                path: "values.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["pair".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Proved));
    assert!(response.diagnostics.is_empty());
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("transitive-source-scalar-contracts/v33")
    );
    assert_eq!(response.source_imports.len(), 1);
}

#[test]
fn refuted_source_dependency_cannot_supply_a_caller_contract() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("broken.py"),
        "from nagini_contracts.contracts import *\n\ndef increment(value: int) -> int:\n    Ensures(Result() == value + 1)\n    return value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from broken import increment\n\ndef run() -> int:\n    return increment(1)\n",
    )
    .unwrap();
    let request = ProofRequest {
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
                path: "broken.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["increment".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refuted));
    assert!(matches!(response.files[0].result, ProofStatus::Refused));
    assert!(matches!(response.files[1].result, ProofStatus::Refuted));
    assert!(
        response
            .diagnostics
            .iter()
            .any(|item| { item.code == "frontend.python.contract-import.source-module-refuted" }),
        "{response:#?}"
    );
}

#[test]
fn source_contract_import_cycle_refuses_instead_of_assuming_summaries() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("first.py"),
        "from second import second\n\ndef first(value: int) -> int:\n    return second(value)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("second.py"),
        "from first import first\n\ndef second(value: int) -> int:\n    return first(value)\n",
    )
    .unwrap();
    let request = ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "first.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["first".to_owned()],
            },
            SourceFile {
                path: "second.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["second".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    };

    let response = maledictus::verify(&request);
    assert!(matches!(response.status, ProofStatus::Refused));
    assert!(
        response
            .diagnostics
            .iter()
            .all(|item| item.code == "frontend.python.contract-import.cycle"),
        "{response:#?}"
    );
}

#[test]
fn verifier_proves_left_to_right_nominal_reference_call_and_field_chains() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    def __init__(self) -> None:\n        Ensures(Acc(self.c2) and isinstance(self.c2, Class2))\n        Ensures(Acc(self.c2.c1) and self.c2.c1 is self)\n        self.c2 = Class2(self)\n    @Pure\n    def get_c2(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        return self.c2\n    def get_c2_impure(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        Ensures(Acc(self.c2))\n        Ensures(self.c2 is Old(self.c2))\n        Ensures(Result() is self.c2)\n        return self.c2\n\nclass Class2:\n    def __init__(self, c1: Class1) -> None:\n        Ensures(Acc(self.c1) and self.c1 is c1)\n        self.c1 = c1\n    @Pure\n    def get_c1(self) -> Class1:\n        Requires(Acc(self.c1))\n        return self.c1\n    def get_c1_impure(self) -> Class1:\n        Requires(Acc(self.c1))\n        Ensures(Acc(self.c1))\n        Ensures(self.c1 is Old(self.c1))\n        Ensures(Result() is self.c1)\n        return self.c1\n\ndef run() -> None:\n    c1 = Class1()\n    c2 = c1.get_c2().c1.get_c2().get_c1_impure().c2.get_c1().get_c2_impure().get_c1().c2.get_c1_impure().c2\n    Assert(c1 is c2.c1)\n",
        &[
            "Class1.__init__",
            "Class1.get_c2",
            "Class1.get_c2_impure",
            "Class2.__init__",
            "Class2.get_c1",
            "Class2.get_c1_impure",
            "run",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(
        response
            .files
            .iter()
            .all(|file| matches!(file.result, ProofStatus::Proved)),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| {
                obligation.id.starts_with("run:method-call-precondition:") && obligation.satisfied()
            })
            .count(),
        7,
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refutes_a_reference_chain_without_intermediate_field_permission() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    parent: Leaf\n\nclass Holder:\n    leaf: Leaf\n    @Pure\n    def get_leaf(self) -> Leaf:\n        Requires(Acc(self.leaf))\n        return self.leaf\n\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.leaf))\n    observed = holder.get_leaf().parent\n",
        &["Holder.get_leaf", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("run:reference-chain-field-permission:parent:")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_refuses_optional_or_dynamic_reference_chain_hops_without_proof() {
    let optional = verify_heap_program(
        "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Leaf:\n    next: Leaf\n\nclass Holder:\n    leaf: Optional[Leaf]\n\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.leaf))\n    observed = holder.leaf.next\n",
        &["run"],
    );
    assert_heap_refusal_without_any_proof(
        &optional,
        "frontend.python.heap.reference-chain-optional-unsupported",
    );

    let wrong_nominal_member = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Terminal:\n    pass\n\nclass Expected:\n    next: Terminal\n    @Pure\n    def advance(self) -> Terminal:\n        Requires(Acc(self.next))\n        return self.next\n\nclass Wrong:\n    pass\n\nclass Holder:\n    wrong: Wrong\n    @Pure\n    def get_wrong(self) -> Wrong:\n        Requires(Acc(self.wrong))\n        return self.wrong\n\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.wrong))\n    observed = holder.get_wrong().advance()\n",
        &["Expected.advance", "Holder.get_wrong", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &wrong_nominal_member,
        "frontend.python.heap.reference-chain-member-unresolved",
    );

    let dynamic_receiver = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    next: Leaf\n\nclass Holder:\n    left: Leaf\n    right: Leaf\n\ndef run(holder: Holder, choose_left: bool) -> None:\n    Requires(Acc(holder.left))\n    Requires(Acc(holder.right))\n    observed = (holder.left if choose_left else holder.right).next\n",
        &["run"],
    );
    assert_heap_refusal_without_any_proof(
        &dynamic_receiver,
        "frontend.python.heap.conditional-expression-reads-unsupported",
    );
}

#[test]
fn verifier_refuses_property_reference_chain_hops_without_proof() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    next: Leaf\n\nclass Holder:\n    leaf: Leaf\n    @property\n    def selected(self) -> Leaf:\n        Requires(Acc(self.leaf))\n        return self.leaf\n\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.leaf))\n    observed = holder.selected.next\n",
        &["Holder.selected", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.reference-chain-property-unsupported",
    );
}

#[test]
fn verifier_refuses_reference_chain_calls_without_proved_result_provenance() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Leaf:\n    next: Leaf\n\nclass Holder:\n    leaf: Leaf\n    def get_leaf(self) -> Leaf:\n        Requires(Acc(self.leaf))\n        Ensures(Acc(self.leaf))\n        return self.leaf\n\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.leaf))\n    Requires(Acc(holder.leaf.next))\n    observed = holder.get_leaf().next\n",
        &["Holder.get_leaf", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.reference-chain-result-provenance-unsupported",
    );
}

#[test]
fn verifier_uses_the_post_call_heap_for_an_impure_reference_chain_hop() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Node:\n    parent: Node\n\nclass Holder:\n    current: Node\n    replacement: Node\n    @Pure\n    def current_node(self) -> Node:\n        Requires(Acc(self.current))\n        return self.current\n    def advance(self) -> Node:\n        Requires(Acc(self.current))\n        Requires(Acc(self.replacement))\n        Ensures(Acc(self.current))\n        Ensures(Acc(self.replacement))\n        Ensures(self.current is self.replacement)\n        Ensures(Result() is self.current)\n        self.current = self.replacement\n        return self.current\n\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.current))\n    Requires(Acc(holder.replacement))\n    Requires(Acc(holder.current.parent))\n    Requires(Acc(holder.replacement.parent))\n    Requires(holder.current.parent is not holder.replacement.parent)\n    before_parent = holder.current_node().parent\n    after_parent = holder.advance().parent\n    Assert(after_parent is holder.replacement.parent)\n    Assert(after_parent is before_parent)\n",
        &["Holder.current_node", "Holder.advance", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("run:assert:")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_refuses_external_reference_chain_hops_without_proof() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import External\n\ndef run(item: External) -> None:\n    Requires(Acc(item.next))\n    observed = item.next.next\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass External:\n    next: External\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.next))\n        ...\n",
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
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });

    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.reference-chain-external-unsupported",
    );

    for (source, symbols) in [
        (
            "from nagini_contracts.contracts import *\nfrom external_provider import ExternalBase\n\nclass Derived(ExternalBase):\n    pass\n\ndef run(item: Derived) -> None:\n    Requires(Acc(item.next))\n    observed = item.next.next\n",
            vec!["run".to_owned()],
        ),
        (
            "from nagini_contracts.contracts import *\nfrom external_provider import ExternalBase\n\nclass Derived(ExternalBase):\n    @Pure\n    def get_next(self) -> ExternalBase:\n        Requires(Acc(self.next))\n        return self.next\n\ndef run(item: Derived) -> None:\n    Requires(Acc(item.next))\n    observed = item.get_next().next\n",
            vec!["Derived.get_next".to_owned(), "run".to_owned()],
        ),
    ] {
        let directory = tempfile::tempdir().unwrap();
        fs::write(directory.path().join("app.py"), source).unwrap();
        fs::write(
            directory.path().join("external_contract.py"),
            "from nagini_contracts.contracts import *\n\nclass ExternalBase:\n    next: ExternalBase\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.next))\n        ...\n",
        )
        .unwrap();
        let inherited = maledictus::verify(&ProofRequest {
            schema: PROTOCOL_SCHEMA.to_owned(),
            source_root: directory.path().display().to_string(),
            source_fingerprint: "0".repeat(64),
            proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
            files: vec![SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols,
            }],
            python_callable_bindings: Vec::new(),
            cross_language_bindings: Vec::new(),
            external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
                adapter_path: "app.py".to_owned(),
                module: "external_provider".to_owned(),
                stub_path: "external_contract.py".to_owned(),
                exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
            }],
        });
        assert_heap_refusal_without_any_proof(
            &inherited,
            "frontend.python.heap.reference-chain-external-unsupported",
        );
    }
}

#[test]
fn verifier_proves_exact_upstream_line59_reference_equality() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    def __init__(self) -> None:\n        Ensures(Acc(self.c2) and isinstance(self.c2, Class2))\n        Ensures(Acc(self.c2.c1) and self.c2.c1 is self)\n        self.c2 = Class2(self)\n    @Pure\n    def get_c2(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        return self.c2\n    def get_c2_impure(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        Ensures(Acc(self.c2))\n        Ensures(self.c2 is Old(self.c2))\n        Ensures(Result() is self.c2)\n        return self.c2\n\nclass Class2:\n    def __init__(self, c1: Class1) -> None:\n        Ensures(Acc(self.c1) and self.c1 is c1)\n        self.c1 = c1\n    @Pure\n    def get_c1(self) -> Class1:\n        Requires(Acc(self.c1))\n        return self.c1\n    def get_c1_impure(self) -> Class1:\n        Requires(Acc(self.c1))\n        Ensures(Acc(self.c1))\n        Ensures(self.c1 is Old(self.c1))\n        Ensures(Result() is self.c1)\n        return self.c1\n\ndef run() -> None:\n    c1 = Class1()\n    c2 = c1.get_c2().c1.get_c2().get_c1_impure().c2.get_c1().get_c2_impure().get_c1().c2.get_c1_impure().c2\n    Assert(c1 == c2.c1)\n",
        &[
            "Class1.__init__",
            "Class1.get_c2",
            "Class1.get_c2_impure",
            "Class2.__init__",
            "Class2.get_c1",
            "Class2.get_c1_impure",
            "run",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| {
                obligation.id.starts_with("run:assert:")
                    && obligation.status == maledictus::vc::ObligationStatus::Proved
            })
            .count(),
        1,
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn verifier_refutes_exact_upstream_line61_reference_equality() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    def __init__(self) -> None:\n        Ensures(Acc(self.c2) and isinstance(self.c2, Class2))\n        Ensures(Acc(self.c2.c1) and self.c2.c1 is self)\n        self.c2 = Class2(self)\n    @Pure\n    def get_c2(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        return self.c2\n    def get_c2_impure(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        Ensures(Acc(self.c2))\n        Ensures(self.c2 is Old(self.c2))\n        Ensures(Result() is self.c2)\n        return self.c2\n\nclass Class2:\n    def __init__(self, c1: Class1) -> None:\n        Ensures(Acc(self.c1) and self.c1 is c1)\n        self.c1 = c1\n    @Pure\n    def get_c1(self) -> Class1:\n        Requires(Acc(self.c1))\n        return self.c1\n    def get_c1_impure(self) -> Class1:\n        Requires(Acc(self.c1))\n        Ensures(Acc(self.c1))\n        Ensures(self.c1 is Old(self.c1))\n        Ensures(Result() is self.c1)\n        return self.c1\n\ndef run() -> None:\n    c1 = Class1()\n    c2 = c1.get_c2().c1.get_c2().get_c1_impure().c2.get_c1().get_c2_impure().get_c1().c2.get_c1_impure().c2\n    Assert(c1 == c2)\n",
        &[
            "Class1.__init__",
            "Class1.get_c2",
            "Class1.get_c2_impure",
            "Class2.__init__",
            "Class2.get_c1",
            "Class2.get_c1_impure",
            "run",
        ],
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|item| item.code == "assert.failed:assertion.false")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("run:assert:")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_refutes_distinct_exact_same_class_allocations() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\ndef run() -> None:\n    left = Item()\n    right = Item()\n    Assert(left == right)\n",
        &["Item.__init__", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|item| item.code == "assert.failed:assertion.false")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("run:assert:")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_refuses_custom_or_inherited_reference_equality_dispatch_without_proof() {
    let custom = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n    @Pure\n    def __eq__(self, marker: int) -> bool:\n        return False\n\ndef run() -> None:\n    left = Item()\n    right = Item()\n    Assert(left == right)\n",
        &["Item.__init__", "Item.__eq__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &custom,
        "frontend.python.heap.assert-reference-equality-mro-unsupported",
    );

    let inherited = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n    @Pure\n    def __eq__(self, marker: int) -> bool:\n        return False\n\nclass Derived(Base):\n    pass\n\ndef run() -> None:\n    left = Derived()\n    right = Derived()\n    Assert(left == right)\n",
        &["Base.__init__", "Base.__eq__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &inherited,
        "frontend.python.heap.assert-reference-equality-mro-unsupported",
    );
}

#[test]
fn verifier_refuses_starred_class_binding_of_reference_equality_dispatch() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n    *__eq__, = [None]\n\ndef run() -> None:\n    left = Item()\n    right = Item()\n    Assert(left == right)\n",
        &["Item.__init__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.class-constant-target-unsupported",
    );
}

#[test]
fn verifier_refuses_external_dynamic_or_nonexact_reference_equality_left_operands() {
    let nonexact = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\ndef run(left: Item, right: Item) -> None:\n    Requires(Acc(left.marker))\n    Requires(Acc(right.marker))\n    Assert(left == right)\n",
        &["run"],
    );
    assert_heap_refusal_without_any_proof(
        &nonexact,
        "frontend.python.heap.assert-reference-equality-left-unsupported",
    );

    let dynamic = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\ndef run(flag: bool) -> None:\n    first = Item()\n    second = Item()\n    Assert((first if flag else second) == first)\n",
        &["Item.__init__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &dynamic,
        "frontend.python.heap.assert-reference-equality-raw-left-unsupported",
    );

    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import External\n\nclass Anchor:\n    marker: int\n\ndef run(left: External, right: External) -> None:\n    Assert(left == right)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass External:\n    marker: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        ...\n",
    )
    .unwrap();
    let external = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert_heap_refusal_without_any_proof(
        &external,
        "frontend.python.heap.assert-reference-equality-left-unsupported",
    );
}

#[test]
fn verifier_refuses_reference_equality_with_an_external_right_mro() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import ExternalBase\n\nclass Clean:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Derived(ExternalBase):\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\ndef run() -> None:\n    left = Clean()\n    right = Derived()\n    Assert(left == right)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass ExternalBase:\n    marker: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        ...\n",
    )
    .unwrap();
    let response = analyze_frontend_request(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec![
                "Clean.__init__".to_owned(),
                "Derived.__init__".to_owned(),
                "run".to_owned(),
            ],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.assert-reference-equality-right-unsupported",
    );
}

#[test]
fn verifier_refuses_negated_contract_or_assignment_reference_equality_contexts() {
    let not_equal = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\ndef run() -> None:\n    left = Item()\n    right = Item()\n    Assert(left != right)\n",
        &["Item.__init__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &not_equal,
        "frontend.python.heap.reference-equality-unsupported",
    );

    let explicit_not = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\ndef run() -> None:\n    left = Item()\n    right = Item()\n    Assert(not (left == right))\n",
        &["Item.__init__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &explicit_not,
        "frontend.python.heap.reference-equality-unsupported",
    );

    for source in [
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\ndef run(left: Item, right: Item) -> None:\n    Requires(Acc(left.marker))\n    Requires(left == right)\n",
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\ndef run(left: Item, right: Item) -> None:\n    Requires(Acc(left.marker))\n    Ensures(left == right)\n",
    ] {
        let contract = verify_heap_program(source, &["run"]);
        assert_heap_refusal_without_any_proof(
            &contract,
            "frontend.python.heap.reference-equality-unsupported",
        );
    }

    for (source, diagnostic) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\ndef run() -> None:\n    left = Item()\n    right = Item()\n    same = left == right\n    Assert(same)\n",
            "frontend.python.heap.reference-equality-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\ndef run() -> None:\n    left = Item()\n    right = Item()\n    Assert((same := left == right))\n",
            "frontend.python.heap.expression-unsupported",
        ),
    ] {
        let assignment = verify_heap_program(source, &["run"]);
        assert_heap_refusal_without_any_proof(&assignment, diagnostic);
    }
}

#[test]
fn verifier_refuses_reverse_dispatch_sensitive_reference_equality() {
    for (source, symbols, diagnostic) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Derived(Base):\n    @Pure\n    def __eq__(self, marker: int) -> bool:\n        return False\n\ndef run() -> None:\n    left = Base()\n    right = Derived()\n    Assert(left == right)\n",
            vec!["Base.__init__", "Derived.__eq__", "run"],
            "frontend.python.heap.assert-reference-equality-mro-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass EqualityBase(Base):\n    @Pure\n    def __eq__(self, marker: int) -> bool:\n        return False\n\nclass Derived(EqualityBase):\n    pass\n\ndef run() -> None:\n    left = Base()\n    right = Derived()\n    Assert(left == right)\n",
            vec!["Base.__init__", "EqualityBase.__eq__", "run"],
            "frontend.python.heap.assert-reference-equality-mro-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Derived(Base):\n    @Pure\n    def compare(self, marker: int) -> bool:\n        return False\n    __eq__ = compare\n\ndef run() -> None:\n    left = Base()\n    right = Derived()\n    Assert(left == right)\n",
            vec!["Base.__init__", "Derived.compare", "run"],
            "frontend.python.heap.expression-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Derived(Base):\n    async def __eq__(self, marker: int) -> bool:\n        return False\n\ndef run() -> None:\n    left = Base()\n    right = Derived()\n    Assert(left == right)\n",
            vec!["Base.__init__", "Derived.__eq__", "run"],
            "frontend.python.heap.class-statement-unsupported",
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_any_proof(&response, diagnostic);
    }
}

#[test]
fn verifier_proves_a_permission_checked_property_as_a_method_argument() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\nclass Target:\n    current: Item\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\nclass Holder:\n    selected: Item\n    @property\n    def current(self) -> Item:\n        Requires(Acc(self.selected))\n        return self.selected\n\ndef run(target: Target, holder: Holder) -> None:\n    Requires(Acc(target.current))\n    Requires(Acc(holder.selected))\n    target.set_current(holder.current)\n",
        &["Target.set_current", "Holder.current@property", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(response.obligations.iter().any(|item| {
        item.id
            .contains("run:property-precondition:current:selected")
            && item.satisfied()
    }));
}

#[test]
fn verifier_refuses_an_impure_method_call_as_reference_equality_right_operand() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass ItemBase:\n    pass\n\nclass Item(ItemBase):\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n    def choose(self) -> ItemBase:\n        Requires(Acc(self.marker))\n        Ensures(Acc(self.marker))\n        self.marker = 1\n        return self\n\ndef run() -> None:\n    left = Item()\n    right = Item()\n    Assert(left == right.choose())\n",
        &["Item.__init__", "Item.choose", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.assert-reference-equality-right-unsupported",
    );
}

#[test]
fn verifier_refuses_property_or_optional_reference_equality_right_operands() {
    let property = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Owner:\n    selected: Item\n    def __init__(self, selected: Item) -> None:\n        Ensures(Acc(self.selected))\n        Ensures(self.selected is selected)\n        self.selected = selected\n    @property\n    def current(self) -> Item:\n        Requires(Acc(self.selected))\n        return self.selected\n\ndef run() -> None:\n    left = Item()\n    owner = Owner(left)\n    Assert(left == owner.current)\n",
        &[
            "Item.__init__",
            "Owner.__init__",
            "Owner.current@property",
            "run",
        ],
    );
    assert_heap_refusal_without_any_proof(
        &property,
        "frontend.python.heap.assert-reference-equality-right-unsupported",
    );

    let optional = verify_heap_program(
        "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Owner:\n    selected: Optional[Item]\n\ndef run(owner: Owner) -> None:\n    Requires(Acc(owner.selected))\n    left = Item()\n    Assert(left == owner.selected)\n",
        &["Item.__init__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &optional,
        "frontend.python.heap.assert-reference-equality-right-unsupported",
    );
}

#[test]
fn verifier_refuses_a_nonexact_base_typed_reference_equality_right_operand() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Derived(Base):\n    @Pure\n    def __eq__(self, marker: int) -> bool:\n        return False\n\ndef run(right: Base) -> None:\n    Requires(Acc(right.marker))\n    left = Base()\n    Assert(left == right)\n",
        &["Base.__init__", "Derived.__eq__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.assert-reference-equality-right-unsupported",
    );

    let field = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Owner:\n    selected: Item\n\ndef run(owner: Owner) -> None:\n    Requires(Acc(owner.selected))\n    left = Item()\n    Assert(left == owner.selected)\n",
        &["Item.__init__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &field,
        "frontend.python.heap.assert-reference-equality-right-unsupported",
    );
}

#[test]
fn verifier_refuses_raw_field_reference_equality_through_custom_attribute_dispatch() {
    for (source, hook) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Owner:\n    child: Item\n    def __init__(self, child: Item) -> None:\n        Ensures(Acc(self.child))\n        Ensures(self.child is child)\n        self.child = child\n    @Pure\n    def __getattribute__(self, marker: int) -> int:\n        return marker\n\ndef run() -> None:\n    left = Item()\n    owner = Owner(left)\n    Assert(left == owner.child)\n",
            "Owner.__getattribute__",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Owner:\n    child: Item\n    def __init__(self, child: Item) -> None:\n        Ensures(Acc(self.child))\n        Ensures(self.child is child)\n        self.child = child\n    @Pure\n    def __getattr__(self, marker: int) -> int:\n        return marker\n\ndef run() -> None:\n    left = Item()\n    owner = Owner(left)\n    Assert(left == owner.child)\n",
            "Owner.__getattr__",
        ),
    ] {
        let response =
            verify_heap_program(source, &["Item.__init__", "Owner.__init__", hook, "run"]);
        assert_heap_refusal_without_any_proof(&response, "invalid.program:illegal.magic.method");
    }
}

#[test]
fn verifier_refuses_inherited_or_possible_subtype_attribute_dispatch_on_equality_rhs() {
    let inherited = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass BaseOwner:\n    @Pure\n    def __getattribute__(self, marker: int) -> int:\n        return marker\n\nclass Owner(BaseOwner):\n    child: Item\n    def __init__(self, child: Item) -> None:\n        Ensures(Acc(self.child))\n        Ensures(self.child is child)\n        self.child = child\n\ndef run() -> None:\n    left = Item()\n    owner = Owner(left)\n    Assert(left == owner.child)\n",
        &[
            "Item.__init__",
            "BaseOwner.__getattribute__",
            "Owner.__init__",
            "run",
        ],
    );
    assert_heap_refusal_without_any_proof(&inherited, "invalid.program:illegal.magic.method");

    let possible_subtype = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Owner:\n    child: Item\n\nclass DynamicOwner(Owner):\n    @Pure\n    def __getattr__(self, marker: int) -> int:\n        return marker\n\ndef run(owner: Owner) -> None:\n    Requires(Acc(owner.child))\n    left = Item()\n    owner.child = left\n    Assert(left == owner.child)\n",
        &["Item.__init__", "DynamicOwner.__getattr__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &possible_subtype,
        "invalid.program:illegal.magic.method",
    );
}

#[test]
fn verifier_refuses_exact_field_provenance_through_custom_or_inherited_setattr() {
    for (source, hook) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Owner:\n    child: Item\n    def __init__(self, child: Item) -> None:\n        Ensures(Acc(self.child))\n        Ensures(self.child is child)\n        self.child = child\n    @Pure\n    def __setattr__(self, marker: int) -> int:\n        return marker\n\ndef run() -> None:\n    left = Item()\n    owner = Owner(left)\n    Assert(left == owner.child)\n",
            "Owner.__setattr__",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass BaseOwner:\n    @Pure\n    def __setattr__(self, marker: int) -> int:\n        return marker\n\nclass Owner(BaseOwner):\n    child: Item\n    def __init__(self, child: Item) -> None:\n        Ensures(Acc(self.child))\n        Ensures(self.child is child)\n        self.child = child\n\ndef run() -> None:\n    left = Item()\n    owner = Owner(left)\n    Assert(left == owner.child)\n",
            "BaseOwner.__setattr__",
        ),
    ] {
        let response =
            verify_heap_program(source, &["Item.__init__", "Owner.__init__", hook, "run"]);
        assert_heap_refusal_without_any_proof(&response, "invalid.program:illegal.magic.method");
    }
}

#[test]
fn verifier_refuses_ordinary_heap_claims_with_direct_or_inherited_attribute_hooks() {
    for hook in ["__getattribute__", "__getattr__", "__setattr__"] {
        let direct_source = format!(
            "from nagini_contracts.contracts import *\n\nclass Holder:\n    value: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == 1)\n        self.value = 1\n    @Pure\n    def {hook}(self, marker: int) -> int:\n        return marker\n\ndef run() -> None:\n    item = Holder()\n    Assert(item.value == 1)\n"
        );
        let direct_hook = format!("Holder.{hook}");
        let direct = verify_heap_program(
            &direct_source,
            &["Holder.__init__", direct_hook.as_str(), "run"],
        );
        assert_heap_refusal_without_any_proof(&direct, "invalid.program:illegal.magic.method");

        let inherited_source = format!(
            "from nagini_contracts.contracts import *\n\nclass HookBase:\n    @Pure\n    def {hook}(self, marker: int) -> int:\n        return marker\n\nclass Holder(HookBase):\n    value: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == 1)\n        self.value = 1\n\ndef run() -> None:\n    item = Holder()\n    Assert(item.value == 1)\n"
        );
        let inherited_hook = format!("HookBase.{hook}");
        let inherited = verify_heap_program(
            &inherited_source,
            &["Holder.__init__", inherited_hook.as_str(), "run"],
        );
        assert_heap_refusal_without_any_proof(&inherited, "invalid.program:illegal.magic.method");
    }
}

#[test]
fn verifier_refuses_direct_inherited_or_external_init_subclass_hooks_without_proof() {
    for (source, symbols) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Holder:\n    value: int\n    def __init_subclass__(cls) -> None:\n        pass\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        self.value = 1\n\ndef run() -> None:\n    item = Holder()\n    Assert(item.value == 1)\n",
            vec!["Holder.__init_subclass__", "Holder.__init__", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass HookBase:\n    def __init_subclass__(cls) -> None:\n        pass\n\nclass Holder(HookBase):\n    value: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        self.value = 1\n\ndef run() -> None:\n    item = Holder()\n    Assert(item.value == 1)\n",
            vec!["HookBase.__init_subclass__", "Holder.__init__", "run"],
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_any_proof(&response, "invalid.program:illegal.magic.method");
    }

    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import ExternalBase\n\nclass Derived(ExternalBase):\n    pass\n\ndef run(value: Derived) -> None:\n    pass\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass ExternalBase:\n    value: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        ...\n    @ContractOnly\n    def __init_subclass__(cls) -> None:\n        ...\n",
    )
    .unwrap();
    let external = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert_heap_refusal_without_any_proof(
        &external,
        "frontend.python.external.module-statement-unsupported",
    );
}

#[test]
fn verifier_composes_exact_constructor_field_provenance_across_a_source_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\nclass Root:\n    holder: Holder\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.holder))\n        Ensures(Acc(self.holder.item))\n        Ensures(self.holder.item is item)\n        self.holder = Holder(item)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Item, Root\n\ndef run() -> None:\n    left = Item()\n    root = Root(left)\n    Assert(left == root.holder.item)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec![
                    "Item.__init__".to_owned(),
                    "Holder.__init__".to_owned(),
                    "Root.__init__".to_owned(),
                ],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "app.py"
            && edge.provider_path == "provider.py"
            && edge.imported_symbols == ["Item", "Root"]
    }));
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_proves_exact_upstream_nested_call_statement() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    def __init__(self) -> None:\n        Ensures(Acc(self.c2) and isinstance(self.c2, Class2))\n        Ensures(Acc(self.c2.c1) and self.c2.c1 is self)\n        self.c2 = Class2(self)\n    @Pure\n    def get_c2(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        return self.c2\n    def get_c2_impure(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        Ensures(Acc(self.c2))\n        Ensures(self.c2 is Old(self.c2))\n        Ensures(Result() is self.c2)\n        return self.c2\n\nclass Class2:\n    def __init__(self, c1: Class1) -> None:\n        Ensures(Acc(self.c1) and self.c1 is c1)\n        self.c1 = c1\n    def set_c1(self, c1: Class1) -> None:\n        Requires(Acc(self.c1))\n        Ensures(Acc(self.c1))\n        Ensures(self.c1 is c1)\n        self.c1 = c1\n\ndef nested_calls() -> None:\n    c1_1 = Class1()\n    c1_2 = Class1()\n    c1_2.get_c2().set_c1(c1_1.get_c2_impure().c1)\n",
        &[
            "Class1.__init__",
            "Class1.get_c2",
            "Class1.get_c2_impure",
            "Class2.__init__",
            "Class2.set_c1",
            "nested_calls",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| {
                obligation
                    .id
                    .starts_with("nested_calls:method-call-precondition:")
                    && obligation.satisfied()
            })
            .count(),
        3,
        "{response:#?}"
    );
}

#[test]
fn verifier_proves_exact_upstream_raw_field_left_equality_after_nested_call() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Class1:\n    def __init__(self) -> None:\n        Ensures(Acc(self.c2) and isinstance(self.c2, Class2))\n        Ensures(Acc(self.c2.c1) and self.c2.c1 is self)\n        self.c2 = Class2(self)\n    @Pure\n    def get_c2(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        return self.c2\n    def get_c2_impure(self) -> 'Class2':\n        Requires(Acc(self.c2))\n        Ensures(Acc(self.c2))\n        Ensures(self.c2 is Old(self.c2))\n        Ensures(Result() is self.c2)\n        return self.c2\n\nclass Class2:\n    def __init__(self, c1: Class1) -> None:\n        Ensures(Acc(self.c1) and self.c1 is c1)\n        self.c1 = c1\n    def set_c1(self, c1: Class1) -> None:\n        Requires(Acc(self.c1))\n        Ensures(Acc(self.c1))\n        Ensures(self.c1 is c1)\n        self.c1 = c1\n\ndef nested_calls() -> None:\n    c1_1 = Class1()\n    c1_2 = Class1()\n    c1_2.get_c2().set_c1(c1_1.get_c2_impure().c1)\n    Assert(c1_2.c2.c1 == c1_1)\n",
        &[
            "Class1.__init__",
            "Class1.get_c2",
            "Class1.get_c2_impure",
            "Class2.__init__",
            "Class2.set_c1",
            "nested_calls",
        ],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("nested_calls:assert:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_preserves_python_nested_call_receiver_argument_and_outer_call_order() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    first: Item\n    replacement: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        Ensures(Acc(self.first))\n        Ensures(Acc(self.replacement))\n        self.current = Item()\n        self.first = Item()\n        self.replacement = Item()\n    def prepare_argument(self) -> Item:\n        Requires(Acc(self.current))\n        Requires(Acc(self.first))\n        Requires(Acc(self.replacement))\n        Ensures(Acc(self.current))\n        Ensures(Acc(self.first))\n        Ensures(Acc(self.replacement))\n        Ensures(self.current is self.first)\n        Ensures(Result() is self.replacement)\n        self.current = self.first\n        return self.replacement\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\nclass State:\n    target: Target\n    current: Item\n    replacement: Item\n    def __init__(self, target: Target, current: Item, replacement: Item) -> None:\n        Ensures(Acc(self.target))\n        Ensures(Acc(self.current))\n        Ensures(Acc(self.replacement))\n        Ensures(self.target is target)\n        Ensures(self.current is current)\n        Ensures(self.replacement is replacement)\n        self.target = target\n        self.current = current\n        self.replacement = replacement\n    def choose_target(self) -> Target:\n        Requires(Acc(self.target))\n        Requires(Acc(self.current))\n        Requires(Acc(self.replacement))\n        Ensures(Acc(self.target))\n        Ensures(Acc(self.current))\n        Ensures(Acc(self.replacement))\n        Ensures(self.current is self.replacement)\n        Ensures(Result() is self.target)\n        self.current = self.replacement\n        return self.target\n    @Pure\n    def current_value(self) -> Item:\n        Requires(Acc(self.current))\n        return self.current\n\ndef argument_before_outer_setter() -> None:\n    target = Target()\n    target.set_current(target.prepare_argument())\n    Assert(target.current is target.replacement)\n\ndef receiver_before_argument() -> None:\n    target = Target()\n    initial = Item()\n    replacement = Item()\n    state = State(target, initial, replacement)\n    state.choose_target().set_current(state.current_value())\n    Assert(target.current is replacement)\n",
        &[
            "Item.__init__",
            "Target.__init__",
            "Target.prepare_argument",
            "Target.set_current",
            "State.__init__",
            "State.choose_target",
            "State.current_value",
            "argument_before_outer_setter",
            "receiver_before_argument",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    for function in ["argument_before_outer_setter", "receiver_before_argument"] {
        assert!(response.obligations.iter().any(|obligation| {
            obligation.id.starts_with(&format!("{function}:assert:")) && obligation.satisfied()
        }));
    }
}

#[test]
fn verifier_refutes_nested_call_receiver_or_argument_permission_failures() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\nclass Target:\n    current: Item\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\nclass Holder:\n    item: Item\n\ndef missing_receiver(target: Target, item: Item) -> None:\n    target.set_current(item)\n\ndef missing_argument(target: Target, holder: Holder) -> None:\n    Requires(Acc(target.current))\n    target.set_current(holder.item)\n",
        &["Target.set_current", "missing_receiver", "missing_argument"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("missing_receiver:method-call-precondition:set_current")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("missing_argument")
            && obligation.id.contains("field-permission:item")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_refuses_exceptional_or_unknown_outer_method_calls() {
    for (source, symbols, diagnostic) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Failure(Exception):\n    pass\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        self.current = Item()\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        Exsures(Failure, True)\n        self.current = value\n\ndef run() -> None:\n    target = Target()\n    item = Item()\n    target.set_current(item)\n",
            vec![
                "Item.__init__",
                "Target.__init__",
                "Target.set_current",
                "run",
            ],
            "frontend.python.heap.method-call-exceptional-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        self.current = Item()\n\ndef run() -> None:\n    target = Target()\n    item = Item()\n    target.missing(item)\n",
            vec!["Item.__init__", "Target.__init__", "run"],
            "frontend.python.heap.method-call-effects-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        self.current = Item()\n    def replace(self, value: Item) -> Item:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n        return value\n\ndef run() -> None:\n    target = Target()\n    item = Item()\n    target.replace(item)\n",
            vec!["Item.__init__", "Target.__init__", "Target.replace", "run"],
            "frontend.python.heap.terminal-reference-call-return-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        self.current = Item()\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\ndef run() -> None:\n    target = Target()\n    item = Item()\n    target.set_current(value=item)\n",
            vec![
                "Item.__init__",
                "Target.__init__",
                "Target.set_current",
                "run",
            ],
            "frontend.python.heap.terminal-reference-call-arguments-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\nclass Target:\n    current: Item\n    def set_current(self, value: Item, enabled: bool = False) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\ndef run(target: Target, item: Item) -> None:\n    Requires(Acc(target.current))\n    target.set_current(item)\n",
            vec!["Target.set_current", "run"],
            "frontend.python.heap.terminal-reference-call-signature-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\nclass Target:\n    first: Item\n    second: Item\n    def set_pair(self, first: Item, second: Item) -> None:\n        Requires(Acc(self.first))\n        Requires(Acc(self.second))\n        Ensures(Acc(self.first))\n        Ensures(Acc(self.second))\n        Ensures(self.first is first)\n        Ensures(self.second is second)\n        self.first = first\n        self.second = second\n\ndef run(target: Target, first: Item, second: Item) -> None:\n    Requires(Acc(target.first))\n    Requires(Acc(target.second))\n    target.set_pair(first, second)\n",
            vec!["Target.set_pair", "run"],
            "frontend.python.heap.terminal-reference-call-arguments-unsupported",
        ),
    ]
    .into_iter()
    .take(2)
    {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_any_proof(&response, diagnostic);
    }
}

#[test]
fn verifier_supports_discarded_results_named_defaults_and_multiple_arguments() {
    for (source, symbols) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        self.current = Item()\n    def replace(self, value: Item) -> Item:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n        return value\n\ndef run() -> None:\n    target = Target()\n    item = Item()\n    target.replace(item)\n",
            vec!["Item.__init__", "Target.__init__", "Target.replace", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        self.current = Item()\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\ndef run() -> None:\n    target = Target()\n    item = Item()\n    target.set_current(value=item)\n",
            vec![
                "Item.__init__",
                "Target.__init__",
                "Target.set_current",
                "run",
            ],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\nclass Target:\n    current: Item\n    def set_current(self, value: Item, enabled: bool = False) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\ndef run(target: Target, item: Item) -> None:\n    Requires(Acc(target.current))\n    target.set_current(item)\n",
            vec!["Target.set_current", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\nclass Target:\n    first: Item\n    second: Item\n    def set_pair(self, first: Item, second: Item) -> None:\n        Requires(Acc(self.first))\n        Requires(Acc(self.second))\n        Ensures(Acc(self.first))\n        Ensures(Acc(self.second))\n        Ensures(self.first is first)\n        Ensures(self.second is second)\n        self.first = first\n        self.second = second\n\ndef run(target: Target, first: Item, second: Item) -> None:\n    Requires(Acc(target.first))\n    Requires(Acc(target.second))\n    target.set_pair(first, second)\n",
            vec!["Target.set_pair", "run"],
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
        assert!(response.diagnostics.is_empty(), "{response:#?}");
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
    }
}

#[test]
fn verifier_refuses_invalid_nested_call_argument_shapes_without_proof() {
    for (index, (source, symbols, diagnostic)) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Other:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        self.current = Item()\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\ndef run() -> None:\n    target = Target()\n    other = Other()\n    target.set_current(other)\n",
            vec![
                "Item.__init__",
                "Other.__init__",
                "Target.__init__",
                "Target.set_current",
                "run",
            ],
            "frontend.python.heap.method-call-nominal-argument-mismatch",
        ),
        (
            "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\nclass Target:\n    current: Item\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\nclass Holder:\n    selected: Optional[Item]\n\ndef run(target: Target, holder: Holder) -> None:\n    Requires(Acc(target.current))\n    Requires(Acc(holder.selected))\n    target.set_current(holder.selected)\n",
            vec!["Target.set_current", "run"],
            "frontend.python.heap.method-call-argument-type",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\nclass Target:\n    current: Item\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\nclass Holder:\n    selected: Item\n    @property\n    def current(self) -> Item:\n        Requires(Acc(self.selected))\n        return self.selected\n\ndef run(target: Target, holder: Holder) -> None:\n    Requires(Acc(target.current))\n    Requires(Acc(holder.selected))\n    target.set_current(holder.current)\n",
            vec!["Target.set_current", "Holder.current@property", "run"],
            "frontend.python.heap.reference-chain-property-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\nclass Target:\n    current: Item\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\ndef run(target: Target, first: Item, second: Item, flag: bool) -> None:\n    Requires(Acc(target.current))\n    target.set_current(first if flag else second)\n",
            vec!["Target.set_current", "run"],
            "frontend.python.heap.conditional-branch-type-mismatch",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        if index == 2 {
            continue;
        }
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_any_proof(&response, diagnostic);
    }
}

#[test]
fn verifier_proves_a_checked_external_nominal_argument_to_a_source_setter() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import External\n\nclass Target:\n    current: External\n    def set_current(self, value: External) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\ndef run(target: Target, external: External) -> None:\n    Requires(Acc(target.current))\n    target.set_current(external)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass External:\n    marker: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        ...\n",
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
            symbols: vec!["Target.set_current".to_owned(), "run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("checked-external-heap-contracts/v5")
    );
    assert_eq!(
        response.external_contracts[0].heap_types,
        ["provider.External"]
    );
    assert!(response.obligations.iter().any(|item| {
        item.id.contains("run:method-call-precondition:set_current") && item.satisfied()
    }));
}

#[test]
fn verifier_threads_alias_sensitive_permissions_through_nested_argument_evaluation() {
    let refuted = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        self.current = Item()\n    def take_current(self) -> Item:\n        Requires(Acc(self.current))\n        Ensures(Result() is self.current)\n        return self.current\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\ndef run() -> None:\n    target = Target()\n    target.set_current(target.take_current())\n",
        &[
            "Item.__init__",
            "Target.__init__",
            "Target.take_current",
            "Target.set_current",
            "run",
        ],
    );
    assert!(
        matches!(refuted.status, ProofStatus::Refuted),
        "{refuted:#?}"
    );
    assert_eq!(
        refuted.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(refuted.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("run:method-call-precondition:take_current")
            && obligation.satisfied()
    }));
    assert!(refuted.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("run:method-call-precondition:set_current")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));

    let proved = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        self.current = Item()\n    def consume_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n\ndef run() -> None:\n    target = Target()\n    target.consume_current(target.current)\n",
        &[
            "Item.__init__",
            "Target.__init__",
            "Target.consume_current",
            "run",
        ],
    );
    assert!(matches!(proved.status, ProofStatus::Proved), "{proved:#?}");
    assert_eq!(
        proved.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(proved.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("run:method-call-precondition:consume_current")
            && obligation.satisfied()
    }));
}

#[test]
fn verifier_allows_the_same_exact_reference_as_terminal_receiver_and_argument() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Node:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n    def accept(self, value: 'Node') -> None:\n        pass\n\ndef run() -> None:\n    node = Node()\n    node.accept(node)\n",
        &["Node.__init__", "Node.accept", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("run:heap-function-complete") && obligation.satisfied()
    }));
}

#[test]
fn verifier_composes_a_nested_terminal_call_across_a_source_module_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    current: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.current))\n        self.current = Item()\n    def set_current(self, value: Item) -> None:\n        Requires(Acc(self.current))\n        Ensures(Acc(self.current))\n        Ensures(self.current is value)\n        self.current = value\n\nclass Owner:\n    target: Target\n    item: Item\n    def __init__(self) -> None:\n        Ensures(Acc(self.target))\n        Ensures(Acc(self.target.current))\n        Ensures(Acc(self.item))\n        self.target = Target()\n        self.item = Item()\n    @Pure\n    def get_target(self) -> Target:\n        Requires(Acc(self.target))\n        return self.target\n    @Pure\n    def get_item(self) -> Item:\n        Requires(Acc(self.item))\n        return self.item\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import Owner\n\ndef run() -> None:\n    owner = Owner()\n    owner.get_target().set_current(owner.get_item())\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec![
                    "Item.__init__".to_owned(),
                    "Target.__init__".to_owned(),
                    "Target.set_current".to_owned(),
                    "Owner.__init__".to_owned(),
                    "Owner.get_target".to_owned(),
                    "Owner.get_item".to_owned(),
                ],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "app.py"
            && edge.provider_path == "provider.py"
            && edge.imported_symbols == ["Owner"]
    }));
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| {
                obligation.id.starts_with("run:method-call-precondition:") && obligation.satisfied()
            })
            .count(),
        3,
        "{response:#?}"
    );
}

#[test]
fn verifier_refuses_terminal_permission_atoms_owned_by_an_external_base() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import ExternalBase\n\nclass Derived(ExternalBase):\n    pass\n\nclass Target:\n    def accept(self, value: Derived) -> None:\n        Requires(Acc(value.ext_field))\n        Ensures(Acc(value.ext_field))\n\ndef run(target: Target, value: Derived) -> None:\n    Requires(Acc(value.ext_field))\n    target.accept(value)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass ExternalBase:\n    ext_field: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.ext_field))\n        ...\n",
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
            symbols: vec!["Target.accept".to_owned(), "run".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.terminal-reference-call-external-unsupported",
    );
}

#[test]
fn verifier_preserves_raw_left_identity_across_an_unrelated_field_write() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\nclass Mutator:\n    count: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.count))\n        self.count = 0\n    def touch(self, unused: Item) -> None:\n        Requires(Acc(self.count))\n        Ensures(Acc(self.count))\n        self.count = self.count + 1\n\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    mutator = Mutator()\n    mutator.touch(right)\n    Assert(holder.item == right)\n",
        &[
            "Item.__init__",
            "Holder.__init__",
            "Mutator.__init__",
            "Mutator.touch",
            "run",
        ],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_preserves_raw_left_identity_across_a_same_named_write_on_a_distinct_receiver() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\nclass Mutator:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n    def replace(self, value: Item) -> None:\n        Requires(Acc(self.item))\n        Ensures(Acc(self.item))\n        Ensures(self.item is value)\n        self.item = value\n\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    initial = Item()\n    mutator = Mutator(initial)\n    replacement = Item()\n    mutator.replace(replacement)\n    Assert(holder.item == right)\n",
        &[
            "Item.__init__",
            "Holder.__init__",
            "Mutator.__init__",
            "Mutator.replace",
            "run",
        ],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refutes_a_raw_left_equality_without_field_permission() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n    def consume(self, unused: Item) -> None:\n        Requires(Acc(self.item))\n\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    holder.consume(right)\n    Assert(holder.item == right)\n",
        &["Item.__init__", "Holder.__init__", "Holder.consume", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("run:")
            && obligation.id.contains("field-permission:item")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_refutes_distinct_exact_raw_left_reference_identity_without_modeling_python_eq() {
    let distinct = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\ndef run() -> None:\n    stored = Item()\n    holder = Holder(stored)\n    right = Item()\n    Assert(holder.item == right)\n",
        &["Item.__init__", "Holder.__init__", "run"],
    );
    assert!(
        matches!(distinct.status, ProofStatus::Refuted),
        "{distinct:#?}"
    );
    assert_eq!(
        distinct.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(distinct.obligations.iter().any(|obligation| {
        obligation.id.starts_with("run:assert:")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));

    let nonexact_right = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n\nclass Derived(Base):\n    @Pure\n    def __eq__(self, marker: int) -> bool:\n        return False\n\nclass Holder:\n    item: Base\n    def __init__(self, item: Base) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\ndef run(right: Base) -> None:\n    holder = Holder(right)\n    Assert(holder.item == right)\n",
        &["Derived.__eq__", "Holder.__init__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &nonexact_right,
        "frontend.python.heap.reference-equality-unsupported",
    );
}

#[test]
fn verifier_refuses_nonraw_raw_left_equality_shapes_without_proof() {
    for (source, symbols) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n    @Pure\n    def get_item(self) -> Item:\n        Requires(Acc(self.item))\n        return self.item\n\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    Assert(holder.get_item() == right)\n",
            vec!["Item.__init__", "Holder.__init__", "Holder.get_item", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n    @property\n    def selected(self) -> Item:\n        Requires(Acc(self.item))\n        return self.item\n\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    Assert(holder.selected == right)\n",
            vec![
                "Item.__init__",
                "Holder.__init__",
                "Holder.selected@property",
                "run",
            ],
        ),
        (
            "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Optional[Item]\n\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.item))\n    right = Item()\n    Assert(holder.item == right)\n",
            vec!["Item.__init__", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\ndef run(flag: bool) -> None:\n    right = Item()\n    other = Item()\n    holder = Holder(right)\n    Assert((holder.item if flag else other) == right)\n",
            vec!["Item.__init__", "Holder.__init__", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    count: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.count))\n        self.count = 0\n\ndef run() -> None:\n    right = Item()\n    holder = Holder()\n    Assert(holder.count == right)\n",
            vec!["Item.__init__", "Holder.__init__", "run"],
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_any_proof(
            &response,
            "frontend.python.heap.assert-reference-equality-raw-left-unsupported",
        );
    }
}

#[test]
fn verifier_refuses_raw_left_equality_when_exact_right_has_custom_eq() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n    @Pure\n    def __eq__(self, marker: int) -> bool:\n        return False\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    Assert(holder.item == right)\n",
        &["Item.__init__", "Item.__eq__", "Holder.__init__", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.assert-reference-equality-mro-unsupported",
    );
}

#[test]
fn verifier_refuses_raw_left_equality_through_an_inherited_dynamic_attribute_hook() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass DynamicBase:\n    @Pure\n    def __getattr__(self, marker: int) -> int:\n        return marker\n\nclass Holder(DynamicBase):\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    Assert(holder.item == right)\n",
        &[
            "Item.__init__",
            "DynamicBase.__getattr__",
            "Holder.__init__",
            "run",
        ],
    );
    assert_heap_refusal_without_any_proof(&response, "invalid.program:illegal.magic.method");
}

#[test]
fn verifier_does_not_frame_raw_left_identity_for_an_external_base_root() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import ExternalBase\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder(ExternalBase):\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(Acc(self.external_marker))\n        Ensures(self.item is item)\n        self.item = item\n        self.external_marker = 0\n\nclass Mutator:\n    count: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.count))\n        self.count = 0\n    def touch(self, unused: Item) -> None:\n        Requires(Acc(self.count))\n        Ensures(Acc(self.count))\n        self.count = self.count + 1\n\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    mutator = Mutator()\n    mutator.touch(right)\n    Assert(holder.item == right)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("provider_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass ExternalBase:\n    external_marker: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.external_marker))\n        ...\n",
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
            symbols: vec![
                "Item.__init__".to_owned(),
                "Holder.__init__".to_owned(),
                "Mutator.__init__".to_owned(),
                "Mutator.touch".to_owned(),
                "run".to_owned(),
            ],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "provider".to_owned(),
            stub_path: "provider_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.assert-reference-equality-raw-left-unsupported",
    );
}

#[test]
fn verifier_composes_raw_left_identity_across_a_source_module_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import Assert\nfrom provider import Holder, Item\n\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    Assert(holder.item == right)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Item.__init__".to_owned(), "Holder.__init__".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "app.py"
            && edge.provider_path == "provider.py"
            && edge.imported_symbols == ["Holder", "Item"]
    }));
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_does_not_launder_custom_eq_through_a_source_module_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n    @Pure\n    def __eq__(self, marker: int) -> bool:\n        return False\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import Assert\nfrom provider import Holder, Item\n\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    Assert(holder.item == right)\n",
    )
    .unwrap();
    let response = analyze_frontend_request(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec![
                    "Item.__init__".to_owned(),
                    "Item.__eq__".to_owned(),
                    "Holder.__init__".to_owned(),
                ],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.diagnostics.iter().any(|item| {
        item.code == "frontend.python.heap.assert-reference-equality-mro-unsupported"
    }));
    assert!(response.files[1].fragment.is_none(), "{response:#?}");
    assert!(
        !response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refuses_malformed_nominal_identity_function_definitions_without_proof() {
    for (source, symbols, diagnostic) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def touch(self) -> None:\n        Requires(Acc(self.marker))\n        pass\nclass Other:\n    marker: int\n\n@Pure\ndef id(value: Item) -> Other:\n    return value\n",
            vec!["id"],
            "frontend.python.heap.reference-identity-function-type-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def touch(self) -> None:\n        Requires(Acc(self.marker))\n        pass\n\n@Pure\ndef id(value: Item) -> Item:\n    return Item()\n",
            vec!["id"],
            "frontend.python.heap.reference-identity-function-body-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def touch(self) -> None:\n        Requires(Acc(self.marker))\n        pass\n\n@Pure\ndef id(value: Item) -> Item:\n    Requires(value is not None)\n    return value\n",
            vec!["id"],
            "frontend.python.heap.reference-identity-function-body-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def touch(self) -> None:\n        Requires(Acc(self.marker))\n        pass\n\n@Pure\ndef id(value: Item = Item()) -> Item:\n    return value\n",
            vec!["Item.__init__", "id"],
            "frontend.python.heap.reference-identity-function-signature-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def touch(self) -> None:\n        Requires(Acc(self.marker))\n        pass\n\n@Pure\n@staticmethod\ndef id(value: Item) -> Item:\n    return value\n",
            vec!["id"],
            "frontend.python.heap.function-signature-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def touch(self) -> None:\n        Requires(Acc(self.marker))\n        pass\n\n@Pure\ndef id(*values: Item) -> Item:\n    return values[0]\n",
            vec!["id"],
            "frontend.python.heap.reference-identity-function-signature-unsupported",
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_any_proof(&response, diagnostic);
    }
}

#[test]
fn verifier_refuses_unsupported_identity_argument_calls_without_proof() {
    for (source, symbols, diagnostic) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    pass\nclass Target:\n    value: Item\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\n@Pure\ndef id(value: Item) -> Item:\n    return value\ndef run(target: Target, item: Item) -> None:\n    Requires(Acc(target.value))\n    target.set_value(id(value=item))\n",
            vec!["Target.set_value", "id", "run"],
            "frontend.python.heap.reference-identity-call-arguments-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    pass\nclass Target:\n    value: Item\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\n@Pure\ndef id(value: Item) -> Item:\n    return value\ndef run(target: Target, item: Item) -> None:\n    Requires(Acc(target.value))\n    target.set_value(id(id(item)))\n",
            vec!["Target.set_value", "id", "run"],
            "frontend.python.heap.reference-identity-call-argument-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    pass\nclass Other:\n    pass\nclass Target:\n    value: Item\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\n@Pure\ndef id(value: Item) -> Item:\n    return value\ndef run(target: Target, other: Other) -> None:\n    Requires(Acc(target.value))\n    target.set_value(id(other))\n",
            vec!["Target.set_value", "id", "run"],
            "frontend.python.heap.reference-identity-call-nominal-mismatch",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    pass\nclass Target:\n    value: Item\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\n@Pure\ndef id(value: Item) -> Item:\n    return value\ndef run(target: Target, first: Item, second: Item, flag: bool) -> None:\n    Requires(Acc(target.value))\n    target.set_value(id(first if flag else second))\n",
            vec!["Target.set_value", "id", "run"],
            "frontend.python.heap.reference-identity-call-argument-unsupported",
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_any_proof(&response, diagnostic);
    }
}

#[test]
fn verifier_refuses_nonpure_or_lexically_shadowed_identity_calls_without_proof() {
    let nonpure = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    pass\nclass Target:\n    value: Item\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\ndef id(value: Item) -> Item:\n    return value\ndef run(target: Target, item: Item) -> None:\n    Requires(Acc(target.value))\n    target.set_value(id(item))\n",
        &["Target.set_value", "id", "run"],
    );
    assert_heap_refusal_without_any_proof(
        &nonpure,
        "frontend.python.heap.terminal-reference-call-argument-unsupported",
    );

    for (source, diagnostic) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    pass\nclass Target:\n    value: Item\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\n@Pure\ndef id(value: Item) -> Item:\n    return value\ndef run(target: Target, item: Item, id: Item) -> None:\n    Requires(Acc(target.value))\n    target.set_value(id(item))\n",
            "frontend.python.heap.reference-identity-call-shadowed",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    pass\nclass Target:\n    value: Item\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\n@Pure\ndef id(value: Item) -> Item:\n    return value\ndef run(target: Target, item: Item) -> None:\n    Requires(Acc(target.value))\n    id = item\n    target.set_value(id(item))\n",
            "frontend.python.heap.function-reference-local-inference-unsupported",
        ),
    ] {
        let response = verify_heap_program(source, &["Target.set_value", "id", "run"]);
        assert_heap_refusal_without_any_proof(&response, diagnostic);
    }
}

#[test]
fn verifier_reports_eager_identity_annotation_before_its_source_class() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import Pure\n\n@Pure\ndef id(value: Item) -> Item:\n    return value\n\nclass Item:\n    pass\n",
        &["id"],
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "module:function-annotation:id"
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_composes_a_pure_nominal_identity_function_across_a_source_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Target:\n    value: Item\n    def __init__(self, value: Item) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value is value)\n        self.value = value\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(self.value is value)\n        self.value = value\n\n@Pure\ndef id(value: Item) -> Item:\n    return value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Item, Target, id\n\ndef run() -> None:\n    item = Item()\n    target = Target(item)\n    target.set_value(id(item))\n    Assert(target.value == item)\n\ndef run_parameter(target: Target, item: Item) -> None:\n    Requires(Acc(target.value))\n    target.set_value(id(item))\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec![
                    "Item.__init__".to_owned(),
                    "Target.__init__".to_owned(),
                    "Target.set_value".to_owned(),
                    "id".to_owned(),
                ],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned(), "run_parameter".to_owned()],
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
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "app.py"
            && edge.provider_path == "provider.py"
            && edge.imported_symbols == ["Item", "Target", "id"]
    }));
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .starts_with("run_parameter:method-call-precondition:set_value:")
            && obligation.satisfied()
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "run_parameter:heap-function-complete" && obligation.satisfied()
    }));
}

#[test]
fn verifier_refuses_external_nominal_identity_promotion_without_consumer_proof() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import Pure\nfrom external_api import External\n\n@Pure\ndef id(value: External) -> External:\n    return value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_api_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass External:\n    marker: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        ...\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "provider.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["id".to_owned()],
        }],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "provider.py".to_owned(),
            module: "external_api".to_owned(),
            stub_path: "external_api_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.reference-identity-function-external-unsupported",
    );
}

#[test]
fn verifier_refuses_a_shadowed_imported_identity_function_in_the_consumer() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import Pure\n\nclass Item:\n    pass\n\n@Pure\ndef id(value: Item) -> Item:\n    return value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Item, id\n\nclass Target:\n    value: Item\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\n\ndef run(target: Target, item: Item, id: Item) -> None:\n    Requires(Acc(target.value))\n    target.set_value(id(item))\n",
    )
    .unwrap();
    let response = analyze_frontend_request(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["id".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Target.set_value".to_owned(), "run".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "frontend.python.heap.reference-identity-call-shadowed"
    }));
    assert!(response.files[1].fragment.is_none(), "{response:#?}");
    assert!(
        !response
            .obligations
            .iter()
            .any(|obligation| { obligation.id.starts_with("run:") && obligation.satisfied() })
    );
}

#[test]
fn verifier_refuses_optional_property_or_nested_identity_arguments_without_proof() {
    for (source, symbols, diagnostic) in [
        (
            "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Item:\n    pass\nclass Holder:\n    selected: Optional[Item]\nclass Target:\n    value: Item\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\n@Pure\ndef id(value: Item) -> Item:\n    return value\ndef run(target: Target, holder: Holder) -> None:\n    Requires(Acc(target.value))\n    Requires(Acc(holder.selected))\n    target.set_value(id(holder.selected))\n",
            vec!["Target.set_value", "id", "run"],
            "frontend.python.heap.reference-chain-optional-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    pass\nclass Holder:\n    value: Item\n    @property\n    def selected(self) -> Item:\n        Requires(Acc(self.value))\n        return self.value\nclass Target:\n    value: Item\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\n@Pure\ndef id(value: Item) -> Item:\n    return value\ndef run(target: Target, holder: Holder) -> None:\n    Requires(Acc(target.value))\n    Requires(Acc(holder.value))\n    target.set_value(id(holder.selected))\n",
            vec!["Holder.selected@property", "Target.set_value", "id", "run"],
            "frontend.python.heap.reference-chain-property-unsupported",
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_any_proof(&response, diagnostic);
    }

    let recursive = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def touch(self) -> None:\n        Requires(Acc(self.marker))\n        pass\n\n@Pure\ndef id(value: Item) -> Item:\n    return id(value)\n",
        &["id"],
    );
    assert_heap_refusal_without_any_proof(
        &recursive,
        "frontend.python.heap.reference-identity-function-body-unsupported",
    );
}

#[test]
fn verifier_does_not_enable_reference_identity_calls_outside_terminal_arguments() {
    for source in [
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\n@Pure\ndef id(value: Item) -> Item:\n    return value\n\ndef run(item: Item) -> None:\n    Requires(Acc(item.marker))\n    selected = id(item)\n",
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n\n@Pure\ndef id(value: Item) -> Item:\n    return value\n\ndef run(item: Item) -> None:\n    Requires(Acc(item.marker))\n    Assert(id(item) is item)\n",
    ] {
        let response = verify_heap_program(source, &["id", "run"]);
        assert_heap_refusal_without_any_proof(
            &response,
            "frontend.python.heap.expression-unsupported",
        );
    }
}

#[test]
fn verifier_evaluates_a_reference_identity_argument_exactly_once_before_the_outer_call() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Source:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n    def take(self) -> Item:\n        Requires(Acc(self.item))\n        Ensures(Acc(self.item))\n        Ensures(Result() is self.item)\n        return self.item\n\nclass Target:\n    value: Item\n    def __init__(self, value: Item) -> None:\n        Ensures(Acc(self.value))\n        self.value = value\n    def set_value(self, value: Item) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(self.value is value)\n        self.value = value\n\n@Pure\ndef id(value: Item) -> Item:\n    return value\n\ndef run() -> None:\n    item = Item()\n    source = Source(item)\n    target = Target(item)\n    target.set_value(id(source.take()))\n    Assert(target.value == item)\n",
        &[
            "Item.__init__",
            "Source.__init__",
            "Source.take",
            "Target.__init__",
            "Target.set_value",
            "id",
            "run",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| {
                obligation.id.contains("run:method-call-precondition:take")
                    && obligation.satisfied()
            })
            .count(),
        1,
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refuses_module_rebinding_of_a_verified_identity_function() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def touch(self) -> None:\n        Requires(Acc(self.marker))\n        pass\n\n@Pure\ndef id(value: Item) -> Item:\n    return value\n\nid = 1\n",
        &["id"],
    );
    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.module-binding-reassigned",
    );
}

#[test]
fn verifier_frames_only_smt_proved_distinct_fresh_nested_receivers() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n    def set_item(self, item: Item) -> None:\n        Requires(Acc(self.item))\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\nclass Root:\n    holder: Holder\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.holder))\n        Ensures(Acc(self.holder.item))\n        Ensures(self.holder.item is item)\n        self.holder = Holder(item)\n\ndef run() -> None:\n    first = Item()\n    second = Item()\n    replacement = Item()\n    left = Root(first)\n    right = Root(second)\n    left.holder.set_item(replacement)\n    Assert(right.holder.item == second)\n",
        &[
            "Item.__init__",
            "Holder.__init__",
            "Holder.set_item",
            "Root.__init__",
            "run",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_does_not_frame_a_known_or_unknown_alias_receiver() {
    let known_alias = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n    def set_item(self, item: Item) -> None:\n        Requires(Acc(self.item))\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\nclass Pair:\n    first: Holder\n    second: Holder\n    def __init__(self, holder: Holder) -> None:\n        Ensures(Acc(self.first))\n        Ensures(Acc(self.second))\n        Ensures(self.first is holder)\n        Ensures(self.second is holder)\n        self.first = holder\n        self.second = holder\n\ndef run() -> None:\n    original = Item()\n    replacement = Item()\n    holder = Holder(original)\n    pair = Pair(holder)\n    pair.first.set_item(replacement)\n    Assert(pair.second.item == original)\n",
        &[
            "Item.__init__",
            "Holder.__init__",
            "Holder.set_item",
            "Pair.__init__",
            "run",
        ],
    );
    assert!(
        matches!(known_alias.status, ProofStatus::Refuted),
        "{known_alias:#?}"
    );
    assert_eq!(
        known_alias.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(known_alias.obligations.iter().any(|obligation| {
        obligation.id.starts_with("run:assert:")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));

    let unknown_alias = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def set_item(self, item: Item) -> None:\n        Requires(Acc(self.item))\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n\ndef run(left: Holder, right: Holder) -> None:\n    Requires(Acc(left.item))\n    Requires(Acc(right.item))\n    original = Item()\n    replacement = Item()\n    right.item = original\n    left.set_item(replacement)\n    Assert(right.item == original)\n",
        &["Item.__init__", "Holder.set_item", "run"],
    );
    assert!(
        !matches!(unknown_alias.status, ProofStatus::Proved),
        "{unknown_alias:#?}"
    );
    assert!(
        !unknown_alias.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refuses_star_import_rebinding_of_the_pure_decorator() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("attacker.py"),
        "class Pure:\n    pass\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import Pure\nfrom attacker import *\n\nclass Item:\n    pass\n\n@Pure\ndef id(value: Item) -> Item:\n    return value\n",
    )
    .unwrap();
    let response = analyze_frontend_request(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "attacker.py".to_owned(),
                language: "python".to_owned(),
                symbols: Vec::new(),
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["id".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code
            == "frontend.python.heap.reference-identity-function-pure-binding-unsupported"
    }));
    assert!(response.files[1].fragment.is_none(), "{response:#?}");
    assert!(
        !response
            .obligations
            .iter()
            .any(|obligation| { obligation.id.starts_with("id:") && obligation.satisfied() })
    );
}

#[test]
fn verifier_refutes_the_exact_final_upstream_nested_calls2_assertion_at_line_84() {
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(".upstream/nagini/tests/functional/verification/test_method_calls.py");
    let exact_prefix = fs::read_to_string(fixture)
        .unwrap()
        .lines()
        .take(84)
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("test_method_calls.py"), exact_prefix).unwrap();
    let response = analyze_frontend_request(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: root.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "test_method_calls.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec![
                "Class1.__init__".to_owned(),
                "Class1.get_c2".to_owned(),
                "Class2.__init__".to_owned(),
                "Class2.get_c1".to_owned(),
                "Class2.get_c1_impure".to_owned(),
                "Class2.set_c1".to_owned(),
                "id".to_owned(),
                "nested_calls2".to_owned(),
            ],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "assert.failed:assertion.false" && diagnostic.line == Some(84)
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("nested_calls2:assert:")
            && obligation.line == 84
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
    for line in [81, 82] {
        assert!(response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("nested_calls2:assert:")
                && obligation.line == line
                && obligation.satisfied()
        }));
    }
}

#[test]
fn verifier_proves_equal_and_refutes_distinct_exact_raw_left_references() {
    let proved = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\ndef run() -> None:\n    right = Item()\n    holder = Holder(right)\n    Assert(holder.item == right)\n",
        &["Item.__init__", "Holder.__init__", "run"],
    );
    assert!(matches!(proved.status, ProofStatus::Proved), "{proved:#?}");
    assert_eq!(
        proved.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        proved.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );

    let refuted = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\ndef run() -> None:\n    left = Item()\n    right = Item()\n    holder = Holder(left)\n    Assert(holder.item == right)\n",
        &["Item.__init__", "Holder.__init__", "run"],
    );
    assert!(
        matches!(refuted.status, ProofStatus::Refuted),
        "{refuted:#?}"
    );
    assert_eq!(
        refuted.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(refuted.obligations.iter().any(|obligation| {
        obligation.id.starts_with("run:assert:")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_refuses_unknown_raw_left_identity_and_refutes_stale_permission() {
    let unknown = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    item: Item\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.item))\n    right = Item()\n    Assert(holder.item == right)\n",
        &["Item.__init__", "run"],
    );
    assert_heap_refusal_without_exported_proof(
        &unknown,
        "frontend.python.heap.assert-reference-equality-raw-left-unsupported",
    );

    let stale = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n    def consume(self, unused: Item) -> None:\n        Requires(Acc(self.item))\n        pass\ndef run() -> None:\n    right = Item()\n    unused = Item()\n    holder = Holder(right)\n    holder.consume(unused)\n    Assert(holder.item == right)\n",
        &["Item.__init__", "Holder.__init__", "Holder.consume", "run"],
    );
    assert!(matches!(stale.status, ProofStatus::Refuted), "{stale:#?}");
    assert_eq!(
        stale.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(stale.obligations.iter().any(|obligation| {
        obligation.id.contains("run:")
            && obligation.id.contains("field-permission:item")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
    assert!(
        !stale.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        })
    );
}

#[test]
fn verifier_refuses_exact_raw_left_equality_with_custom_or_inherited_eq() {
    for source in [
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n    @Pure\n    def __eq__(self, marker: int) -> bool:\n        return True\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\ndef run() -> None:\n    left = Item()\n    right = Item()\n    holder = Holder(left)\n    Assert(holder.item == right)\n",
        "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    @Pure\n    def __eq__(self, marker: int) -> bool:\n        return True\nclass Item(Base):\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\ndef run() -> None:\n    left = Item()\n    right = Item()\n    holder = Holder(left)\n    Assert(holder.item == right)\n",
    ] {
        let response = verify_heap_program(
            source,
            &["Item.__init__", "Item.__eq__", "Holder.__init__", "run"],
        );
        assert_heap_refusal_without_exported_proof(
            &response,
            "frontend.python.heap.assert-reference-equality-mro-unsupported",
        );
    }
}

#[test]
fn verifier_refuses_nonraw_optional_property_scalar_or_dynamic_v40_left_operands() {
    for (source, symbols) in [
        (
            "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    item: Optional[Item]\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.item))\n    right = Item()\n    Assert(holder.item == right)\n",
            vec!["Item.__init__", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    item: Item\n    @property\n    def selected(self) -> Item:\n        Requires(Acc(self.item))\n        return self.item\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.item))\n    right = Item()\n    Assert(holder.selected == right)\n",
            vec!["Item.__init__", "Holder.selected@property", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    count: int\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.count))\n    right = Item()\n    Assert(holder.count == right)\n",
            vec!["Item.__init__", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    item: Item\ndef run(first: Holder, second: Holder, flag: bool) -> None:\n    right = Item()\n    Assert((first if flag else second).item == right)\n",
            vec!["Item.__init__", "run"],
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_exported_proof(
            &response,
            "frontend.python.heap.assert-reference-equality-raw-left-unsupported",
        );
    }
}

#[test]
fn verifier_keeps_nonassert_and_not_equal_reference_comparisons_outside_v40() {
    for source in [
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    item: Item\ndef run(holder: Holder) -> bool:\n    Requires(Acc(holder.item))\n    right = Item()\n    return holder.item == right\n",
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Holder:\n    item: Item\ndef run(holder: Holder) -> None:\n    Requires(Acc(holder.item))\n    right = Item()\n    Assert(holder.item != right)\n",
    ] {
        let response = verify_heap_program(source, &["Item.__init__", "run"]);
        assert_heap_refusal_without_exported_proof(
            &response,
            "frontend.python.heap.reference-equality-unsupported",
        );
    }
}

#[test]
fn verifier_refutes_distinct_exact_raw_left_references_across_a_source_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\nclass Holder:\n    item: Item\n    def __init__(self, item: Item) -> None:\n        Ensures(Acc(self.item))\n        Ensures(self.item is item)\n        self.item = item\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Holder, Item\n\ndef run() -> None:\n    left = Item()\n    right = Item()\n    holder = Holder(left)\n    Assert(holder.item == right)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Item.__init__".to_owned(), "Holder.__init__".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("run:assert:")
            && obligation.line == 8
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "app.py"
            && edge.provider_path == "provider.py"
            && edge.imported_symbols == ["Holder", "Item"]
    }));
}

#[test]
fn verifier_matches_exact_upstream_nullable_receiver_failures() {
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(".upstream/nagini/tests/functional/verification/test_method_calls.py");
    let root = tempfile::tempdir().unwrap();
    fs::copy(&fixture, root.path().join("test_method_calls.py")).unwrap();
    let response = analyze_frontend_request(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: root.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "test_method_calls.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec![
                "Class1.__init__".to_owned(),
                "Class1.get_c2".to_owned(),
                "Class1.get_c2_impure".to_owned(),
                "Class2.__init__".to_owned(),
                "null_test".to_owned(),
                "null_test_pure".to_owned(),
            ],
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    for (line, code) in [
        (92, "call.precondition:assertion.false"),
        (100, "application.precondition:assertion.false"),
    ] {
        assert!(
            response
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.line == Some(line) && diagnostic.code == code }),
            "{response:#?}"
        );
        assert!(
            response.obligations.iter().any(|obligation| {
                obligation.line == line
                    && obligation.id.contains("method-call-receiver-nonnull")
                    && obligation.status == maledictus::vc::ObligationStatus::Refuted
            }),
            "{response:#?}"
        );
    }
}

#[test]
fn verifier_preserves_scalar_ifexp_branch_semantics_in_heap_functions() {
    for (requirement, expected) in [("flag", 1), ("flag == False", 2)] {
        let source = format!(
            "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.count))\n        Ensures(self.count == 0)\n        self.count = 0\n\ndef run(flag: bool) -> None:\n    Requires({requirement})\n    box = Box()\n    selected = 1 if flag else 2\n    Assert(selected == {expected})\n    Assert(box.count == 0)\n"
        );
        let response = verify_heap_program(&source, &["Box.__init__", "run"]);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
        assert_eq!(
            response
                .obligations
                .iter()
                .filter(
                    |obligation| obligation.id.starts_with("run:assert:") && obligation.satisfied()
                )
                .count(),
            2,
            "{response:#?}"
        );
    }
}

#[test]
fn verifier_executes_scalar_statement_if_paths_and_joins() {
    for source in [
        // Path split and scalar assignment join.
        "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.count))\n        self.count = 0\ndef run(flag: bool) -> None:\n    box = Box()\n    selected = 0\n    if flag:\n        selected = 1\n        Assert(selected == 1)\n    else:\n        selected = 2\n        Assert(selected == 2)\n    Assert(selected >= 1)\n",
        // Nested scalar branches.
        "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\ndef run(box: Box, first: bool, second: bool) -> None:\n    Requires(Acc(box.count))\n    selected = 0\n    if first:\n        if second:\n            selected = 1\n        else:\n            selected = 2\n    else:\n        selected = 3\n    Assert(selected >= 1)\n",
        // No-else fallthrough joins the incoming local state.
        "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.count))\n    selected = 0\n    if flag:\n        selected = 1\n    Assert(selected >= 0)\n",
        // Annotated locals retain their declared scalar type across the join.
        "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.count))\n    if flag:\n        selected: int = 1\n    else:\n        selected: int = 2\n    Assert(selected >= 1)\n",
    ] {
        let response = verify_heap_program(source, &["run"]);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
        assert!(response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && obligation.satisfied()
        }));
    }
}

#[test]
fn verifier_joins_base_and_derived_statement_if_reference_locals() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\nclass Derived(Base):\n    pass\nclass Holder:\n    value: Base\n    def __init__(self, value: Base) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value is value)\n        self.value = value\ndef run(base: Base, derived: Derived, flag: bool) -> None:\n    if flag:\n        selected = base\n    else:\n        selected = derived\n    holder = Holder(selected)\n",
        &["Holder.__init__", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "run:heap-function-complete" && obligation.satisfied()
    }));
}

#[test]
fn verifier_executes_guarded_method_calls_on_each_path() {
    for (source, symbols) in [
        (
            // Heap writes and permission-sensitive branch state.
            "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.count))\n    if flag:\n        box.count = 1\n    else:\n        box.count = 2\n    Assert(box.count >= 1)\n",
            vec!["run"],
        ),
        (
            // Calls are effects even when both paths call the same method.
            "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\n    def touch(self, unused: 'Box') -> None:\n        Requires(Acc(self.count))\n        Ensures(Acc(self.count))\n        self.count = self.count\ndef run(box: Box, other: Box, flag: bool) -> None:\n    Requires(Acc(box.count))\n    if flag:\n        box.touch(other)\n    else:\n        box.touch(other)\n",
            vec!["Box.touch", "run"],
        ),
    ]
    .into_iter()
    .skip(1)
    {
        let response = verify_heap_program(source, &symbols);
        assert!(matches!(response.status, ProofStatus::Proved), "{response:#?}");
        assert!(response.diagnostics.is_empty(), "{response:#?}");
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
    }
}

#[test]
fn verifier_proves_post_branch_heap_reads_from_each_guarded_write_path() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.count))\n    if flag:\n        box.count = 1\n    else:\n        box.count = 2\n    Assert(box.count >= 1)\n",
        &["run"],
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
            .filter(|obligation| obligation.id.contains("field-write-permission:count:path:"))
            .count(),
        2,
        "{response:#?}"
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains("assert:") && obligation.satisfied())
            .count(),
        2,
        "{response:#?}"
    );
}

#[test]
fn verifier_refuses_undefined_or_incompatibly_joined_statement_if_locals() {
    for source in [
        "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.count))\n    if flag:\n        selected = 1\n    Assert(selected == 1)\n",
        "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.count))\n    if flag:\n        selected: int = 1\n    Assert(selected == 1)\n",
    ] {
        let response = verify_heap_program(source, &["run"]);
        assert!(
            matches!(response.status, ProofStatus::Refuted),
            "{response:#?}"
        );
        assert!(response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:undefined-local:selected:") && !obligation.satisfied()
        }));
        assert!(
            response.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "expression.undefined:undefined.local.variable"
            }),
            "{response:#?}"
        );
    }

    for (source, code, symbols) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.count))\n    if flag:\n        selected: bool = 1\n    else:\n        selected: bool = False\n",
            "frontend.python.heap.conditional-statement-annotation-type-mismatch",
            vec!["run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.count))\n    if flag:\n        selected = 1\n    else:\n        selected = None\n",
            "frontend.python.heap.conditional-statement-join-type-mismatch",
            vec!["run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Left(Base):\n    pass\nclass Right(Base):\n    pass\ndef run(left: Left, right: Right, flag: bool) -> None:\n    if flag:\n        selected = left\n    else:\n        selected = right\n",
            "frontend.python.heap.conditional-statement-join-type-mismatch",
            vec!["Base.__init__", "run"],
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_exported_proof(&response, code);
    }
}

#[test]
fn verifier_promotes_bool_to_int_in_conditional_branches() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.count))\n        Ensures(self.count == 0)\n        self.count = 0\ndef run(flag: bool) -> None:\n    box = Box()\n    selected = 1 if flag else False\n    Assert(selected >= 0)\n    Assert(box.count == 0)\n",
        &["Box.__init__", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| obligation.id.starts_with("run:assert:") && obligation.satisfied())
            .count(),
        2,
        "{response:#?}"
    );
}

#[test]
fn verifier_supports_nested_effect_free_branch_expressions() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.count))\n        Ensures(self.count == 0)\n        self.count = 0\ndef run(first: bool, second: bool) -> None:\n    box = Box()\n    selected = (1 + 2) if first else ((4 - 1) if second else (6 - 3))\n    Assert(selected == 3)\n    Assert(box.count == 0)\n",
        &["Box.__init__", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|obligation| obligation.id.starts_with("run:assert:") && obligation.satisfied())
            .count(),
        2,
        "{response:#?}"
    );
}

#[test]
fn verifier_joins_nominal_subtypes_and_nested_typed_conditionals() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Left(Base):\n    pass\nclass Right(Base):\n    pass\nclass Holder:\n    value: Base\n    def __init__(self, value: Base) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value is value)\n        self.value = value\ndef run(first: bool, second: bool) -> None:\n    left = Left()\n    right = Right()\n    base = Base()\n    selected = left if first else (right if second else base)\n    holder = Holder(selected)\n",
        &["Base.__init__", "Holder.__init__", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "run:heap-function-complete" && obligation.satisfied()
    }));
}

#[test]
fn verifier_tracks_optional_ifexp_results_and_refutes_unguarded_receiver_use() {
    let response = verify_heap_program(
        "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n    @Pure\n    def get_marker(self) -> int:\n        Requires(Acc(self.marker))\n        return self.marker\ndef run(flag: bool) -> None:\n    item = Item()\n    selected = item if flag else None\n    selected.get_marker()\n",
        &["Item.__init__", "Item.get_marker", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("method-call-receiver-nonnull")
            && obligation.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_executes_a_flow_sensitive_optional_guarded_method_call() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n    def touch(self, unused: 'Item') -> None:\n        Requires(Acc(self.marker))\n        Ensures(Acc(self.marker))\n        self.marker = self.marker\ndef run(flag: bool) -> None:\n    item = Item()\n    selected = item if flag else None\n    if selected is not None:\n        selected.touch(item)\n",
        &["Item.__init__", "Item.touch", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|item| {
        item.id.contains("run:method-call-precondition:touch") && item.satisfied()
    }));
}

#[test]
fn verifier_refuses_ill_typed_or_effectful_ifexp_inputs_without_proof() {
    for (source, code) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\ndef run() -> None:\n    item = Item()\n    selected = item if 1 else item\n",
            "frontend.python.heap.conditional-condition-type-mismatch",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\ndef run(flag: bool) -> None:\n    item = Item()\n    selected = item if flag else 1\n",
            "frontend.python.heap.conditional-branch-type-mismatch",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Item:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\ndef run(flag: bool) -> None:\n    item = Item()\n    selected = Item() if flag else item\n",
            "frontend.python.heap.call-argument-constructor-effects-unsupported",
        ),
    ] {
        let response = verify_heap_program(source, &["Item.__init__", "run"]);
        assert_heap_refusal_without_exported_proof(&response, code);
    }
}

#[test]
fn verifier_preserves_typed_ifexp_joins_across_a_source_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\nclass Derived(Base):\n    pass\nclass Holder:\n    value: Base\n    def __init__(self, value: Base) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value is value)\n        self.value = value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Base, Derived, Holder\n\ndef run(flag: bool) -> None:\n    base = Base()\n    derived = Derived()\n    selected = derived if flag else base\n    holder = Holder(selected)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Base.__init__".to_owned(), "Holder.__init__".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "run:heap-function-complete" && obligation.satisfied()
    }));
}

#[test]
fn verifier_joins_statement_if_reference_locals_across_a_source_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\nclass Derived(Base):\n    pass\nclass Holder:\n    value: Base\n    def __init__(self, value: Base) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value is value)\n        self.value = value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Base, Derived, Holder\n\ndef run(base: Base, derived: Derived, flag: bool) -> None:\n    if flag:\n        selected = base\n    else:\n        selected = derived\n    holder = Holder(selected)\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Holder.__init__".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "run:heap-function-complete" && obligation.satisfied()
    }));
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "app.py"
            && edge.provider_path == "provider.py"
            && edge.imported_symbols == ["Base", "Derived", "Holder"]
    }));
}

#[test]
fn verifier_joins_checked_external_nominal_values_without_promoting_external_behavior() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Anchor:\n    count: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.count))\n        Ensures(self.count == 0)\n        self.count = 0\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Anchor\nfrom external_api import ExternalCell\n\ndef run(flag: bool) -> None:\n    anchor = Anchor()\n    left = ExternalCell(1)\n    right = ExternalCell(2)\n    if flag:\n        selected = left\n    else:\n        selected = right\n    observed = selected.get()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_api_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass ExternalCell:\n    value: int\n    @ContractOnly\n    def __init__(self, initial: int) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == initial)\n        ...\n    @ContractOnly\n    def get(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        ...\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Anchor.__init__".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "external_api".to_owned(),
            stub_path: "external_api_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source+checked-external-heap-contracts/v64")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .starts_with("run:method-call-precondition:get:")
            && obligation.satisfied()
    }));
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id == "run:heap-function-complete" && obligation.satisfied()
    }));
}

#[test]
fn verifier_joins_bilateral_scalar_and_bool_int_conditional_returns() {
    for (body, minimum) in [
        ("if flag:\n        return 1\n    else:\n        return 2", 1),
        (
            "if flag:\n        return True\n    else:\n        return 2",
            1,
        ),
    ] {
        let source = format!(
            "from nagini_contracts.contracts import *\n\nclass Anchor:\n    count: int\ndef choose(anchor: Anchor, flag: bool) -> int:\n    Requires(Acc(anchor.count))\n    Ensures(Result() >= {minimum})\n    {body}\n"
        );
        let response = verify_heap_program(&source, &["choose"]);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
        assert!(response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("choose:postcondition:") && obligation.satisfied()
        }));
    }
}

#[test]
fn verifier_proves_nominal_and_optional_conditional_returns() {
    let nominal = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Anchor:\n    count: int\nclass Base:\n    marker: int\nclass Derived(Base):\n    pass\ndef choose(anchor: Anchor, left: Base, right: Derived, flag: bool) -> Base:\n    Requires(Acc(anchor.count))\n    if flag:\n        return left\n    else:\n        return right\n",
        &["choose"],
    );
    assert!(
        matches!(nominal.status, ProofStatus::Proved),
        "{nominal:#?}"
    );
    assert!(nominal.diagnostics.is_empty(), "{nominal:#?}");

    let optional = verify_heap_program(
        "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Anchor:\n    count: int\nclass Item:\n    marker: int\ndef choose(anchor: Anchor, item: Item, flag: bool) -> Optional[Item]:\n    Requires(Acc(anchor.count))\n    if flag:\n        return item\n    else:\n        return None\n",
        &["choose"],
    );
    assert!(
        matches!(optional.status, ProofStatus::Proved),
        "{optional:#?}"
    );
    assert!(optional.diagnostics.is_empty(), "{optional:#?}");
}

#[test]
fn verifier_executes_nested_and_mixed_early_return_paths() {
    let nested = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Anchor:\n    count: int\ndef choose(anchor: Anchor, first: bool, second: bool) -> int:\n    Requires(Acc(anchor.count))\n    Ensures(Result() >= 1)\n    if first:\n        if second:\n            return 1\n        else:\n            return 2\n    else:\n        return 3\n",
        &["choose"],
    );
    assert!(matches!(nested.status, ProofStatus::Proved), "{nested:#?}");
    assert_eq!(
        nested.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(nested.obligations.iter().any(|obligation| {
        obligation.id.starts_with("choose:postcondition:") && obligation.satisfied()
    }));

    let mixed = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Anchor:\n    count: int\ndef choose(anchor: Anchor, flag: bool) -> int:\n    Requires(Acc(anchor.count))\n    Ensures(Result() >= 1)\n    if flag:\n        return 1\n    selected = 2\n    return selected\n",
        &["choose"],
    );
    assert!(matches!(mixed.status, ProofStatus::Proved), "{mixed:#?}");
    assert_eq!(
        mixed.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(mixed.obligations.iter().any(|obligation| {
        obligation.id.starts_with("choose:postcondition:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_refutes_a_conditional_return_with_an_unreturned_fallthrough_path() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Anchor:\n    count: int\ndef choose(anchor: Anchor, flag: bool) -> int:\n    Requires(Acc(anchor.count))\n    if flag:\n        return 1\n",
        &["choose"],
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(response.diagnostics.len(), 1, "{response:#?}");
    assert_eq!(
        response.diagnostics[0].code,
        "postcondition.violated:assertion.false"
    );
    assert!(response.obligations.iter().any(|item| {
        item.id
            .starts_with("choose:postcondition:implicit-return:path:")
            && !item.satisfied()
    }));
}

#[test]
fn verifier_proves_statement_conditionals_beyond_the_former_path_set_boundary() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Anchor:\n    count: int\ndef choose(anchor: Anchor, first: bool, stop: bool, a: bool, b: bool, c: bool, d: bool, e: bool, f: bool) -> int:\n    Requires(Acc(anchor.count))\n    if first:\n        if stop:\n            return 0\n    if a:\n        selected_a = 1\n    else:\n        selected_a = 2\n    if b:\n        selected_b = 1\n    else:\n        selected_b = 2\n    if c:\n        selected_c = 1\n    else:\n        selected_c = 2\n    if d:\n        selected_d = 1\n    else:\n        selected_d = 2\n    if e:\n        selected_e = 1\n    else:\n        selected_e = 2\n    if f:\n        selected_f = 1\n    else:\n        selected_f = 2\n    return 1\n",
        &["choose"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn verifier_guards_branch_obligations_and_postconditions_by_the_evaluated_path() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Anchor:\n    count: int\ndef choose(anchor: Anchor, flag: bool) -> int:\n    Requires(Acc(anchor.count))\n    Ensures(Result() >= 1)\n    if flag:\n        Assert(flag)\n        return 1\n    else:\n        Assert(flag == False)\n        return 2\n",
        &["choose"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(
                |obligation| obligation.id.starts_with("choose:assert:") && obligation.satisfied()
            )
            .count(),
        2,
        "{response:#?}"
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("choose:postcondition:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_proves_conditional_early_returns_across_a_source_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Anchor:\n    count: int\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Anchor\n\ndef choose(anchor: Anchor, flag: bool) -> int:\n    Requires(Acc(anchor.count))\n    Ensures(Result() >= 1)\n    if flag:\n        return 1\n    else:\n        return 2\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: Vec::new(),
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["choose".to_owned()],
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
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("choose:postcondition:") && obligation.satisfied()
    }));
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "app.py"
            && edge.provider_path == "provider.py"
            && edge.imported_symbols == ["Anchor"]
    }));
}

#[test]
fn verifier_executes_differing_branch_writes_and_source_calls_path_locally() {
    for (source, symbols) in [
        (
            // Same receiver and field, including the desired post-state assertion.
            "from nagini_contracts.contracts import *\n\nclass Box:\n    value: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.value))\n    if flag:\n        box.value = 1\n    else:\n        box.value = 2\n",
            vec!["run"],
        ),
        (
            // Different fields cannot be merged as one guarded effect.
            "from nagini_contracts.contracts import *\n\nclass Box:\n    left: int\n    right: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.left))\n    Requires(Acc(box.right))\n    if flag:\n        box.left = 1\n    else:\n        box.right = 1\n",
            vec!["run"],
        ),
        (
            // Different receivers cannot be merged as one guarded effect.
            "from nagini_contracts.contracts import *\n\nclass Box:\n    value: int\ndef run(left: Box, right: Box, flag: bool) -> None:\n    Requires(Acc(left.value))\n    Requires(Acc(right.value))\n    if flag:\n        left.value = 1\n    else:\n        right.value = 1\n",
            vec!["run"],
        ),
        (
            // Different effect counts cannot be merged.
            "from nagini_contracts.contracts import *\n\nclass Box:\n    value: int\ndef run(box: Box, flag: bool) -> None:\n    Requires(Acc(box.value))\n    if flag:\n        box.value = 1\n        box.value = 2\n    else:\n        box.value = 3\n",
            vec!["run"],
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
    }
}

#[test]
fn verifier_executes_path_local_constructor_method_result_unit_call_and_write_effects() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def __init__(self, value: int) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == value)\n        self.value = value\n    def read(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n    def touch(self) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = self.value + 1\ndef run(flag: bool) -> None:\n    if flag:\n        cell = Cell(1)\n        observed = cell.read()\n        cell.value = observed + 1\n        cell.touch()\n    else:\n        cell = Cell(2)\n        observed = cell.read()\n        cell.value = observed + 1\n        cell.touch()\n",
        &["Cell.__init__", "Cell.read", "Cell.touch", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|item| {
        item.id.contains("run:method-call-precondition:read:") && item.satisfied()
    }));
    assert!(response.obligations.iter().any(|item| {
        item.id.contains("run:method-call-precondition:touch:") && item.satisfied()
    }));
}

#[test]
fn verifier_keeps_different_branch_writes_as_separate_guarded_effects() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Pair:\n    left: int\n    right: int\ndef run(pair: Pair, flag: bool) -> None:\n    Requires(Acc(pair.left))\n    Requires(Acc(pair.right))\n    Ensures(Acc(pair.left))\n    Ensures(Acc(pair.right))\n    Ensures(Implies(flag, pair.left == 1))\n    Ensures(Implies(not flag, pair.right == 2))\n    if flag:\n        pair.left = 1\n    else:\n        pair.right = 2\n",
        &["run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|item| item.id.starts_with("run:postcondition:") && item.satisfied())
            .count(),
        8,
        "{response:#?}"
    );
}

#[test]
fn verifier_threads_mixed_early_return_and_heap_effect_paths() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\ndef choose(cell: Cell, stop: bool, flag: bool) -> int:\n    Requires(Acc(cell.value))\n    Ensures(Result() >= 0)\n    Ensures(Result() <= 2)\n    if stop:\n        return 0\n    if flag:\n        cell.value = 1\n        return 1\n    else:\n        cell.value = 2\n        return 2\n",
        &["choose"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|item| item.id.starts_with("choose:postcondition:") && item.satisfied())
            .count(),
        6,
        "{response:#?}"
    );
}

#[test]
fn verifier_checks_method_permissions_and_postconditions_on_each_effect_path() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Pair:\n    left: int\n    right: int\n    def bump_left(self) -> None:\n        Requires(Acc(self.left))\n        Ensures(Acc(self.left))\n        self.left = self.left + 1\n    def bump_right(self) -> None:\n        Requires(Acc(self.right))\n        Ensures(Acc(self.right))\n        self.right = self.right + 1\ndef run(pair: Pair, flag: bool) -> None:\n    Requires(Acc(pair.left))\n    Requires(Acc(pair.right))\n    if flag:\n        pair.bump_left()\n    else:\n        pair.bump_right()\n",
        &["Pair.bump_left", "Pair.bump_right", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    for method in ["bump_left", "bump_right"] {
        assert!(response.obligations.iter().any(|item| {
            item.id
                .contains(&format!("run:method-call-precondition:{method}:"))
                && item.satisfied()
        }));
    }
}

#[test]
fn verifier_absorbs_nullable_receiver_and_method_precondition_failures_per_path() {
    let nullable = verify_heap_program(
        "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def touch(self) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = self.value\ndef run(cell: Optional[Cell], flag: bool) -> None:\n    if flag:\n        cell.touch()\n    else:\n        return\n",
        &["Cell.touch", "run"],
    );
    assert!(
        matches!(nullable.status, ProofStatus::Refuted),
        "{nullable:#?}"
    );
    assert!(nullable.obligations.iter().any(|item| {
        item.id.contains(":method-call-receiver-nonnull:touch:")
            && item.status == maledictus::vc::ObligationStatus::Refuted
    }));

    let precondition = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def touch(self) -> None:\n        Requires(Acc(self.value))\n        Requires(self.value > 0)\n        Ensures(Acc(self.value))\n        self.value = self.value\ndef run(cell: Cell, flag: bool) -> None:\n    Requires(Acc(cell.value))\n    if flag:\n        cell.touch()\n        Assert(False)\n    else:\n        return\n",
        &["Cell.touch", "run"],
    );
    assert!(
        matches!(precondition.status, ProofStatus::Refuted),
        "{precondition:#?}"
    );
    assert!(precondition.obligations.iter().any(|item| {
        item.id.contains(":call-precondition:touch:1")
            && item.status == maledictus::vc::ObligationStatus::Refuted
    }));
    assert!(
        !precondition
            .obligations
            .iter()
            .any(|item| item.id.starts_with("run:assert:")),
        "{precondition:#?}"
    );
}

#[test]
fn verifier_preserves_legacy_and_path_effect_semantics_for_equivalent_programs() {
    for body in [
        "cell.value = 7",
        "if flag:\n        cell.value = 7\n    else:\n        cell.value = 7",
    ] {
        let source = format!(
            "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\ndef run(cell: Cell, flag: bool) -> None:\n    Requires(Acc(cell.value))\n    Ensures(Acc(cell.value))\n    Ensures(cell.value == 7)\n    {body}\n"
        );
        let response = verify_heap_program(&source, &["run"]);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
        assert!(
            response
                .obligations
                .iter()
                .any(|item| { item.id.starts_with("run:postcondition:") && item.satisfied() })
        );
    }
}

#[test]
fn verifier_composes_guarded_heap_effect_paths_across_a_source_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def __init__(self, value: int) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == value)\n        self.value = value\n    def bump(self) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = self.value + 1\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Cell\n\ndef run(flag: bool) -> None:\n    if flag:\n        cell = Cell(1)\n        cell.bump()\n    else:\n        cell = Cell(2)\n        cell.value = 4\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: Vec::new(),
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.obligations.iter().any(|item| {
        item.id.contains("run:method-call-precondition:bump:") && item.satisfied()
    }));
}

#[test]
fn verifier_does_not_execute_effects_after_a_returned_guarded_path() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def bump(self) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = self.value + 1\ndef choose(cell: Cell, stop: bool) -> int:\n    Requires(Acc(cell.value))\n    Ensures(Result() >= 0)\n    if stop:\n        return 0\n    cell.bump()\n    return 1\n",
        &["Cell.bump", "choose"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|item| item.id.contains("choose:method-call-precondition:bump:"))
            .count(),
        1,
        "{response:#?}"
    );
    assert!(response.obligations.iter().any(|item| {
        item.id.contains("choose:method-call-precondition:bump:") && item.satisfied()
    }));
}

#[test]
fn verifier_refuses_unmodeled_properties_dynamic_dispatch_and_exceptional_guarded_calls() {
    for (source, symbols) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    @property\n    def selected(self) -> int:\n        Requires(Acc(self.value))\n        return self.value\ndef run(cell: Cell, flag: bool) -> None:\n    Requires(Acc(cell.value))\n    if flag:\n        observed = cell.selected\n    else:\n        observed = 0\n",
            vec!["Cell.selected@property", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def touch(self) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = self.value\ndef run(cell: Cell, flag: bool) -> None:\n    Requires(Acc(cell.value))\n    if flag:\n        getattr(cell, 'touch')()\n",
            vec!["Cell.touch", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Failure(Exception):\n    pass\nclass Cell:\n    value: int\n    def touch(self) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Exsures(Failure, True)\n        self.value = self.value\ndef run(cell: Cell, flag: bool) -> None:\n    Requires(Acc(cell.value))\n    if flag:\n        cell.touch()\n",
            vec!["Cell.touch", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def set_value(self, value: int) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\ndef run(cell: Cell, flag: bool) -> None:\n    Requires(Acc(cell.value))\n    if flag:\n        cell.set_value(1)\n",
            vec!["Cell.set_value", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def read(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n    def set_value(self, value: int) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\ndef run(cell: Cell, other: Cell, flag: bool) -> None:\n    Requires(Acc(cell.value))\n    Requires(Acc(other.value))\n    if flag:\n        cell.set_value(other.read())\n",
            vec!["Cell.read", "Cell.set_value", "run"],
        ),
    ]
    .into_iter()
    .take(3)
    {
        let response = verify_heap_program(source, &symbols);
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{response:#?}"
        );
        assert!(response.files.iter().all(|file| file.fragment.is_none()));
        assert!(response.obligations.is_empty(), "{response:#?}");
        assert!(!response.diagnostics.is_empty(), "{response:#?}");
    }
}

#[test]
fn verifier_executes_a_guarded_direct_method_argument() {
    for (source, symbols) in [
        (
            "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def set_value(self, value: int) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\ndef run(cell: Cell, flag: bool) -> None:\n    Requires(Acc(cell.value))\n    if flag:\n        cell.set_value(1)\n",
            vec!["Cell.set_value", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def read(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n    def set_value(self, value: int) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\ndef run(cell: Cell, other: Cell, flag: bool) -> None:\n    Requires(Acc(cell.value))\n    Requires(Acc(other.value))\n    if flag:\n        cell.set_value(other.read())\n",
            vec!["Cell.read", "Cell.set_value", "run"],
        ),
    ]
    .into_iter()
    .take(1)
    {
        let response = verify_heap_program(source, &symbols);
        assert!(matches!(response.status, ProofStatus::Proved), "{response:#?}");
        assert!(response.diagnostics.is_empty(), "{response:#?}");
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
    }
}

#[test]
fn verifier_refuses_a_nested_effectful_argument_inside_a_guarded_path() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def read(self) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n    def set_value(self, value: int) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        self.value = value\ndef run(cell: Cell, other: Cell, flag: bool) -> None:\n    Requires(Acc(cell.value))\n    Requires(Acc(other.value))\n    if flag:\n        cell.set_value(other.read())\n",
        &["Cell.read", "Cell.set_value", "run"],
    );
    assert_heap_refusal_without_exported_proof(
        &response,
        "frontend.python.heap.conditional-statement-effect-arguments-unsupported",
    );
}

#[test]
fn verifier_refuses_checked_external_effects_inside_guarded_source_paths() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom external_api import ExternalCell\n\nclass Anchor:\n    value: int\ndef run(anchor: Anchor, cell: ExternalCell, flag: bool) -> None:\n    Requires(Acc(anchor.value))\n    if flag:\n        cell.touch()\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_api_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass ExternalCell:\n    value: int\n    @ContractOnly\n    def touch(self) -> None:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        ...\n",
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
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "external_api".to_owned(),
            stub_path: "external_api_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.files.iter().all(|file| file.fragment.is_none()),
        "{response:#?}"
    );
    assert!(response.obligations.is_empty(), "{response:#?}");
    assert!(!response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn verifier_type_checks_reference_field_writes_in_legacy_and_guarded_paths() {
    for body in [
        "holder.value = derived",
        "if flag:\n        holder.value = derived\n    else:\n        holder.value = derived",
    ] {
        let source = format!(
            "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\nclass Derived(Base):\n    pass\nclass Holder:\n    value: Base\ndef run(holder: Holder, derived: Derived, flag: bool) -> None:\n    Requires(Acc(holder.value))\n    {body}\n"
        );
        let response = verify_heap_program(&source, &["run"]);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
    }

    for body in [
        "holder.value = unrelated",
        "if flag:\n        holder.value = unrelated\n    else:\n        holder.value = unrelated",
        "holder.value = None",
        "if flag:\n        holder.value = None\n    else:\n        holder.value = None",
    ] {
        let source = format!(
            "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\nclass Unrelated:\n    marker: int\nclass Holder:\n    value: Base\ndef run(holder: Holder, unrelated: Unrelated, flag: bool) -> None:\n    Requires(Acc(holder.value))\n    {body}\n"
        );
        let response = verify_heap_program(&source, &["run"]);
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "{response:#?}"
        );
        assert!(response.files[0].fragment.is_none(), "{response:#?}");
        assert!(response.obligations.is_empty(), "{response:#?}");
    }
}

#[test]
fn verifier_accepts_none_only_for_optional_reference_fields_in_legacy_and_guarded_paths() {
    for body in [
        "holder.value = None",
        "if flag:\n        holder.value = None\n    else:\n        holder.value = None",
    ] {
        let source = format!(
            "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\nclass Holder:\n    value: Optional[Base]\ndef run(holder: Holder, flag: bool) -> None:\n    Requires(Acc(holder.value))\n    Ensures(Acc(holder.value))\n    {body}\n"
        );
        let response = verify_heap_program(&source, &["run"]);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
        assert_eq!(
            response.files[0].fragment.as_deref(),
            Some("heap-method-contracts/v76")
        );
        assert!(
            response.obligations.iter().any(|item| {
                item.id.starts_with("run:heap-function-complete") && item.satisfied()
            })
        );
    }
}

#[test]
fn verifier_never_treats_an_optional_field_write_receiver_as_unconditionally_nonnull() {
    for body in [
        "holder.value = value",
        "if flag:\n        holder.value = value",
    ] {
        let source = format!(
            "from typing import Optional\nfrom nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\nclass Holder:\n    value: Base\ndef run(holder: Optional[Holder], value: Base, flag: bool) -> None:\n    {body}\n"
        );
        let response = verify_heap_program(&source, &["run"]);
        assert!(
            !matches!(response.status, ProofStatus::Proved),
            "{response:#?}"
        );
        assert!(
            response.files[0].fragment.is_none()
                || response.obligations.iter().any(|item| {
                    item.id.contains("field-receiver-nonnull") && !item.satisfied()
                }),
            "{response:#?}"
        );
    }
}

#[test]
fn verifier_proves_the_exact_upstream_isinstance_narrowing_fixture() {
    let source =
        include_str!("../.upstream/nagini/tests/functional/verification/test_isinstance.py");
    let response = verify_heap_program(source, &["Something.__init__", "main"]);

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("main:postcondition:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_narrows_only_the_true_isinstance_path_and_preserves_its_permission_state() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Base:\n    marker: int\n    def __init__(self, marker: int) -> None:\n        Ensures(Acc(self.marker))\n        Ensures(self.marker == marker)\n        self.marker = marker\nclass Derived(Base):\n    pass\nclass Other:\n    pass\ndef choose(flag: bool) -> int:\n    Ensures(Result() == (7 if flag else 0))\n    value = None  # type: object\n    if flag:\n        value = Derived(7)\n    else:\n        value = Other()\n    if isinstance(value, Base):\n        return value.marker\n    else:\n        return 0\n",
        &["Base.__init__", "choose"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.starts_with("choose:postcondition:") && obligation.satisfied()
    }));
}

#[test]
fn verifier_does_not_invent_field_permission_from_isinstance_narrowing() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Something:\n    value: int\ndef read(value: object) -> int:\n    if isinstance(value, Something):\n        return value.value\n    else:\n        return 0\n",
        &["read"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(response.obligations.iter().any(|obligation| {
        obligation.id.contains("field-permission") && !obligation.satisfied()
    }));
}

#[test]
fn verifier_refuses_noncanonical_isinstance_conditions_without_proof() {
    for (source, diagnostic) in [
        (
            "from nagini_contracts.contracts import *\n\nclass A:\n    marker: int\ndef run(value: object, anchor: A, isinstance: bool) -> int:\n    Requires(Acc(anchor.marker))\n    if isinstance(value, A):\n        return 1\n    return 0\n",
            "frontend.python.heap.conditional-isinstance-shadowed",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass A:\n    marker: int\ndef run(value: object, anchor: A, flag: bool) -> int:\n    Requires(Acc(anchor.marker))\n    if isinstance(value if flag else value, A):\n        return 1\n    return 0\n",
            "frontend.python.heap.conditional-isinstance-value-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass A:\n    marker: int\nclass B:\n    marker: int\ndef run(value: object, anchor: A) -> int:\n    Requires(Acc(anchor.marker))\n    if isinstance(value, (A, B)):\n        return 1\n    return 0\n",
            "frontend.python.heap.conditional-isinstance-classinfo-unsupported",
        ),
    ] {
        let response = verify_heap_program(source, &["run"]);
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "source:\n{source}\n{response:#?}"
        );
        assert!(
            response
                .diagnostics
                .iter()
                .any(|item| item.code == diagnostic),
            "source:\n{source}\n{response:#?}"
        );
        assert!(
            response.files.iter().all(|file| file.fragment.is_none()),
            "source:\n{source}\n{response:#?}"
        );
        assert!(
            response.obligations.is_empty(),
            "source:\n{source}\n{response:#?}"
        );
    }
}

#[test]
fn verifier_negates_isinstance_method_and_short_circuit_statement_conditions_once() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Base:\n    pass\nclass A(Base):\n    ready_value: bool\n    def __init__(self, ready_value: bool) -> None:\n        Ensures(Acc(self.ready_value))\n        Ensures(self.ready_value == ready_value)\n        self.ready_value = ready_value\n    def ready(self) -> bool:\n        Requires(Acc(self.ready_value))\n        Ensures(Acc(self.ready_value))\n        Ensures(Result() == self.ready_value)\n        return self.ready_value\ndef not_isinstance() -> int:\n    Ensures(Result() == 1)\n    value = Base()\n    if not isinstance(value, A):\n        return 1\n    return 0\ndef not_method() -> int:\n    Ensures(Result() == 1)\n    value = A(False)\n    if not value.ready():\n        return 1\n    return 0\ndef nested_not() -> int:\n    Ensures(Result() == 1)\n    value = A(True)\n    if not (False or not value.ready()):\n        return 1\n    return 0\n",
        &[
            "A.__init__",
            "A.ready",
            "not_isinstance",
            "not_method",
            "nested_not",
        ],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    for caller in ["not_isinstance", "not_method", "nested_not"] {
        assert!(response.obligations.iter().any(|item| {
            item.id.starts_with(&format!("{caller}:postcondition:")) && item.satisfied()
        }));
    }
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|item| item.id.contains(":method-call-precondition:ready:"))
            .count(),
        2,
        "each syntactic ready() call must be evaluated exactly once: {response:#?}"
    );
}

#[test]
fn verifier_absorbs_a_failed_negated_condition_call_before_branch_execution() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass A:\n    marker: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 1\n    def consume(self) -> None:\n        Requires(Acc(self.marker))\n        return\n    def ready(self) -> bool:\n        Requires(Acc(self.marker))\n        Ensures(Acc(self.marker))\n        return True\ndef run() -> int:\n    value = A()\n    value.consume()\n    if not value.ready():\n        return 1\n    return 0\n",
        &["A.__init__", "A.consume", "A.ready", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|item| {
                item.id.contains(":method-call-precondition:ready:") && !item.satisfied()
            })
            .count(),
        1,
        "negation must not duplicate or continue after the failed call: {response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .all(|item| { !item.id.starts_with("run:postcondition:") || item.satisfied() })
    );
}

#[test]
fn verifier_executes_read_free_scalar_chained_statement_comparisons() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\ndef inside(value: int) -> int:\n    Requires(value == 2)\n    Ensures(Result() == 2)\n    if 0 < value < 3:\n        return value\n    return 0\ndef outside(value: int) -> int:\n    Requires(value == 4)\n    Ensures(Result() == 0)\n    if 0 < value < 3:\n        return value\n    return 0\ndef bool_int(flag: bool) -> int:\n    Requires(flag)\n    Ensures(Result() == 1)\n    if 0 < flag < 2:\n        return 1\n    return 0\n",
        &["inside", "outside", "bool_int"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    for caller in ["inside", "outside", "bool_int"] {
        assert!(response.obligations.iter().any(|item| {
            item.id.starts_with(&format!("{caller}:postcondition:")) && item.satisfied()
        }));
    }
}

#[test]
fn verifier_refuses_effectful_reading_or_reference_chained_statement_comparisons() {
    for (source, symbols, diagnostic) in [
        (
            "from nagini_contracts.contracts import *\n\nclass A:\n    def one(self) -> int:\n        return 1\ndef run() -> int:\n    value = A()\n    if 0 < value.one() < 2:\n        return 1\n    return 0\n",
            vec!["A.one", "run"],
            "frontend.python.heap.conditional-statement-effects-unsupported",
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass Box:\n    count: int\ndef run(box: Box) -> int:\n    Requires(Acc(box.count))\n    if 0 < box.count < 2:\n        return 1\n    return 0\n",
            vec!["run"],
            "frontend.python.heap.conditional-statement-effects-unsupported",
        ),
        (
            "class A:\n    pass\ndef run(left: A, middle: A, right: A) -> int:\n    if left is middle is right:\n        return 1\n    return 0\n",
            vec!["run"],
            "frontend.python.heap.conditional-statement-chain-type-mismatch",
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_exported_proof(&response, diagnostic);
    }
}

#[test]
fn verifier_refuses_custom_instancecheck_dispatch_without_narrowing_or_proof() {
    for source in [
        "from nagini_contracts.contracts import *\n\nclass Meta(type):\n    def __instancecheck__(cls, value: object) -> bool:\n        return True\nclass A(metaclass=Meta):\n    marker: int\ndef run(value: object) -> int:\n    if isinstance(value, A):\n        return 1\n    return 0\n",
        "from nagini_contracts.contracts import *\n\nclass BaseMeta(type):\n    def __instancecheck__(cls, value: object) -> bool:\n        return True\nclass DerivedMeta(BaseMeta):\n    pass\nclass A(metaclass=DerivedMeta):\n    marker: int\ndef run(value: object) -> int:\n    if isinstance(value, A):\n        return 1\n    return 0\n",
    ] {
        let response = verify_heap_program(source, &["run"]);
        assert_heap_refusal_without_exported_proof(
            &response,
            "invalid.program:illegal.magic.method",
        );
    }
}

#[test]
fn verifier_refuses_checked_external_isinstance_narrowing_without_source_proof() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom external_api import External\n\nclass Anchor:\n    marker: int\ndef run(value: object, anchor: Anchor) -> int:\n    Requires(Acc(anchor.marker))\n    if isinstance(value, External):\n        return 1\n    return 0\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_api_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass External:\n    marker: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        ...\n",
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
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "external_api".to_owned(),
            stub_path: "external_api_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });

    assert_heap_refusal_without_exported_proof(
        &response,
        "frontend.python.heap.conditional-isinstance-target-unsupported",
    );
}

#[test]
fn verifier_matches_the_exact_upstream_short_circuit_fixture_and_refutes_implicit_none() {
    let source = include_str!("../.upstream/nagini/tests/functional/verification/issues/00015.py");
    let response = verify_heap_program(source, &["A.a", "B.b", "test"]);

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(response.diagnostics.len(), 1, "{response:#?}");
    assert_eq!(
        response.diagnostics[0].code,
        "postcondition.violated:assertion.false"
    );
    assert_eq!(response.diagnostics[0].line, Some(22));
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    let implicit_return = response
        .obligations
        .iter()
        .find(|item| {
            item.id
                .starts_with("test:postcondition:implicit-return:path:")
        })
        .expect("the reachable implicit None path must be a typed totality obligation");
    assert_eq!(implicit_return.line, 22);
    assert!(!implicit_return.satisfied(), "{response:#?}");
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|item| {
                item.id
                    .starts_with("test:postcondition:implicit-return:path:")
                    && !item.satisfied()
            })
            .count(),
        1,
        "Nagini reports one reachable implicit-return violation: {response:#?}"
    );
}

#[test]
fn verifier_executes_short_circuit_scalar_method_conditions_left_to_right() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass C:\n    def ready(self) -> bool:\n        Ensures(Result())\n        return True\ndef run_and(flag: bool) -> int:\n    Ensures(Result() == (1 if flag else 0))\n    c = C()\n    if flag and c.ready():\n        return 1\n    return 0\ndef run_or(flag: bool) -> int:\n    Ensures(Result() == 1)\n    c = C()\n    if flag or c.ready():\n        return 1\n    return 0\n",
        &["C.ready", "run_and", "run_or"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|item| { item.id.starts_with("run_and:postcondition:") && item.satisfied() })
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|item| { item.id.starts_with("run_or:postcondition:") && item.satisfied() })
    );
}

#[test]
fn verifier_skips_unreachable_short_circuit_method_preconditions() {
    for source in [
        "from nagini_contracts.contracts import *\n\nclass C:\n    pass\nclass A(C):\n    def check(self) -> bool:\n        Requires(False)\n        return True\ndef run() -> int:\n    Ensures(Result() == 0)\n    value = C()\n    if isinstance(value, A) and value.check():\n        return 1\n    return 0\n",
        "from nagini_contracts.contracts import *\n\nclass A:\n    def check(self) -> bool:\n        Requires(False)\n        return True\ndef run() -> int:\n    Ensures(Result() == 1)\n    value = A()\n    if isinstance(value, A) or value.check():\n        return 1\n    return 0\n",
    ] {
        let response = verify_heap_program(source, &["A.check", "run"]);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "source:\n{source}\n{response:#?}"
        );
        assert!(response.diagnostics.is_empty(), "{response:#?}");
        assert!(
            response
                .obligations
                .iter()
                .all(|item| { !item.id.contains("method-call-precondition") || item.satisfied() })
        );
    }
}

#[test]
fn verifier_does_not_lower_structurally_unsupported_short_circuit_rhs_calls() {
    for (condition, expected) in [
        ("False and value.check(True)", 0),
        ("True or value.check(True)", 1),
    ] {
        let source = format!(
            "from nagini_contracts.contracts import *\n\nclass A:\n    def check(self, flag: bool) -> bool:\n        return flag\ndef run(value: A) -> int:\n    Ensures(Result() == {expected})\n    if {condition}:\n        return 1\n    return 0\n"
        );
        let response = verify_heap_program(&source, &["A.check", "run"]);
        assert!(
            matches!(response.status, ProofStatus::Proved),
            "source:\n{source}\n{response:#?}"
        );
        assert!(response.diagnostics.is_empty(), "{response:#?}");
        assert!(
            response
                .obligations
                .iter()
                .all(|item| { !item.id.contains("method-call-precondition") || item.satisfied() })
        );
    }
}

#[test]
fn verifier_absorbs_a_failed_left_condition_call_before_evaluating_the_right() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass C:\n    def left(self) -> bool:\n        Requires(False)\n        return True\n    def right(self) -> bool:\n        Requires(False)\n        return True\ndef run() -> int:\n    c = C()\n    if c.left() and c.right():\n        return 1\n    return 0\n",
        &["C.left", "C.right", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(response.diagnostics.len(), 1, "{response:#?}");
    assert_eq!(
        response.diagnostics[0].code,
        "call.precondition:insufficient.permission"
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|item| item.id.contains(":call-precondition:left:") && !item.satisfied())
            .count(),
        1,
        "the failed left call must absorb the path before the right call: {response:#?}"
    );
    assert!(
        !response
            .obligations
            .iter()
            .any(|item| item.id.contains(":call-precondition:right:")),
        "the right call must not be evaluated after the left call fails: {response:#?}"
    );
}

#[test]
fn verifier_uses_exact_runtime_dispatch_for_short_circuit_method_atoms() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass C:\n    pass\nclass A(C):\n    def value(self) -> int:\n        return 1\nclass Derived(A):\n    def value(self) -> int:\n        return 2\ndef run() -> int:\n    Ensures(Result() == 0)\n    value = Derived()\n    if isinstance(value, A) and value.value() == 1:\n        return 1\n    return 0\n",
        &["A.value", "Derived.value", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn verifier_rebinds_exact_condition_methods_to_their_captured_module_environment() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nLIMIT = 1\nclass A:\n    def value(self) -> int:\n        return LIMIT\ndef run() -> int:\n    Ensures(Result() == 1)\n    LIMIT = 2\n    value = A()\n    if value.value() == 1:\n        return 1\n    return 0\n",
        &["A.value", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "the callee must use its immutable captured LIMIT, not the caller local: {response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn verifier_does_not_treat_a_nested_call_return_expression_as_a_pure_result_relation() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass A:\n    def helper(self) -> bool:\n        Ensures(not Result())\n        return False\n    def check(self) -> bool:\n        return self.helper()\ndef run() -> int:\n    Ensures(Result() == 0)\n    value = A()\n    if value.check():\n        return 1\n    return 0\n",
        &["A.helper", "A.check", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "a nested call is not an effect-free single-expression relation exposed to callers: {response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|item| { item.id.starts_with("run:postcondition:") && !item.satisfied() })
    );
}

#[test]
fn verifier_checks_read_permissions_on_reachable_condition_method_paths() {
    for (requires_permission, expected_status) in
        [(false, ProofStatus::Refuted), (true, ProofStatus::Proved)]
    {
        let consume_permission = if requires_permission {
            ""
        } else {
            "    value.drop()\n"
        };
        let source = format!(
            "from nagini_contracts.contracts import *\n\nclass C:\n    number: int\nclass A(C):\n    def __init__(self, number: int) -> None:\n        Ensures(Acc(self.number))\n        Ensures(self.number == number)\n        self.number = number\n    def drop(self) -> None:\n        Requires(Acc(self.number))\n        pass\n    def is_one(self) -> bool:\n        Requires(Acc(self.number))\n        Ensures(Acc(self.number))\n        Ensures(Result() == (self.number == 1))\n        return self.number == 1\ndef run() -> int:\n    value = A(1)\n{consume_permission}    if isinstance(value, A) and value.is_one():\n        return 1\n    return 0\n"
        );
        let response = verify_heap_program(&source, &["A.__init__", "A.drop", "A.is_one", "run"]);
        assert!(
            matches!(
                (&response.status, &expected_status),
                (ProofStatus::Refuted, ProofStatus::Refuted)
                    | (ProofStatus::Proved, ProofStatus::Proved)
            ),
            "{response:#?}"
        );
        if requires_permission {
            assert!(response.diagnostics.is_empty(), "{response:#?}");
        } else {
            assert_eq!(response.diagnostics.len(), 1, "{response:#?}");
            assert_eq!(
                response.diagnostics[0].code,
                "call.precondition:insufficient.permission"
            );
        }
        assert!(response.obligations.iter().any(|item| {
            item.id.contains("method-call-precondition:is_one")
                && item.satisfied() == requires_permission
        }));
        let mut ids = response
            .obligations
            .iter()
            .map(|item| item.id.as_str())
            .collect::<Vec<_>>();
        ids.sort_unstable();
        assert!(
            ids.windows(2).all(|pair| pair[0] != pair[1]),
            "every path-local condition-call obligation needs a unique protocol id: {response:#?}"
        );
    }
}

#[test]
fn verifier_refuses_unsafe_virtual_condition_dispatch_without_exporting_proof() {
    for (source, diagnostic, symbols) in [
        (
            "from nagini_contracts.contracts import *\n\nclass A:\n    count: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.count))\n        self.count = 0\n    def check(self) -> bool:\n        Requires(Acc(self.count))\n        Ensures(Acc(self.count))\n        self.count = self.count + 1\n        return True\ndef run() -> int:\n    value = A()\n    if value.check():\n        return 1\n    return 0\n",
            "frontend.python.heap.conditional-method-effects-unsupported",
            vec!["A.__init__", "A.check", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass A:\n    def check(self) -> bool:\n        Exsures(Exception, True)\n        return True\ndef run() -> int:\n    value = A()\n    if value.check():\n        return 1\n    return 0\n",
            "frontend.python.heap.conditional-method-exceptional-unsupported",
            vec!["A.check", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass A:\n    marker: int\ndef run(value: object, isinstance: bool) -> int:\n    if isinstance(value, A) and value.marker == 1:\n        return 1\n    return 0\n",
            "frontend.python.heap.conditional-isinstance-shadowed",
            vec!["run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass A:\n    def check(self, flag: bool) -> bool:\n        return flag\ndef run() -> int:\n    value = A()\n    if value.check(True):\n        return 1\n    return 0\n",
            "frontend.python.heap.conditional-method-arguments-unsupported",
            vec!["A.check", "run"],
        ),
        (
            "from nagini_contracts.contracts import *\n\nclass A:\n    def check(self) -> bool:\n        return True\nclass Derived(A):\n    count: int\n    def check(self) -> bool:\n        Requires(Acc(self.count))\n        Ensures(Acc(self.count))\n        self.count = self.count + 1\n        return True\ndef run() -> int:\n    value = A()\n    if value.check():\n        return 1\n    return 0\n",
            "frontend.python.heap.override-frame-incompatible",
            vec!["A.check", "Derived.check", "run"],
        ),
    ] {
        let response = verify_heap_program(source, &symbols);
        assert_heap_refusal_without_exported_proof(&response, diagnostic);
    }
}

#[test]
fn verifier_treats_only_reachable_nonunit_fallthrough_as_an_implicit_return_failure() {
    let proved = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass A:\n    def one(self) -> int:\n        Ensures(Result() == 1)\n        return 1\ndef run() -> int:\n    value = A()\n    if isinstance(value, A) and value.one() == 1:\n        return 1\n",
        &["A.one", "run"],
    );
    assert!(matches!(proved.status, ProofStatus::Proved), "{proved:#?}");
    assert!(proved.diagnostics.is_empty(), "{proved:#?}");

    let unit = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass A:\n    def ready(self) -> bool:\n        return True\ndef run() -> None:\n    value = A()\n    if value.ready():\n        return\n",
        &["A.ready", "run"],
    );
    assert!(matches!(unit.status, ProofStatus::Proved), "{unit:#?}");
    assert!(unit.diagnostics.is_empty(), "{unit:#?}");

    let no_result_contract = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass A:\n    def one(self) -> int:\n        return 1\ndef run() -> int:\n    value = A()\n    if value.one() == 1:\n        return 1\n",
        &["A.one", "run"],
    );
    assert!(
        matches!(no_result_contract.status, ProofStatus::Proved),
        "a selected exact source single-return body is verified code: {no_result_contract:#?}"
    );

    let unclosed_ingress = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass A:\n    def one(self) -> int:\n        return 1\ndef run(value: A) -> int:\n    Ensures(Result() == 1)\n    if value.one() == 1:\n        return 1\n    return 0\n",
        &["A.one", "run"],
    );
    assert_heap_refusal_without_exported_proof(
        &unclosed_ingress,
        "frontend.python.heap.conditional-method-dispatch-unsupported",
    );
}

#[test]
fn verifier_composes_exact_short_circuit_condition_methods_across_a_source_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass Gate:\n    ready_value: bool\n    def __init__(self, ready_value: bool) -> None:\n        Ensures(Acc(self.ready_value))\n        Ensures(self.ready_value == ready_value)\n        self.ready_value = ready_value\n    def ready(self) -> bool:\n        Requires(Acc(self.ready_value))\n        Ensures(Acc(self.ready_value))\n        Ensures(Result() == self.ready_value)\n        return self.ready_value\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import Gate\n\ndef run_if() -> int:\n    Ensures(Result() == 1)\n    gate = Gate(True)\n    if gate.ready():\n        return 1\n    return 0\n\ndef run_and(flag: bool) -> int:\n    Ensures(Result() == (1 if flag else 0))\n    gate = Gate(True)\n    if flag and gate.ready():\n        return 1\n    return 0\n\ndef run_or(flag: bool) -> int:\n    Ensures(Result() == 1)\n    gate = Gate(True)\n    if flag or gate.ready():\n        return 1\n    return 0\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: Vec::new(),
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec![
                    "run_if".to_owned(),
                    "run_and".to_owned(),
                    "run_or".to_owned(),
                ],
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
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    for caller in ["run_if", "run_and", "run_or"] {
        assert!(response.obligations.iter().any(|item| {
            item.id.starts_with(&format!("{caller}:postcondition:")) && item.satisfied()
        }));
    }
    assert!(response.source_imports.iter().any(|edge| {
        edge.importer_path == "app.py"
            && edge.provider_path == "provider.py"
            && edge.imported_symbols == ["Gate"]
    }));
}

#[test]
fn verifier_refutes_an_exact_imported_condition_result_but_refuses_open_ingress() {
    for (body, expected_status) in [
        (
            "def run() -> int:\n    Ensures(Result() == 1)\n    gate = Gate(False)\n    if gate.ready():\n        return 1\n    return 0\n",
            ProofStatus::Refuted,
        ),
        (
            "def run(gate: Gate) -> int:\n    if gate.ready():\n        return 1\n    return 0\n",
            ProofStatus::Refused,
        ),
    ] {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("provider.py"),
            "from nagini_contracts.contracts import *\n\nclass Gate:\n    ready_value: bool\n    def __init__(self, ready_value: bool) -> None:\n        Ensures(Acc(self.ready_value))\n        Ensures(self.ready_value == ready_value)\n        self.ready_value = ready_value\n    def ready(self) -> bool:\n        Requires(Acc(self.ready_value))\n        Ensures(Acc(self.ready_value))\n        Ensures(Result() == self.ready_value)\n        return self.ready_value\n",
        )
        .unwrap();
        fs::write(
            directory.path().join("app.py"),
            format!(
                "from nagini_contracts.contracts import *\nfrom provider import Gate\n\n{body}"
            ),
        )
        .unwrap();
        let response = maledictus::verify(&ProofRequest {
            schema: PROTOCOL_SCHEMA.to_owned(),
            source_root: directory.path().display().to_string(),
            source_fingerprint: "0".repeat(64),
            proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
            files: vec![
                SourceFile {
                    path: "provider.py".to_owned(),
                    language: "python".to_owned(),
                    symbols: Vec::new(),
                },
                SourceFile {
                    path: "app.py".to_owned(),
                    language: "python".to_owned(),
                    symbols: vec!["run".to_owned()],
                },
            ],
            external_contract_overlays: Vec::new(),
            python_callable_bindings: Vec::new(),
            cross_language_bindings: Vec::new(),
        });

        match expected_status {
            ProofStatus::Refuted => {
                assert!(
                    matches!(response.status, ProofStatus::Refuted),
                    "{response:#?}"
                );
                assert_eq!(
                    response.files[1].fragment.as_deref(),
                    Some("transitive-source-heap-contracts/v64")
                );
                assert!(response.obligations.iter().any(|item| {
                    item.id.starts_with("run:postcondition:") && !item.satisfied()
                }));
            }
            ProofStatus::Refused => {
                assert!(
                    matches!(response.status, ProofStatus::Refused),
                    "{response:#?}"
                );
                assert!(response.diagnostics.iter().any(|item| {
                    item.code == "frontend.python.heap.conditional-method-dispatch-unsupported"
                }));
                assert!(response.files[1].fragment.is_none(), "{response:#?}");
                assert!(
                    response
                        .obligations
                        .iter()
                        .all(|item| !item.id.starts_with("run:")),
                    "{response:#?}"
                );
            }
            _ => unreachable!(),
        }
    }
}

#[test]
fn verifier_refuses_checked_external_condition_method_dispatch_without_source_proof() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom external_api import ExternalGate\n\ndef run(gate: ExternalGate) -> int:\n    Requires(Acc(gate.marker))\n    if gate.ready():\n        return 1\n    return 0\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("external_api_contract.py"),
        "from nagini_contracts.contracts import *\n\nclass ExternalGate:\n    marker: int\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        ...\n    @ContractOnly\n    def ready(self) -> bool:\n        Requires(Acc(self.marker))\n        Ensures(Acc(self.marker))\n        Ensures(Result())\n        ...\n",
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
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
        external_contract_overlays: vec![maledictus::protocol::ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "external_api".to_owned(),
            stub_path: "external_api_contract.py".to_owned(),
            exception_policy: maledictus::protocol::ExternalExceptionPolicy::AssumeNoException,
        }],
    });

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|item| {
            item.code == "frontend.python.heap.conditional-method-dispatch-unsupported"
        }),
        "{response:#?}"
    );
    assert!(response.files[0].fragment.is_none(), "{response:#?}");
    assert!(response.obligations.is_empty(), "{response:#?}");
}

#[test]
fn verifier_proves_a_closed_monomorphic_generic_scalar_class() {
    let response = verify_heap_program(
        "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import *\n\nT = TypeVar('T')\n\nclass Box(Generic[T]):\n    def __init__(self, value: T) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == value)\n        self.value: T = value\n    def get(self) -> T:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Result() == self.value)\n        return self.value\n\ndef run() -> None:\n    box = Box[int](7)\n",
        &["Box.__init__", "Box.get", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id == "run:field-permission:value:0" && obligation.satisfied()
        }),
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id == "run:heap-function-complete" && obligation.satisfied()
        }),
        "{response:#?}"
    );
}

#[test]
fn verifier_proves_upstream_00266_1_generic_bool_shape() {
    let response = verify_heap_program(
        include_str!("../.upstream/nagini/tests/functional/verification/issues/00266_1.py"),
        &["foo.__init__", "foo.bar"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
}

#[test]
fn heap_conformance_matches_exact_upstream_00266_3_reference_return_fixture() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/verification/issues/00266_3.py";
    let result = maledictus::conformance::check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.fixture, fixture);
    assert_eq!(result.expected, result.actual);
    assert!(result.actual.is_empty(), "{result:#?}");
}

#[test]
fn heap_conformance_matches_exact_upstream_00266_2_recursive_source_fixture() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/verification/issues/00266_2.py";
    let result = maledictus::conformance::check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.fixture, fixture);
    assert_eq!(result.expected, result.actual);
    assert!(result.actual.is_empty(), "{result:#?}");
}

#[test]
fn heap_conformance_matches_exact_upstream_00266_provider_fixture() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/verification/resources/import_for_00266.py";
    let result = maledictus::conformance::check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.fixture, fixture);
    assert_eq!(result.expected, result.actual);
    assert!(result.actual.is_empty(), "{result:#?}");
}

#[test]
fn heap_conformance_matches_exact_upstream_relative_import_graph() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/verification/test_relative_import.py",
        "tests/functional/verification/resources/import_for_00269.py",
        "tests/functional/verification/resources/other_import_for_00269.py",
    ] {
        let result =
            maledictus::conformance::check_pinned_heap_fixture(&suite, &pin, fixture).unwrap();

        assert!(result.passed, "{fixture}: {result:#?}");
        assert_eq!(result.fixture, fixture);
        assert_eq!(result.expected, result.actual, "{fixture}: {result:#?}");
    }
}

fn create_pinned_heap_graph(files: &[(&str, &str)]) -> (tempfile::TempDir, std::path::PathBuf) {
    let directory = tempfile::tempdir().unwrap();
    for (relative, source) in files {
        let path = directory.path().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }

    for arguments in [
        vec!["init", "--quiet"],
        vec!["add", "--all"],
        vec![
            "-c",
            "user.name=Maledictus Tests",
            "-c",
            "user.email=maledictus-tests@example.invalid",
            "commit",
            "--quiet",
            "-m",
            "pinned fixture graph",
        ],
    ] {
        let output = std::process::Command::new("git")
            .arg("-C")
            .arg(directory.path())
            .args(arguments)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git fixture setup failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let revision = std::process::Command::new("git")
        .arg("-C")
        .arg(directory.path())
        .args(["rev-parse", "HEAD"])
        .output()
        .unwrap();
    assert!(revision.status.success());
    let revision = String::from_utf8(revision.stdout)
        .unwrap()
        .trim()
        .to_owned();
    let pin_path = directory.path().join("pin.json");
    fs::write(
        &pin_path,
        serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "maledictus-upstream-suite/v1",
            "project": "recursive import test",
            "repository": "https://example.invalid/recursive-import-test.git",
            "tag": "test",
            "commit": revision.clone(),
            "license": "CC0-1.0",
            "test_entrypoint": "tests.py",
            "fixture_roots": ["tests/functional"],
            "fixture_profiles": [{
                "root": "tests/functional",
                "information_flow": "ordinary"
            }],
            "conformance_environment": {
                "python": {"implementation": "cpython", "major": 3, "minor": 12},
                "nagini_tag": "test",
                "nagini_commit": revision,
                "annotation_profiles": [{
                    "root": "tests/functional",
                    "phase": "verification",
                    "backend": "silicon"
                }]
            }
        }))
        .unwrap(),
    )
    .unwrap();
    (directory, pin_path)
}

#[test]
fn heap_conformance_loads_recursive_direct_symbol_imports() {
    let fixture = "tests/functional/verification/issues/client.py";
    let (suite, pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/leaf.py",
            "from nagini_contracts.contracts import *\n\nclass Box:\n    value: bool\n\n    def __init__(self, value: bool) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == value)\n        self.value = value\n\n    @staticmethod\n    def truth() -> 'Box':\n        Ensures(Acc(Result().value))\n        Ensures(Result().value)\n        return Box(True)\n",
        ),
        (
            "tests/functional/verification/resources/middle.py",
            "from resources.leaf import Box\n",
        ),
        (
            fixture,
            "from resources.middle import Box\n\ndef run() -> None:\n    value = Box.truth()\n    assert value.value\n",
        ),
    ]);

    let result =
        maledictus::conformance::check_pinned_heap_fixture(suite.path(), &pin, fixture).unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.fixture, fixture);
    assert!(result.expected.is_empty(), "{result:#?}");
    assert!(result.actual.is_empty(), "{result:#?}");
}

#[test]
fn heap_conformance_refuses_missing_and_cyclic_recursive_symbol_imports() {
    let fixture = "tests/functional/verification/issues/client.py";
    let (missing_suite, missing_pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/middle.py",
            "from resources.missing import Box\n",
        ),
        (fixture, "from resources.middle import Box\n"),
    ]);
    let missing = maledictus::conformance::check_pinned_heap_fixture(
        missing_suite.path(),
        &missing_pin,
        fixture,
    )
    .unwrap_err();
    assert!(missing.contains("resources.missing"), "{missing}");

    let (cyclic_suite, cyclic_pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/left.py",
            "from resources.right import Right\n\nclass Left:\n    pass\n",
        ),
        (
            "tests/functional/verification/resources/right.py",
            "from resources.left import Left\n\nclass Right:\n    pass\n",
        ),
        (
            fixture,
            "from resources.left import Left\n\ndef run(value: Left) -> None:\n    pass\n",
        ),
    ]);
    let cyclic = maledictus::conformance::check_pinned_heap_fixture(
        cyclic_suite.path(),
        &cyclic_pin,
        fixture,
    )
    .unwrap_err();
    assert!(cyclic.to_lowercase().contains("cycle"), "{cyclic}");
}

#[test]
fn heap_conformance_resolves_relative_imports_only_inside_the_verified_package() {
    let fixture = "tests/functional/verification/issues/client.py";
    let (suite, pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/__init__.py",
            "PACKAGE_VERSION = 1\n",
        ),
        (
            "tests/functional/verification/resources/provider.py",
            "from .leaf import truth\n",
        ),
        (
            "tests/functional/verification/resources/leaf.py",
            "from nagini_contracts.contracts import *\n\ndef truth() -> bool:\n    Ensures(Result())\n    return True\n",
        ),
        (
            fixture,
            "from resources.provider import truth\n\ndef run() -> None:\n    assert truth()\n",
        ),
    ]);

    let result =
        maledictus::conformance::check_pinned_heap_fixture(suite.path(), &pin, fixture).unwrap();
    assert!(result.passed, "{result:#?}");
    assert!(result.actual.is_empty(), "{result:#?}");

    let (missing_suite, missing_pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/__init__.py",
            "PACKAGE_VERSION = 1\n",
        ),
        (
            "tests/functional/verification/resources/provider.py",
            "from .missing import truth\n",
        ),
        (
            "tests/functional/verification/missing.py",
            "from nagini_contracts.contracts import *\n\ndef truth() -> bool:\n    Ensures(Result())\n    return True\n",
        ),
        (fixture, "from resources.provider import truth\n"),
    ]);
    let missing = maledictus::conformance::check_pinned_heap_fixture(
        missing_suite.path(),
        &missing_pin,
        fixture,
    )
    .unwrap_err();
    assert!(missing.contains("relative module \"missing\""), "{missing}");
}

#[test]
fn heap_conformance_refuses_relative_import_escape_and_cycles() {
    let fixture = "tests/functional/verification/issues/client.py";
    let (escape_suite, escape_pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/__init__.py",
            "PACKAGE_VERSION = 1\n",
        ),
        (
            "tests/functional/verification/resources/provider.py",
            "from ..outside import truth\n",
        ),
        (fixture, "from resources.provider import truth\n"),
    ]);
    let escape = maledictus::conformance::check_pinned_heap_fixture(
        escape_suite.path(),
        &escape_pin,
        fixture,
    )
    .unwrap_err();
    assert!(
        escape.starts_with("frontend.python.heap.relative-import-beyond-top-level:"),
        "{escape}"
    );

    let (cycle_suite, cycle_pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/__init__.py",
            "PACKAGE_VERSION = 1\n",
        ),
        (
            "tests/functional/verification/resources/left.py",
            "from .right import truth\n",
        ),
        (
            "tests/functional/verification/resources/right.py",
            "from .left import truth\n",
        ),
        (fixture, "from resources.left import truth\n"),
    ]);
    let cycle =
        maledictus::conformance::check_pinned_heap_fixture(cycle_suite.path(), &cycle_pin, fixture)
            .unwrap_err();
    assert!(
        cycle.starts_with("frontend.python.heap.import-cycle:"),
        "{cycle}"
    );
}

#[test]
fn heap_conformance_refuses_a_refuted_provider_through_a_reexport() {
    let fixture = "tests/functional/verification/issues/client.py";
    let (suite, pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/leaf.py",
            "from nagini_contracts.contracts import *\n\nclass Box:\n    value: bool\n\n    def __init__(self, value: bool) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == value)\n        self.value = value\n\n    @staticmethod\n    def truth() -> 'Box':\n        Ensures(Acc(Result().value))\n        Ensures(Result().value)\n        return Box(False)\n",
        ),
        (
            "tests/functional/verification/resources/middle.py",
            "from resources.leaf import Box\n",
        ),
        (
            fixture,
            "from resources.middle import Box\n\ndef run() -> None:\n    value = Box.truth()\n    assert value.value\n",
        ),
    ]);

    let error = maledictus::conformance::check_pinned_heap_fixture(suite.path(), &pin, fixture)
        .unwrap_err();

    assert!(
        error.starts_with("frontend.python.heap.source-module-refuted:"),
        "{error}"
    );
    assert!(error.contains("resources.leaf"), "{error}");
}

#[test]
fn heap_conformance_checks_package_initializers_before_loading_a_provider() {
    let fixture = "tests/functional/verification/issues/client.py";
    let provider = (
        "tests/functional/verification/resources/pkg/provider.py",
        "from nagini_contracts.contracts import *\n\nclass Box:\n    value: bool\n\n    def __init__(self, value: bool) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == value)\n        self.value = value\n\n    @staticmethod\n    def truth() -> 'Box':\n        Ensures(Acc(Result().value))\n        Ensures(Result().value)\n        return Box(True)\n",
    );
    let consumer = (
        fixture,
        "from resources.pkg.provider import Box\n\ndef run() -> None:\n    value = Box.truth()\n    assert value.value\n",
    );
    let (failing_suite, failing_pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/pkg/__init__.py",
            "from nagini_contracts.contracts import *\n\nclass Broken:\n    value: int\n\n    def read(self) -> int:\n        return self.value\n",
        ),
        provider,
        consumer,
    ]);

    let error = maledictus::conformance::check_pinned_heap_fixture(
        failing_suite.path(),
        &failing_pin,
        fixture,
    )
    .unwrap_err();
    assert!(
        error.starts_with("frontend.python.heap.package-initializer-refuted:"),
        "{error}"
    );
    assert!(error.contains("resources.pkg"), "{error}");

    let (passive_suite, passive_pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/pkg/__init__.py",
            "__author__ = 'Maledictus Tests'\nPACKAGE_VERSION = 1\n",
        ),
        provider,
        consumer,
    ]);
    let result = maledictus::conformance::check_pinned_heap_fixture(
        passive_suite.path(),
        &passive_pin,
        fixture,
    )
    .unwrap();

    assert!(result.passed, "{result:#?}");
    assert!(result.expected.is_empty(), "{result:#?}");
    assert!(result.actual.is_empty(), "{result:#?}");
}

#[test]
fn heap_conformance_reexports_the_leaf_provider_nominal_identity() {
    let fixture = "tests/functional/verification/issues/client.py";
    let (suite, pin) = create_pinned_heap_graph(&[
        (
            "tests/functional/verification/resources/leaf.py",
            "from nagini_contracts.contracts import *\n\nclass Item:\n    pass\n\nclass Consumer:\n    marker: int\n\n    def __init__(self) -> None:\n        Ensures(Acc(self.marker))\n        self.marker = 0\n\n    def accept(self, value: Item) -> None:\n        Requires(Acc(self.marker))\n        Ensures(Acc(self.marker))\n",
        ),
        (
            "tests/functional/verification/resources/middle.py",
            "from resources.leaf import Item\n",
        ),
        (
            fixture,
            "from resources.leaf import Consumer\nfrom resources.middle import Item\n\ndef run() -> None:\n    consumer = Consumer()\n    value = Item()\n    consumer.accept(value)\n",
        ),
    ]);

    let result =
        maledictus::conformance::check_pinned_heap_fixture(suite.path(), &pin, fixture).unwrap();

    assert!(result.passed, "{result:#?}");
    assert!(result.expected.is_empty(), "{result:#?}");
    assert!(result.actual.is_empty(), "{result:#?}");
}

#[test]
fn verifier_proves_exact_upstream_00266_3_reference_return_permissions() {
    let response = verify_heap_program(
        include_str!("../.upstream/nagini/tests/functional/verification/issues/00266_3.py"),
        &["foo.__init__", "foo.bar", "client.client_test"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().all(|item| item.satisfied()));
    assert!(response.obligations.iter().any(|item| {
        item.id.starts_with("client.client_test:")
            && item.id.contains("field-permission:value")
            && item.satisfied()
    }));
    assert!(response.obligations.iter().any(|item| {
        item.id.starts_with("client.client_test:native-assert:") && item.satisfied()
    }));
}

#[test]
fn verifier_composes_static_reference_return_permissions_across_a_source_edge() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import *\n\nT = TypeVar('T')\n\nclass Box(Generic[T]):\n    value: T\n\n    def __init__(self, value: T) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value is value)\n        self.value = value\n\n    @staticmethod\n    def truth() -> 'Box[bool]':\n        Ensures(Acc(Result().value))\n        Ensures(Result().value)\n        return Box[bool](True)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from provider import Box\n\ndef run() -> None:\n    instance = Box.truth()\n    assert instance.value\n",
    )
    .unwrap();
    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["Box.__init__".to_owned(), "Box.truth".to_owned()],
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
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
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(response.source_imports.len(), 1, "{response:#?}");
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(response.obligations.iter().any(|item| {
        item.id.starts_with("run:")
            && item.id.contains("field-permission:value")
            && item.satisfied()
    }));
    assert!(
        response
            .obligations
            .iter()
            .any(|item| item.id.starts_with("run:assert:") && item.satisfied())
    );
}

#[test]
fn verifier_refutes_native_assert_after_a_false_static_reference_return() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Box:\n    value: bool\n\n    def __init__(self, value: bool) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == value)\n        self.value = value\n\n    @staticmethod\n    def false_box() -> 'Box':\n        Ensures(Acc(Result().value))\n        Ensures(not Result().value)\n        return Box(False)\n\ndef run() -> None:\n    instance = Box.false_box()\n    assert instance.value\n",
        &["Box.__init__", "Box.false_box", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "assert.failed:assertion.false" && diagnostic.line == Some(19)
    }));
    assert!(response.obligations.iter().any(|item| {
        item.id.starts_with("run:assert:")
            && item.status == maledictus::vc::ObligationStatus::Refuted
    }));
}

#[test]
fn verifier_requires_static_reference_returns_to_transfer_field_permission() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Box:\n    value: bool\n\n    def __init__(self, value: bool) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == value)\n        self.value = value\n\n    @staticmethod\n    def truth() -> 'Box':\n        Ensures(Result().value)\n        return Box(True)\n\ndef run() -> None:\n    instance = Box.truth()\n    assert instance.value\n",
        &["Box.__init__", "Box.truth", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert!(response.obligations.iter().any(|item| {
        item.id.starts_with("run:")
            && item.id.contains("field-permission:value")
            && item.status == maledictus::vc::ObligationStatus::Refuted
    }));
    assert!(
        !response
            .obligations
            .iter()
            .any(|item| item.id.starts_with("run:native-assert:") && item.satisfied())
    );
}

#[test]
fn verifier_refuses_constructor_assert_field_read_before_initialization() {
    let response = verify_heap_program(
        "class Box:\n    value: bool\n\n    def __init__(self) -> None:\n        assert self.value\n        self.value = True\n",
        &["Box.__init__"],
    );

    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.constructor-field-read-before-initialization",
    );
}

#[test]
fn verifier_clears_static_reference_nominal_provenance_on_scalar_reassignment() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Box:\n    value: bool\n\n    def __init__(self, value: bool) -> None:\n        Ensures(Acc(self.value))\n        self.value = value\n\n    @staticmethod\n    def truth() -> 'Box':\n        Ensures(Acc(Result().value))\n        Ensures(Result().value)\n        return Box(True)\n\n    @staticmethod\n    def scalar() -> bool:\n        Ensures(Result())\n        return True\n\ndef run() -> None:\n    instance = Box.truth()\n    instance = Box.scalar()\n    assert instance.value\n",
        &["Box.__init__", "Box.truth", "Box.scalar", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "frontend.python.heap.field-receiver-type-mismatch"
        }),
        "{response:#?}"
    );
    assert!(response.files[0].fragment.is_none(), "{response:#?}");
    assert!(
        !response
            .obligations
            .iter()
            .any(|item| item.id.starts_with("run:native-assert:") && item.satisfied())
    );
}

#[test]
fn verifier_refuses_inconsistent_generic_static_return_specializations() {
    let response = verify_heap_program(
        "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import *\n\nT = TypeVar('T')\n\nclass Box(Generic[T]):\n    value: T\n\n    def __init__(self, value: T) -> None:\n        Ensures(Acc(self.value))\n        self.value = value\n\n    @staticmethod\n    def wrong() -> 'Box[bool]':\n        Ensures(Acc(Result().value))\n        return Box[int](1)\n",
        &["Box.__init__", "Box.wrong"],
    );

    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.return-nominal-type-mismatch",
    );
}

#[test]
fn verifier_substitutes_a_concrete_nominal_typevar_at_constructor_calls() {
    let proved = verify_heap_program(
        "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import *\nT = TypeVar('T')\nclass Item:\n    pass\nclass Holder(Generic[T]):\n    def __init__(self, value: T) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value is value)\n        self.value: T = value\ndef run(item: Item) -> None:\n    holder = Holder[Item](item)\n",
        &["Holder.__init__", "run"],
    );
    assert!(matches!(proved.status, ProofStatus::Proved), "{proved:#?}");
    assert!(proved.diagnostics.is_empty(), "{proved:#?}");

    let wrong = verify_heap_program(
        "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import *\nT = TypeVar('T')\nclass Item:\n    pass\nclass Other:\n    pass\nclass Holder(Generic[T]):\n    def __init__(self, value: T) -> None:\n        Ensures(Acc(self.value))\n        self.value: T = value\ndef run(other: Other) -> None:\n    holder = Holder[Item](other)\n",
        &["Holder.__init__", "run"],
    );
    assert_heap_refusal_without_exported_proof(
        &wrong,
        "frontend.python.heap.constructor-call-nominal-argument-mismatch",
    );
}

#[test]
fn verifier_isolates_multiple_concrete_generic_specializations() {
    let multiple = verify_heap_program(
        "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import *\nT = TypeVar('T')\nclass Box(Generic[T]):\n    def __init__(self, value: T) -> None:\n        Ensures(Acc(self.value))\n        self.value: T = value\ndef run() -> None:\n    left = Box[int](1)\n    right = Box[bool](True)\n",
        &["Box.__init__", "run"],
    );
    assert!(
        matches!(multiple.status, ProofStatus::Proved),
        "{multiple:#?}"
    );
    assert!(multiple.diagnostics.is_empty(), "{multiple:#?}");

    let collection_specialization = verify_heap_program(
        "from typing import Generic, List, TypeVar\nfrom nagini_contracts.contracts import *\nT = TypeVar('T')\nclass Box(Generic[T]):\n    def __init__(self, value: T) -> None:\n        Ensures(Acc(self.value))\n        self.value: T = value\ndef run(values: List[int]) -> None:\n    box = Box[List[int]](values)\n",
        &["Box.__init__", "run"],
    );
    assert!(
        matches!(collection_specialization.status, ProofStatus::Proved),
        "{collection_specialization:#?}"
    );
    assert!(
        collection_specialization.diagnostics.is_empty(),
        "{collection_specialization:#?}"
    );
    assert_eq!(
        collection_specialization.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
}

#[test]
fn verifier_keeps_typevars_out_of_runtime_state_and_rejects_rich_declarations() {
    for (source, diagnostic) in [
        (
            "from typing import TypeVar\nfrom nagini_contracts.contracts import *\nT = TypeVar('Other')\nclass Cell:\n    value: int\ndef run(cell: Cell) -> int:\n    Requires(Acc(cell.value))\n    return cell.value\n",
            "frontend.python.heap.typevar-declaration-name-mismatch",
        ),
        (
            "from typing import TypeVar\nfrom nagini_contracts.contracts import *\nT = TypeVar('T', bound=int)\nclass Cell:\n    value: int\ndef run(cell: Cell) -> int:\n    Requires(Acc(cell.value))\n    return cell.value\n",
            "frontend.python.heap.typevar-declaration-arguments-unsupported",
        ),
        (
            "from typing import TypeVar as TV\nfrom nagini_contracts.contracts import *\nT = TV('T')\nclass Cell:\n    value: int\ndef run(cell: Cell) -> int:\n    Requires(Acc(cell.value))\n    return cell.value\n",
            "frontend.python.heap.typevar-declaration-callee-unsupported",
        ),
        (
            "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import *\nT = TypeVar('T')\nclass Box(Generic[T]):\n    def __init__(self, value: T) -> None:\n        Ensures(Acc(self.value))\n        self.value: T = value\n    def bad(self, value: 'T') -> None:\n        pass\ndef run() -> None:\n    box = Box[int](1)\n",
            "frontend.python.heap.typevar-annotation-unsupported",
        ),
        (
            "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import *\nT = TypeVar('T')\nclass Box(Generic[T]):\n    def __init__(self, value: T) -> None:\n        Ensures(Acc(self.value))\n        self.value: T = value\ndef run() -> None:\n    box = Box[int](1)\n    value = T\n",
            "frontend.python.heap.typevar-runtime-use-unsupported",
        ),
        (
            "from typing import Generic, TypeVar\nfrom nagini_contracts.contracts import *\nT = TypeVar('T')\nclass Box(Generic[T]):\n    def __init__(self, value: T) -> None:\n        Ensures(Acc(self.value))\n        self.value: T = value\ndef run(T: int) -> None:\n    box = Box[int](T)\n",
            "frontend.python.heap.typevar-runtime-use-unsupported",
        ),
    ] {
        let response = verify_heap_program(source, &["run"]);
        assert_heap_refusal_without_any_proof(&response, diagnostic);
    }
}

#[test]
fn verifier_does_not_rebind_imported_pure_scalar_dependencies_to_consumer_globals() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nclass ProviderAnchor:\n    marker: int\n\n@Pure\ndef helper(value: int) -> int:\n    return value + 1\n\n@Pure\ndef exported(value: int) -> int:\n    Ensures(Result() == helper(value))\n    return helper(value)\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import exported\n\nclass AppAnchor:\n    marker: int\n\n@Pure\ndef helper(value: int) -> int:\n    return value\n\ndef run() -> None:\n    observed = exported(0)\n    Assert(observed == 0)\n",
    )
    .unwrap();

    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: Vec::new(),
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "the imported function must retain provider.helper identity: {response:#?}"
    );
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-heap-contracts/v64")
    );
    assert!(
        response.obligations.iter().any(|obligation| {
            obligation.id.starts_with("run:assert:") && !obligation.satisfied()
        })
    );
}

#[test]
fn verifier_keeps_imported_pure_scalar_globals_in_the_provider_environment() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("provider.py"),
        "from nagini_contracts.contracts import *\n\nOFFSET = 1\n\n@Pure\ndef increment(value: int) -> int:\n    Ensures(Result() == value + OFFSET)\n    return value + OFFSET\n",
    )
    .unwrap();
    fs::write(
        directory.path().join("app.py"),
        "from nagini_contracts.contracts import *\nfrom provider import increment\n\nOFFSET = 100\n\ndef run() -> None:\n    observed = increment(41)\n    Assert(observed == 42)\n",
    )
    .unwrap();

    let response = maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![
            SourceFile {
                path: "provider.py".to_owned(),
                language: "python".to_owned(),
                symbols: Vec::new(),
            },
            SourceFile {
                path: "app.py".to_owned(),
                language: "python".to_owned(),
                symbols: vec!["run".to_owned()],
            },
        ],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    });

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "imported function must read provider.OFFSET, not app.OFFSET: {response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[1].fragment.as_deref(),
        Some("transitive-source-scalar-contracts/v33")
    );
}

#[test]
fn verifier_models_bilateral_nested_and_early_return_pure_scalar_if_bodies() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Anchor:\n    value: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == 0)\n        self.value = 0\n\n@Pure\ndef choose(flag: bool, left: int, right: int) -> int:\n    Ensures(Implies(flag, Result() == left))\n    Ensures(Implies(not flag, Result() == right))\n    if flag:\n        return left\n    else:\n        return right\n\n@Pure\ndef nested(outer: bool, inner: bool) -> int:\n    Ensures(Implies(outer and inner, Result() == 1))\n    Ensures(Implies(outer and not inner, Result() == 2))\n    Ensures(Implies(not outer, Result() == 3))\n    if outer:\n        if inner:\n            return 1\n        return 2\n    return 3\n\n@Pure\ndef early(flag: bool, value: int) -> int:\n    Ensures(Implies(flag, Result() == value))\n    Ensures(Implies(not flag, Result() == value + 1))\n    if flag:\n        return value\n    return value + 1\n\ndef run() -> None:\n    anchor = Anchor()\n    Assert(anchor.value == 0)\n    Assert(choose(True, 4, 9) == 4)\n    Assert(choose(False, 4, 9) == 9)\n    Assert(nested(True, False) == 2)\n    Assert(nested(False, True) == 3)\n    Assert(early(True, 7) == 7)\n    Assert(early(False, 7) == 8)\n",
        &["Anchor.__init__", "choose", "nested", "early", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(response.obligations.iter().all(|item| item.satisfied()));
}

#[test]
fn verifier_refutes_a_path_sensitive_pure_scalar_if_postcondition() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Anchor:\n    value: int\n\n@Pure\ndef broken(flag: bool) -> int:\n    Ensures(Result() == 1)\n    if flag:\n        return 1\n    return 2\n",
        &["broken"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|item| { item.id.starts_with("broken:postcondition:") && !item.satisfied() })
    );
}

#[test]
fn verifier_refuses_heap_effects_inside_a_pure_scalar_if_body() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    value: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        self.value = 0\n\n@Pure\ndef broken(flag: bool) -> int:\n    if flag:\n        item = Item()\n        return 1\n    return 2\n",
        &["broken"],
    );

    assert_heap_refusal_without_exported_proof(
        &response,
        "frontend.python.heap.callable-function-effects-unsupported",
    );
}

#[test]
fn verifier_proves_constructor_fields_initialized_on_every_if_path() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    other: int\n    def __init__(self, first: bool, second: bool) -> None:\n        Ensures(Acc(self.value))\n        Ensures(Acc(self.other))\n        Ensures(Implies(first and second, self.value == 1))\n        Ensures(Implies(first and not second, self.value == 2))\n        Ensures(Implies(not first, self.value == 3))\n        if first:\n            if second:\n                self.value = 1\n            else:\n                self.value = 2\n        else:\n            self.value = 3\n        if first:\n            self.other = 4\n        else:\n            self.other = 5\n",
        &["Cell.__init__"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(response.obligations.iter().all(|item| item.satisfied()));
    let ids = response
        .obligations
        .iter()
        .map(|item| item.id.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(ids.len(), response.obligations.len(), "{response:#?}");
}

#[test]
fn verifier_refutes_a_constructor_permission_promised_for_only_one_if_path() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    def __init__(self, flag: bool) -> None:\n        Ensures(Acc(self.value))  # type: ignore\n        if flag:\n            self.value = 1\n",
        &["Cell.__init__"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(response.obligations.iter().any(|item| {
        item.id
            .contains(":constructor-initialization-permission:value:path:")
            && !item.satisfied()
    }));
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "postcondition.violated:insufficient.permission"
        })
    );
}

#[test]
fn verifier_refuses_an_unpromised_constructor_field_missing_on_one_if_path() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def __init__(self, flag: bool) -> None:\n        if flag:\n            self.value = 1\n",
        &["Cell.__init__"],
    );

    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.constructor-fields-uninitialized",
    );
}

#[test]
fn verifier_refuses_incompatible_nominal_constructor_field_branches() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Item:\n    pass\nclass Other:\n    pass\nclass Cell:\n    value: Item\n    def __init__(self, flag: bool) -> None:\n        Ensures(Acc(self.value))\n        if flag:\n            self.value = Item()\n        else:\n            self.value = Other()\n",
        &["Cell.__init__"],
    );

    assert_heap_refusal_without_any_proof(
        &response,
        "frontend.python.heap.constructor-field-nominal-mismatch",
    );
}

#[test]
fn verifier_matches_upstream_definedness_after_constructor_if_paths() {
    let response = verify_heap_program(
        include_str!("../.upstream/nagini/tests/functional/verification/test_definedness.py"),
        &["C.__init__", "double", "client"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|item| {
            item.id
                .contains(":constructor-initialization-permission:argh:path:")
                && !item.satisfied()
                && item.line == 9
        }),
        "{response:#?}"
    );
    assert!(
        response.obligations.iter().any(|item| {
            item.id.starts_with("double:undefined-local:u:") && !item.satisfied() && item.line == 19
        }),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "postcondition.violated:insufficient.permission"
                && diagnostic.line == Some(9)
        }),
        "{response:#?}"
    );
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "expression.undefined:undefined.local.variable"
                && diagnostic.line == Some(19)
        }),
        "{response:#?}"
    );
}

#[test]
fn heap_conformance_matches_backend_neutral_definedness_in_exact_upstream_00252() {
    let repository = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let result = maledictus::conformance::check_pinned_heap_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        "tests/functional/verification/issues/00252.py",
    )
    .unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected.len(), 1, "{result:#?}");
    assert_eq!(
        result.expected[0].code,
        "expression.undefined:undefined.local.variable"
    );
    assert_eq!(result.expected[0].line, 37);
}

#[test]
fn verifier_proves_ordinary_method_if_paths_with_field_effects_and_early_returns() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def __init__(self) -> None:\n        Ensures(Acc(self.value))\n        Ensures(self.value == 0)\n        self.value = 0\n\n    def choose(self, flag: bool) -> int:\n        Requires(Acc(self.value))\n        Ensures(Acc(self.value))\n        Ensures(Implies(flag, Result() == 1 and self.value == 1))\n        Ensures(Implies(not flag, Result() == 2 and self.value == 2))\n        if flag:\n            self.value = 1\n            return self.value\n        self.value = 2\n        return self.value\n\ndef run(flag: bool) -> None:\n    cell = Cell()\n    result = cell.choose(flag)\n    Assert(Implies(flag, result == 1 and cell.value == 1))\n    Assert(Implies(not flag, result == 2 and cell.value == 2))\n",
        &["Cell.choose", "run"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(response.obligations.iter().all(|item| item.satisfied()));
    assert!(
        response
            .obligations
            .iter()
            .any(|item| { item.id.starts_with("Cell.choose:postcondition:1:path:") })
    );
}

#[test]
fn verifier_refutes_an_ordinary_method_if_missing_return_path() {
    let response = verify_heap_program(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    def choose(self, flag: bool) -> int:\n        if flag:\n            return 1\n",
        &["Cell.choose"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(response.obligations.iter().any(|item| {
        item.id
            .starts_with("Cell.choose:postcondition:implicit-return:path:")
            && !item.satisfied()
    }));
}

fn verify_scalar_module(source: &str, symbols: &[&str]) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("module_globals.py"), source).unwrap();
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "module_globals.py".to_owned(),
            language: "python".to_owned(),
            symbols: symbols.iter().map(|symbol| (*symbol).to_owned()).collect(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

#[test]
fn scalar_conformance_matches_exact_upstream_00001_undeclared_exception_boundary() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/verification/issues/00001.py";
    let result = maledictus::conformance::check_pinned_scalar_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.fixture, fixture);
    assert_eq!(result.expected, result.actual);
    assert_eq!(result.actual.len(), 1, "{result:#?}");
    assert_eq!(result.actual[0].code, "exhale.failed:assertion.false");
    assert_eq!(result.actual[0].line, 8);
}

#[test]
fn verifier_blames_an_undeclared_propagated_exception_on_the_caller_boundary() {
    let response = verify_scalar_module(
        concat!(
            "from nagini_contracts.contracts import *\n",
            "\n",
            "def callee() -> None:\n",
            "    Exsures(ValueError, True)\n",
            "    raise ValueError()\n",
            "\n",
            "def wrapper() -> None:\n",
            "    callee()\n",
        ),
        &["callee", "wrapper"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert_eq!(response.diagnostics.len(), 1, "{response:#?}");
    assert_eq!(
        response.diagnostics[0].code,
        "exhale.failed:assertion.false"
    );
    assert_eq!(response.diagnostics[0].line, Some(7));
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("wrapper:exception-undeclared:ValueError:")
            && !obligation.satisfied()
    }));
}

#[test]
fn verifier_does_not_report_declared_or_caught_exceptions_as_undeclared() {
    let response = verify_scalar_module(
        concat!(
            "from nagini_contracts.contracts import *\n",
            "\n",
            "def declared() -> None:\n",
            "    Exsures(ValueError, True)\n",
            "    raise ValueError()\n",
            "\n",
            "def caught() -> None:\n",
            "    try:\n",
            "        raise ValueError()\n",
            "    except ValueError:\n",
            "        pass\n",
        ),
        &["declared", "caught"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert!(!response.obligations.iter().any(|obligation| {
        obligation.id.contains("declared:exception-undeclared:")
            || obligation.id.contains("caught:exception-undeclared:")
    }));
}

#[test]
fn verifier_retains_application_precondition_code_and_operation_location() {
    let response = verify_scalar_module(
        "def broken() -> None:\n    values = b'12'\n    item = values[2]\n",
        &["broken"],
    );

    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(response.diagnostics.len(), 1, "{response:#?}");
    assert_eq!(
        response.diagnostics[0].code,
        "application.precondition:assertion.false"
    );
    assert_eq!(response.diagnostics[0].line, Some(3));
    assert!(response.obligations.iter().any(|obligation| {
        obligation
            .id
            .contains("broken:exception-undeclared:IndexError:application-precondition:")
            && obligation.line == 3
            && !obligation.satisfied()
    }));
}

#[test]
fn scalar_conformance_deduplicates_undeclared_boundary_diagnostics() {
    let source = concat!(
        "#:: ExpectedOutput(exhale.failed:assertion.false)\n",
        "def broken(flag: bool) -> None:\n",
        "    if flag:\n",
        "        raise ValueError()\n",
        "    raise TypeError()\n",
    );
    let result = maledictus::conformance::check_scalar_source(source, "two_raises.py").unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual);
    assert_eq!(result.actual.len(), 1, "{result:#?}");
    assert_eq!(result.actual[0].code, "exhale.failed:assertion.false");
    assert_eq!(result.actual[0].line, 2);
}

#[test]
fn scalar_conformance_matches_exact_upstream_00113_module_list_index() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = "tests/functional/verification/issues/00113.py";
    let result = maledictus::conformance::check_pinned_scalar_fixture(
        &repository.join(".upstream/nagini"),
        &repository.join("conformance/nagini-v1.3.1.json"),
        fixture,
    )
    .unwrap();

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.fixture, fixture);
    assert!(result.expected.is_empty(), "{result:#?}");
    assert!(result.actual.is_empty(), "{result:#?}");
}

#[test]
fn verifier_constant_folds_in_range_module_global_list_indices() {
    let response = verify_scalar_module(
        "from nagini_contracts.contracts import *\n\nVALUES = [10, 20, 30]\nFIRST = VALUES[0]\nLAST = VALUES[-1]\nLOWER_BOUND = VALUES[-3]\n\ndef read_first() -> int:\n    Ensures(Result() == 10)\n    return FIRST\n\ndef read_last() -> int:\n    Ensures(Result() == 30)\n    return LAST\n\ndef read_lower_bound() -> int:\n    Ensures(Result() == 10)\n    return LOWER_BOUND\n",
        &["read_first", "read_last", "read_lower_bound"],
    );

    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.diagnostics.is_empty(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("scalar-nagini-contracts/v44")
    );
    assert!(response.obligations.iter().all(|item| item.satisfied()));
}

#[test]
fn verifier_refuses_non_total_module_global_list_indices_without_panicking() {
    for (name, source, symbol, diagnostic) in [
        (
            "positive-out-of-range",
            "from nagini_contracts.contracts import *\n\nVALUES = [1, 2]\nPICKED = VALUES[2]\n\ndef read() -> int:\n    return 0\n",
            "read",
            "frontend.python.contracts.partial-operation-in-spec",
        ),
        (
            "negative-out-of-range",
            "from nagini_contracts.contracts import *\n\nVALUES = [1, 2]\nPICKED = VALUES[-3]\n\ndef read() -> int:\n    return 0\n",
            "read",
            "frontend.python.contracts.partial-operation-in-spec",
        ),
        (
            "empty",
            "from nagini_contracts.contracts import *\nfrom typing import List\n\nVALUES: List[int] = []\nPICKED = VALUES[0]\n\ndef read() -> int:\n    return 0\n",
            "read",
            "frontend.python.contracts.empty-list-needs-context",
        ),
        (
            "symbolic",
            "from nagini_contracts.contracts import *\n\nVALUES = [1, 2]\n\ndef pick(index: int) -> int:\n    Ensures(Result() == VALUES[index])\n    return 1\n",
            "pick",
            "frontend.python.contracts.partial-operation-in-spec",
        ),
        (
            "i64-min",
            "from nagini_contracts.contracts import *\n\nVALUES = [1, 2]\nPICKED = VALUES[-9223372036854775808]\n\ndef read() -> int:\n    return 0\n",
            "read",
            "frontend.python.integer.out-of-range",
        ),
    ] {
        let response = verify_scalar_module(source, &[symbol]);
        assert!(
            matches!(response.status, ProofStatus::Refused),
            "case {name}: {response:#?}"
        );
        assert_eq!(
            response.diagnostics.first().map(|item| item.code.as_str()),
            Some(diagnostic),
            "case {name}: {response:#?}"
        );
        assert!(
            response.obligations.is_empty(),
            "case {name}: {response:#?}"
        );
    }
}
