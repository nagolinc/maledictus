use std::fs;

use maledictus::protocol::{
    FileResult, PROTOCOL_SCHEMA, ProofRequest, ProofResponse, ProofStatus, SourceFile,
};
use maledictus::solver::discharge;
use maledictus::vc::{
    IntEnumDescriptor, Obligation, ObligationExpectation, ObligationStatus, Sort, Term,
};
use maledictus::{FrontendDisposition, analyze_python_frontend};

fn request_in(directory: &tempfile::TempDir, source: &str, symbols: &[&str]) -> ProofRequest {
    fs::write(directory.path().join("enum_program.py"), source).unwrap();
    ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "enum_program.py".to_owned(),
            language: "python".to_owned(),
            symbols: symbols.iter().map(|symbol| (*symbol).to_owned()).collect(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    }
}

fn verify_frontend(source: &str, symbols: &[&str]) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    let request = request_in(&directory, source, symbols);
    let analysis = analyze_python_frontend(&request);
    let mut response = ProofResponse::refused(&request);
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
    response.obligations = analysis.obligations;
    response.solver = analysis.solver;
    response.diagnostics = analysis.diagnostics;
    response
}

fn verify_issuance(source: &str, symbols: &[&str]) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    maledictus::verify(&request_in(&directory, source, symbols))
}

#[test]
fn frontend_protocol_proves_selected_finite_int_enum_program() {
    let response = verify_frontend(
        "from nagini_contracts.contracts import *\nfrom enum import IntEnum\n\nclass Flag(IntEnum):\n    off = 0\n    on = 1\n\ndef run(value: Flag) -> None:\n    assert value == 0 or value == 1\n    assert Flag.off == 0\n    assert Flag.off is Flag(0)\n",
        &["Flag", "run"],
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
        response.solver.as_ref().unwrap().vc_ir,
        "maledictus-scalar-vc/v27"
    );
}

#[test]
fn frontend_protocol_refutes_false_enum_identity_without_collapsing_to_int() {
    let response = verify_frontend(
        "from nagini_contracts.contracts import *\nfrom enum import IntEnum\n\nclass First(IntEnum):\n    zero = 0\n\nclass Second(IntEnum):\n    zero = 0\n\ndef run() -> None:\n    assert First.zero == Second.zero\n    assert First.zero is Second.zero\n",
        &["run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert_eq!(
        response
            .obligations
            .iter()
            .filter(|item| !item.satisfied())
            .count(),
        1
    );
}

#[test]
fn frontend_protocol_refuses_unmodeled_top_level_effects() {
    let response = verify_frontend(
        "from enum import IntEnum\ndangerous_call()\nclass Flag(IntEnum):\n    off = 0\n",
        &[],
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(!response.diagnostics.is_empty(), "{response:#?}");
}

#[test]
fn production_issuance_proves_int_enum_only_after_strict_python_typecheck() {
    let response = verify_issuance(
        "from nagini_contracts.contracts import *\nfrom enum import IntEnum\n\nclass Flag(IntEnum):\n    off = 0\n    on = 1\n\ndef run(value: Flag) -> None:\n    assert value == 0 or value == 1\n",
        &["Flag", "run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
    assert!(response.verifier_identity.is_some(), "{response:#?}");
    assert_eq!(
        response.files[0].fragment.as_deref(),
        Some("heap-method-contracts/v76")
    );
    assert_eq!(
        response.solver.as_ref().unwrap().vc_ir,
        "maledictus-scalar-vc/v27"
    );
}

#[test]
fn production_issuance_refutes_false_int_enum_value_claim() {
    let response = verify_issuance(
        "from nagini_contracts.contracts import *\nfrom enum import IntEnum\n\nclass Flag(IntEnum):\n    off = 0\n    on = 1\n\ndef run(value: Flag) -> None:\n    Requires(value == Flag.off)\n    assert value == Flag.on\n",
        &["run"],
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
}

#[test]
fn production_issuance_refuses_typechecked_unmodeled_mixed_class() {
    let response = verify_issuance(
        "from enum import IntEnum\n\nclass Flag(IntEnum):\n    off = 0\n\nclass Ordinary:\n    pass\n",
        &[],
    );
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some(), "{response:#?}");
}

fn descriptor(class: &str, values: &[(&str, i64)]) -> IntEnumDescriptor {
    IntEnumDescriptor {
        class: class.to_owned(),
        members: values
            .iter()
            .map(|(name, value)| ((*name).to_owned(), *value))
            .collect(),
    }
}

fn enum_value(descriptor: &IntEnumDescriptor, value: i64) -> Term {
    Term::IntEnumValue {
        descriptor: descriptor.clone(),
        value: Box::new(Term::Int { value }),
    }
}

fn prove(conclusion: Term) -> ObligationStatus {
    discharge(&Obligation {
        id: "int-enum-ir-parity".to_owned(),
        expectation: ObligationExpectation::Prove,
        assumptions: Vec::new(),
        conclusion,
        path: "enum_ir.py".to_owned(),
        byte_offset: 0,
        line: 1,
        column: 1,
    })
    .unwrap()
    .status
}

#[test]
fn solver_ir_matches_finite_domain_projection_and_identity_algebra() {
    let first = descriptor("First", &[("zero", 0), ("one", 1)]);
    let second = descriptor("Second", &[("zero", 0), ("two", 2)]);
    assert_eq!(
        prove(Term::IntEnumDomain {
            value: Box::new(enum_value(&first, 1)),
        }),
        ObligationStatus::Proved
    );
    assert_eq!(
        prove(Term::IntEnumDomain {
            value: Box::new(enum_value(&first, 2)),
        }),
        ObligationStatus::Refuted
    );
    assert_eq!(
        prove(Term::Equal {
            left: Box::new(Term::IntEnumProjection {
                value: Box::new(enum_value(&first, 0)),
            }),
            right: Box::new(Term::IntEnumProjection {
                value: Box::new(enum_value(&second, 0)),
            }),
        }),
        ObligationStatus::Proved
    );
    assert_eq!(
        prove(Term::IntEnumIdentity {
            left: Box::new(enum_value(&first, 0)),
            right: Box::new(enum_value(&second, 0)),
        }),
        ObligationStatus::Refuted
    );
    assert_eq!(
        prove(Term::IntEnumIdentity {
            left: Box::new(enum_value(&first, 1)),
            right: Box::new(enum_value(&first, 1)),
        }),
        ObligationStatus::Proved
    );
}

#[test]
fn vc_rejects_malformed_enum_descriptors_and_erased_identity_inputs() {
    let duplicate = descriptor("Flag", &[("off", 0), ("also_off", 0)]);
    assert!(enum_value(&duplicate, 0).sort().is_err());
    assert!(
        Term::IntEnumIdentity {
            left: Box::new(Term::Int { value: 0 }),
            right: Box::new(Term::Int { value: 0 }),
        }
        .sort()
        .is_err()
    );
    assert_eq!(
        enum_value(&descriptor("Flag", &[("off", 0)]), 0).sort(),
        Ok(Sort::Int)
    );
}

#[test]
fn solver_identity_requires_the_complete_descriptor_not_only_its_class_name() {
    let first = descriptor("Flag", &[("zero", 0), ("one", 1)]);
    let incompatible = descriptor("Flag", &[("zero", 0), ("two", 2)]);
    assert_eq!(
        prove(Term::IntEnumIdentity {
            left: Box::new(enum_value(&first, 0)),
            right: Box::new(enum_value(&incompatible, 0)),
        }),
        ObligationStatus::Refuted
    );
}
