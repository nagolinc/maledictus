use maledictus::protocol::{
    ExternalExceptionPolicy, ExternalOverlay, PROTOCOL_SCHEMA, ProofRequest, ProofResponse,
    ProofStatus, SourceFile,
};
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};
use maledictus::vc::ObligationStatus;
use std::fs;

fn verify(source: &str) -> HeapContractVerification {
    verify_heap_module(source, "float_conversion.py", &[])
        .unwrap_or_else(|error| panic!("{}: {}", error.code, error.message))
}

fn refuted(verification: &HeapContractVerification, fragment: &str) -> bool {
    verification.obligations.iter().any(|obligation| {
        obligation.id.contains(fragment) && obligation.status == ObligationStatus::Refuted
    })
}

#[test]
fn caught_string_conversion_keeps_normal_and_value_error_paths() {
    let source = "def run(text: str) -> int:\n    try:\n        value = float(text)\n    except ValueError:\n        return 0\n    return 1\n";
    assert!(verify(source).passed);
    for changed in [
        source.replace("        return 0", "        assert False\n        return 0"),
        source.replace("    return 1", "    assert False\n    return 1"),
    ] {
        let result = verify(&changed);
        assert!(refuted(&result, "assert"), "{result:#?}");
    }
}

#[test]
fn uncaught_and_wrongly_caught_string_conversions_refute() {
    for source in [
        "def run(text: str) -> int:\n    float(text)\n    return 1\n",
        "def run(text: str) -> int:\n    value = float(text)\n    return 1\n",
        "def run(text: str) -> float:\n    return float(text)\n",
        "def run(text: str) -> int:\n    try:\n        float(text)\n    except TypeError:\n        return 0\n    return 1\n",
    ] {
        let result = verify(source);
        assert!(
            refuted(&result, "exception-undeclared"),
            "{source}\n{result:#?}"
        );
    }
}

#[test]
fn integer_overflow_is_not_treated_as_a_parse_error() {
    let source = "def run(value: int) -> int:\n    try:\n        converted = float(value)\n    except OverflowError:\n        return 0\n    return 1\n";
    assert!(verify(source).passed);
    let result = verify(&source.replace("except OverflowError", "except ValueError"));
    assert!(refuted(&result, "exception-undeclared"), "{result:#?}");
}

#[test]
fn float_and_bool_inputs_are_total_but_numeric_facts_are_not_invented() {
    for source in [
        "def run(value: float) -> float:\n    return float(value)\n",
        "def run(value: bool) -> float:\n    converted: float = float(value)\n    return converted\n",
    ] {
        let result = verify(source);
        assert!(result.passed, "{result:#?}");
    }
    let result = verify(
        "def run(value: float) -> int:\n    converted = float(value)\n    assert converted == converted\n    return 1\n",
    );
    assert!(
        refuted(&result, "assert"),
        "NaN must remain possible: {result:#?}"
    );
}

#[test]
fn unsupported_owned_argument_calls_are_not_silently_dropped() {
    let source = "from nagini_contracts.contracts import Exsures\n\ndef text(fail: bool) -> str:\n    Exsures(Exception, True)\n    if fail:\n        raise Exception()\n    return '1.0'\n\ndef run(fail: bool) -> int:\n    try:\n        value = float(text(fail))\n    except Exception:\n        return 0\n    return 1\n";
    let error = verify_heap_module(source, "unsupported_argument.py", &[]).unwrap_err();
    assert_eq!(
        error.code,
        "frontend.python.heap.conditional-expression-call-unsupported"
    );
}

fn native_argument(source: &str, precondition: &str) -> ProofResponse {
    let directory = tempfile::tempdir().unwrap();
    let contract = format!(
        "from nagini_contracts.contracts import ContractOnly, Exsures, Requires\n\nclass Reader:\n    @ContractOnly\n    def text(self) -> str:\n        Requires({precondition})\n        Exsures(Exception, True)\n        ...\n"
    );
    fs::write(directory.path().join("reader_contract.py"), contract).unwrap();
    fs::write(directory.path().join("app.py"), source).unwrap();
    maledictus::verify(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "app.py".to_owned(),
            language: "python".to_owned(),
            symbols: vec!["run".to_owned()],
        }],
        external_contract_overlays: vec![ExternalOverlay {
            adapter_path: "app.py".to_owned(),
            module: "native_reader".to_owned(),
            stub_path: "reader_contract.py".to_owned(),
            exception_policy: ExternalExceptionPolicy::DeclaredByExsures,
        }],
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    })
}

#[test]
fn native_argument_failures_and_preconditions_are_preserved() {
    let source = "from native_reader import Reader\n\ndef run(reader: Reader) -> int:\n    try:\n        value = float(reader.text())\n    except Exception:\n        return 0\n    return 1\n";
    let response = native_argument(source, "True");
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    let response = native_argument(
        &source.replace("except Exception", "except ValueError"),
        "True",
    );
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(response.obligations.iter().any(|o|o.id.contains("exception-undeclared") && o.status==ObligationStatus::Refuted));
    let response = native_argument(source, "False");
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
    assert!(
        response
            .obligations
            .iter()
            .any(|o| o.id.contains("precondition") && o.status == ObligationStatus::Refuted)
    );
}

#[test]
fn shadowed_conversion_calls_retain_owned_function_behavior() {
    let result = verify(
        "def float(text: str) -> int:\n    return 7\n\ndef run(text: str) -> int:\n    value = float(text)\n    assert value == 8\n    return value\n",
    );
    assert!(refuted(&result, "assert"), "{result:#?}");
}

#[test]
fn conversion_argument_indices_cannot_erase_lookup_failures() {
    let source = "from typing import List\n\ndef run(index: int) -> int:\n    values: List[str] = ['1.0']\n    try:\n        float(values[index])\n    except ValueError:\n        return 0\n    return 1\n";
    let result = verify_heap_module(source, "partial_argument.py", &[]);
    assert!(
        !result.as_ref().is_ok_and(|v| v.passed),
        "an IndexError was erased: {result:#?}"
    );
    let valid = source.replace("values[index]", "values[0]");
    assert!(verify(&valid).passed);
}

#[test]
fn owned_method_argument_is_evaluated_once_before_both_conversion_outcomes() {
    let source = "from nagini_contracts.contracts import Acc, Requires, Ensures, Old\n\nclass Counter:\n    def __init__(self) -> None:\n        Ensures(Acc(self.count))\n        Ensures(self.count == 0)\n        self.count = 0\n\n    def text(self) -> str:\n        Requires(Acc(self.count))\n        Ensures(Acc(self.count))\n        Ensures(self.count == Old(self.count) + 1)\n        self.count += 1\n        return '1.0'\n\ndef run() -> None:\n    counter = Counter()\n    try:\n        float(counter.text())\n    except ValueError:\n        pass\n    assert counter.count == 1\n";
    let result = verify(source);
    assert!(result.passed, "{result:#?}");
    let result = verify(&source.replace("assert counter.count == 1", "assert counter.count == 2"));
    assert!(refuted(&result, "assert"), "{result:#?}");
}

#[test]
fn dynamic_object_conversion_and_shadowed_exception_identity_refuse() {
    for source in [
        "def run(value: object) -> int:\n    try:\n        float(value)\n    except Exception:\n        return 0\n    return 1\n",
        "class ValueError(Exception):\n    pass\n\ndef run(text: str) -> int:\n    try:\n        float(text)\n    except ValueError:\n        return 0\n    return 1\n",
    ] {
        assert!(
            verify_heap_module(source, "unsupported.py", &[]).is_err(),
            "{source}"
        );
    }
}

#[test]
fn protocol_proves_the_actual_conversion_body_with_strict_types() {
    let source = "def run(text: str) -> int:\n    try:\n        float(text)\n    except ValueError:\n        return 0\n    return 1\n";
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("app.py"), source).unwrap();
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
        external_contract_overlays: vec![],
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    };
    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some());
    fs::write(
        directory.path().join("app.py"),
        source.replace("except ValueError", "except TypeError"),
    )
    .unwrap();
    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Refuted),
        "{response:#?}"
    );
}

#[test]
fn closed_operation_keeps_the_failure_outcome_and_record_field_read() {
    let source = "from dataclasses import dataclass\nfrom dagcert.runtime import operation\n\n@dataclass(frozen=True)\nclass Request:\n    text: str\n\n@dataclass(frozen=True)\nclass Accepted:\n    valid: bool\n\n@dataclass(frozen=True)\nclass Invalid:\n    valid: bool\n\n@operation\ndef run(request: Request) -> Accepted | Invalid:\n    try:\n        float(request.text)\n    except ValueError:\n        return Invalid(False)\n    return Accepted(True)\n";
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("app.py"), source).unwrap();
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
        external_contract_overlays: vec![],
        python_callable_bindings: vec![],
        embedded_external_calls: vec![],
        cross_language_bindings: vec![],
    };
    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Proved),
        "{response:#?}"
    );
    assert!(response.python_typechecker.is_some());
    fs::write(
        directory.path().join("app.py"),
        source.replace("except ValueError", "except TypeError"),
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
            .any(|d| d.code == "frontend.python.dagcert.operation-not-total"
                && d.message.contains("ValueError"))
    );
    let sibling = source.replace(
        "    except ValueError:\n        return Invalid(False)",
        "    except ValueError:\n        float(request.text)\n        return Invalid(False)\n    except Exception:\n        return Invalid(False)",
    );
    fs::write(directory.path().join("app.py"), sibling).unwrap();
    let response = maledictus::verify(&request);
    assert!(
        matches!(response.status, ProofStatus::Refused),
        "{response:#?}"
    );
    assert!(
        response
            .diagnostics
            .iter()
            .any(|d| d.code == "frontend.python.dagcert.operation-not-total"
                && d.message.contains("ValueError"))
    );
}
