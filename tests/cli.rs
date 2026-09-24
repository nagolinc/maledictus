use std::process::Command;
use std::{fs, path::Path};

#[test]
fn capabilities_are_machine_readable_and_honest() {
    let output = Command::new(env!("CARGO_BIN_EXE_maledictus"))
        .arg("capabilities")
        .output()
        .unwrap();

    assert!(output.status.success());
    let document: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(document["verifier"], "maledictus");
    let refinements = document["implementation_refinements"]
        .as_array()
        .expect("implementation refinements must be an array");
    assert_eq!(refinements.len(), 1);
    let full_refinement = refinements
        .iter()
        .find(|refinement| refinement["identity"] == "call-binding-full-aeneas-extraction/v1")
        .expect("full call-binding refinement must be reported");
    assert_eq!(
        full_refinement["identity"],
        "call-binding-full-aeneas-extraction/v1"
    );
    assert_eq!(
        full_refinement["status"],
        "translated-compiled-and-universally-refinement-proved"
    );
    assert_eq!(full_refinement["counts_as_implementation_refinement"], true);
    assert_eq!(
        full_refinement["scope"]["rust_function"],
        "call_binding::bind_call_with_allocator"
    );
    assert_eq!(
        full_refinement["scope"]["production_wrapper"],
        "call_binding::bind_call"
    );
    assert!(full_refinement["scope"]["maximum_parameters"].is_null());
    assert!(full_refinement["scope"]["maximum_expanded_arguments"].is_null());
    assert_eq!(full_refinement["open_obligations"], serde_json::json!([]));
    assert_eq!(document["languages"][0]["status"], "ready");
    assert_eq!(
        document["languages"][0]["fragments"][0],
        "closed-total-functions+safe-builtin-slices/v1"
    );
    assert_eq!(
        document["languages"][0]["fragments"][1],
        "caught-callable-dataclass-boundaries/v1"
    );
    assert_eq!(
        document["languages"][0]["fragments"][2],
        "scalar-nagini-contracts/v44"
    );
    assert_eq!(
        document["languages"][0]["fragments"][3],
        "nominal-reference-contracts/v4"
    );
    assert_eq!(
        document["languages"][0]["fragments"][4],
        "heap-method-contracts/v76"
    );
    let python_fragments = document["languages"][0]["fragments"].as_array().unwrap();
    for expected in [
        "checked-external-scalar-contracts/v26",
        "transitive-source-scalar-contracts/v33",
        "transitive-source+checked-external-scalar-contracts/v33",
        "transitive-source-heap-contracts/v64",
        "transitive-source+checked-external-heap-contracts/v64",
        "python-to-js-primitive-total/v1",
        "python-call-argument-binding/v3",
    ] {
        assert!(
            python_fragments.iter().any(|fragment| fragment == expected),
            "missing Python capability {expected}"
        );
    }
    assert!(
        document["languages"][0]["fragments"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fragment| fragment == "checked-external-nominal-reference-contracts/v4")
    );
    assert!(
        document["languages"][0]["fragments"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fragment| fragment == "dagcert-closed-typed-operations/v3")
    );
    assert!(
        document["languages"][0]["fragments"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fragment| fragment == "python-call-argument-binding/v3")
    );
    assert!(
        document["languages"][0]["fragments"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fragment| fragment == "transitive-source-heap-contracts/v64")
    );
    assert!(
        document["languages"][0]["fragments"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fragment| {
                fragment == "transitive-source+checked-external-heap-contracts/v64"
            })
    );
    assert_eq!(document["languages"][1]["language"], "javascript");
    assert_eq!(document["languages"][1]["status"], "ready");
    assert_eq!(
        document["languages"][1]["compiler"],
        "typescript/5.9.3-checkJs"
    );
    assert_eq!(
        document["languages"][1]["fragments"][0],
        "strict-javascript-jsdoc-closed-total-functions/v11"
    );
    assert_eq!(document["languages"][2]["language"], "typescript");
    assert_eq!(document["languages"][2]["status"], "ready");
    assert_eq!(document["languages"][2]["compiler"], "typescript/5.9.3");
    assert_eq!(
        document["languages"][2]["fragments"][0],
        "strict-typescript-closed-total-functions/v11"
    );
}

#[test]
fn malformed_invocation_uses_usage_exit_status() {
    let output = Command::new(env!("CARGO_BIN_EXE_maledictus"))
        .arg("verify")
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(64));
}

#[test]
fn check_heap_cli_loads_the_exact_recursive_00266_2_source_graph() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new(env!("CARGO_BIN_EXE_maledictus"))
        .args(["conformance", "check-heap", "--suite"])
        .arg(repository.join(".upstream/nagini"))
        .arg("--pin")
        .arg(repository.join("conformance/nagini-v1.3.1.json"))
        .args([
            "--fixture",
            "tests/functional/verification/issues/00266_2.py",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        result["fixture"],
        "tests/functional/verification/issues/00266_2.py"
    );
    assert_eq!(result["passed"], true);
    assert_eq!(result["expected"], serde_json::json!([]));
    assert_eq!(result["actual"], serde_json::json!([]));
}

#[test]
fn analyze_python_emits_source_derived_model() {
    let directory = tempfile::tempdir().unwrap();
    let source_path = directory.path().join("slice.py");
    fs::write(
        &source_path,
        "def take(values: list[int], step: int) -> list[int]:\n    return values[::step]\n",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_maledictus"))
        .arg("analyze-python")
        .arg(&source_path)
        .output()
        .unwrap();

    assert!(output.status.success());
    let document: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(document["functions"][0]["qualified_name"], "take");
    assert_eq!(document["features"][0]["kind"], "slice");
    assert_eq!(
        document["exceptional_effects"][0]["exception_type"],
        "ValueError"
    );
    assert!(Path::new(document["path"].as_str().unwrap()).ends_with("slice.py"));
}
