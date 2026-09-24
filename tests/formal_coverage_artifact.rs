use std::fs;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

fn project_path(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(relative)
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn collect_rust_sources(directory: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_rust_sources(&path, files);
        } else if path.extension().and_then(|extension| extension.to_str()) == Some("rs") {
            files.push(path);
        }
    }
}

fn source_tree_hash() -> String {
    let project = project_path("");
    let mut files = Vec::new();
    collect_rust_sources(&project.join("src"), &mut files);
    files.sort();
    let mut digest = Sha256::new();
    for file in files {
        let relative = file
            .strip_prefix(&project)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        digest.update(relative.as_bytes());
        digest.update([0]);
        digest.update(fs::read(file).unwrap());
        digest.update([0]);
    }
    format!("{:x}", digest.finalize())
}

#[test]
fn formal_coverage_denominator_is_current_and_arithmetically_honest() {
    let coverage: serde_json::Value =
        serde_json::from_slice(&fs::read(project_path("formal/coverage.json")).unwrap()).unwrap();

    assert_eq!(coverage["schema"], "maledictus-formal-coverage/v2");
    assert_eq!(coverage["root"]["symbol"], "maledictus::verify_internal");
    assert_eq!(coverage["root"]["source_tree_sha256"], source_tree_hash());

    for identity in ["generator", "config"] {
        let path_key = if identity == "generator" {
            "path"
        } else {
            "config_path"
        };
        let hash_key = if identity == "generator" {
            "sha256"
        } else {
            "config_sha256"
        };
        let relative = coverage["generator"][path_key].as_str().unwrap();
        assert_eq!(
            coverage["generator"][hash_key],
            sha256(&fs::read(project_path(relative)).unwrap()),
            "formal coverage {identity} changed without regeneration"
        );
    }

    let metrics = &coverage["metrics"];
    let unconditional = metrics["source_unconditional_proved"].as_u64().unwrap();
    let conditional = metrics["source_conditional_proved"].as_u64().unwrap();
    let model_only = metrics["source_model_only"].as_u64().unwrap();
    let unproved = metrics["source_unproved"].as_u64().unwrap();
    let total = metrics["source_total"].as_u64().unwrap();
    assert_eq!(unconditional + conditional + model_only + unproved, total);
    assert_eq!(
        coverage["source_nodes"].as_array().unwrap().len() as u64,
        total
    );

    for node in coverage["source_nodes"].as_array().unwrap() {
        match node["basis"].as_str().unwrap() {
            "unconditional-source-bound" | "conditional-source-bound" => {
                let proof = &node["proof"];
                assert_eq!(proof["current_source_hash_matches"], true);
                assert_eq!(proof["counts_as_implementation_refinement"], true);
                assert_eq!(proof["proof_obligations_closed"], true);
                assert_eq!(proof["axiom_audit_clean"], true);
            }
            "unproved" => assert!(node["proof"].is_null()),
            other => panic!("unexpected source-node basis {other:?}"),
        }
    }

    for model in coverage["model_only_artifacts"].as_array().unwrap() {
        assert_eq!(model["basis"], "model-only");
        assert_eq!(model["counts_toward_source_numerator"], false);
    }

    assert_eq!(metrics["root_composition_proved"], false);
    assert_eq!(metrics["whole_type_system_formally_proven"], false);
}
