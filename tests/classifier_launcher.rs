#![cfg(windows)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use sha2::{Digest, Sha256};

fn run_git(root: &Path, arguments: &[&str]) -> String {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(arguments)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "git {arguments:?} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}

fn create_pinned_suite() -> (tempfile::TempDir, PathBuf) {
    let directory = tempfile::tempdir().unwrap();
    let fixture = directory.path().join("tests/functional/a.py");
    fs::create_dir_all(fixture.parent().unwrap()).unwrap();
    fs::write(fixture, "").unwrap();
    run_git(directory.path(), &["init", "--quiet"]);
    run_git(directory.path(), &["add", "--all"]);
    run_git(
        directory.path(),
        &[
            "-c",
            "user.name=Maledictus Tests",
            "-c",
            "user.email=maledictus-tests@example.invalid",
            "commit",
            "--quiet",
            "-m",
            "classifier launcher suite",
        ],
    );
    let commit = run_git(directory.path(), &["rev-parse", "HEAD"]);
    let pin = directory.path().join("pin.json");
    fs::write(
        &pin,
        serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "maledictus-upstream-suite/v1",
            "project": "classifier launcher test",
            "repository": "https://example.invalid/classifier-launcher.git",
            "tag": "test",
            "commit": commit.clone(),
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
                "nagini_commit": commit,
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
    (directory, pin)
}

fn sha256_file(path: &Path) -> String {
    format!("{:x}", Sha256::digest(fs::read(path).unwrap()))
}

fn launcher_command(suite: &Path, pin: &Path, libz3: &Path, cache: &Path) -> Command {
    let mut command = Command::new("powershell.exe");
    command
        .args(["-NoProfile", "-ExecutionPolicy", "Bypass", "-File"])
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("scripts/classify-suite.ps1"))
        .arg("-Executable")
        .arg(env!("CARGO_BIN_EXE_maledictus"))
        .arg("-LibZ3")
        .arg(libz3)
        .arg("-Suite")
        .arg(suite)
        .arg("-Pin")
        .arg(pin)
        .arg("-CacheRoot")
        .arg(cache)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    command
}

fn assert_successful_report(output: &Output) -> serde_json::Value {
    assert!(
        output.status.success(),
        "launcher failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["total"], 1);
    report
}

#[test]
fn launcher_writes_a_valid_report_only_below_repository_cache() {
    let (suite, pin) = create_pinned_suite();
    let repository_cache = Path::new(env!("CARGO_MANIFEST_DIR")).join(".cache");
    fs::create_dir_all(&repository_cache).unwrap();
    let disposable = tempfile::Builder::new()
        .prefix("classifier-report-")
        .tempdir_in(&repository_cache)
        .unwrap();
    let binary_cache = disposable.path().join("classifier-bin");
    let report_path = disposable.path().join("reports/classification.json");
    let libz3 = Path::new(env!("CARGO_MANIFEST_DIR")).join("z3-5.1.0/bin/libz3.dll");

    let output = launcher_command(suite.path(), &pin, &libz3, &binary_cache)
        .arg("-Output")
        .arg(&report_path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "launcher failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stdout.is_empty(),
        "captured report leaked to stdout: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    let report: serde_json::Value =
        serde_json::from_slice(&fs::read(&report_path).unwrap()).unwrap();
    assert_eq!(report["total"], 1);

    let outside = tempfile::tempdir().unwrap();
    let refused_path = outside.path().join("classification.json");
    let refused = launcher_command(suite.path(), &pin, &libz3, &binary_cache)
        .arg("-Output")
        .arg(&refused_path)
        .output()
        .unwrap();
    assert!(
        !refused.status.success(),
        "launcher wrote a report outside repository .cache"
    );
    assert!(!refused_path.exists());
}

#[test]
fn concurrent_launchers_publish_and_reuse_one_runnable_content_snapshot() {
    let (suite, pin) = create_pinned_suite();
    let repository_cache = Path::new(env!("CARGO_MANIFEST_DIR")).join(".cache");
    fs::create_dir_all(&repository_cache).unwrap();
    let disposable = tempfile::Builder::new()
        .prefix("classifier-launcher-")
        .tempdir_in(&repository_cache)
        .unwrap();
    let binary_cache = disposable.path().join("classifier-bin");
    let executable = Path::new(env!("CARGO_BIN_EXE_maledictus"));
    let libz3 = Path::new(env!("CARGO_MANIFEST_DIR")).join("z3-5.1.0/bin/libz3.dll");

    let first = launcher_command(suite.path(), &pin, &libz3, &binary_cache)
        .spawn()
        .unwrap();
    let second = launcher_command(suite.path(), &pin, &libz3, &binary_cache)
        .spawn()
        .unwrap();
    let first_output = first.wait_with_output().unwrap();
    let second_output = second.wait_with_output().unwrap();
    let first_report = assert_successful_report(&first_output);
    let second_report = assert_successful_report(&second_output);
    assert_eq!(first_report, second_report);

    let executable_sha = sha256_file(executable);
    let snapshot = binary_cache.join(executable_sha);
    assert_eq!(
        sha256_file(&snapshot.join("maledictus.exe")),
        sha256_file(executable)
    );
    assert_eq!(
        sha256_file(&snapshot.join("libz3.dll")),
        sha256_file(&libz3)
    );
    assert!(snapshot.join("snapshot.json").is_file());
    let children = fs::read_dir(&binary_cache)
        .unwrap()
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    assert_eq!(children.len(), 1, "staging output survived publication");

    let conflicting_libz3 = suite.path().join("libz3.dll");
    fs::copy(&libz3, &conflicting_libz3).unwrap();
    let mut conflicting_bytes = fs::read(&conflicting_libz3).unwrap();
    conflicting_bytes.push(0);
    fs::write(&conflicting_libz3, conflicting_bytes).unwrap();
    let conflict = launcher_command(suite.path(), &pin, &conflicting_libz3, &binary_cache)
        .output()
        .unwrap();
    assert!(
        !conflict.status.success(),
        "same executable identity accepted different Z3 bytes"
    );

    let reused_output = launcher_command(suite.path(), &pin, &libz3, &binary_cache)
        .output()
        .unwrap();
    assert_eq!(assert_successful_report(&reused_output), first_report);
    assert_eq!(
        fs::read_dir(&binary_cache).unwrap().count(),
        1,
        "reuse published another snapshot"
    );
}
