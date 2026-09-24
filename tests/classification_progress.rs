use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use maledictus::conformance::{
    ClassificationLane, ClassificationProgressEvent, classify_pinned_combined_suite,
    classify_pinned_combined_suite_parallel_with_progress_and_cache,
    classify_pinned_combined_suite_with_progress,
};

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
    let fixture_root = directory.path().join("tests/functional");
    fs::create_dir_all(&fixture_root).unwrap();
    fs::write(fixture_root.join("a.py"), "").unwrap();
    fs::write(fixture_root.join("b.py"), "").unwrap();

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
            "pinned classification suite",
        ],
    );
    let commit = run_git(directory.path(), &["rev-parse", "HEAD"]);
    let pin = directory.path().join("pin.json");
    fs::write(
        &pin,
        serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "maledictus-upstream-suite/v1",
            "project": "classification progress test",
            "repository": "https://example.invalid/classification-progress.git",
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

fn repository_cache_directory(prefix: &str) -> tempfile::TempDir {
    let cache = Path::new(env!("CARGO_MANIFEST_DIR")).join(".cache");
    fs::create_dir_all(&cache).unwrap();
    tempfile::Builder::new()
        .prefix(prefix)
        .tempdir_in(cache)
        .unwrap()
}

#[test]
fn progress_observer_reports_every_fixture_and_lane_without_changing_the_report() {
    let (suite, pin) = create_pinned_suite();
    let mut events = Vec::new();
    let observed = classify_pinned_combined_suite_with_progress(suite.path(), &pin, &mut |event| {
        events.push(event)
    })
    .unwrap();
    let silent = classify_pinned_combined_suite(suite.path(), &pin).unwrap();

    assert_eq!(observed, silent);
    assert_eq!(observed.total, 2);
    assert_eq!(events.len(), 9);
    for (lane_index, lane) in [
        ClassificationLane::Scalar,
        ClassificationLane::Heap,
        ClassificationLane::Reference,
    ]
    .into_iter()
    .enumerate()
    {
        let offset = lane_index * 3;
        assert_eq!(
            events[offset],
            ClassificationProgressEvent::FixtureStarted {
                lane,
                root: "tests/functional".to_owned(),
                fixture: "tests/functional/a.py".to_owned(),
                ordinal: 1,
                total: 2,
            }
        );
        assert_eq!(
            events[offset + 1],
            ClassificationProgressEvent::FixtureStarted {
                lane,
                root: "tests/functional".to_owned(),
                fixture: "tests/functional/b.py".to_owned(),
                ordinal: 2,
                total: 2,
            }
        );
        assert_eq!(
            events[offset + 2],
            ClassificationProgressEvent::LaneCompleted {
                lane,
                root: "tests/functional".to_owned(),
                total: 2,
            }
        );
    }
}

#[test]
fn parallel_progress_is_complete_and_ordered_inside_each_lane() {
    let (suite, pin) = create_pinned_suite();
    let cache = repository_cache_directory("classification-progress-parallel-");
    let mut events = Vec::new();
    let caller = std::thread::current().id();
    let parallel = classify_pinned_combined_suite_parallel_with_progress_and_cache(
        suite.path(),
        &pin,
        &cache.path().join("classify-suite"),
        &mut |event| {
            assert_eq!(std::thread::current().id(), caller);
            events.push(event);
        },
    )
    .unwrap();
    let sequential = classify_pinned_combined_suite(suite.path(), &pin).unwrap();
    assert_eq!(parallel, sequential);
    assert_eq!(events.len(), 9);

    for lane in [
        ClassificationLane::Scalar,
        ClassificationLane::Heap,
        ClassificationLane::Reference,
    ] {
        let lane_events = events
            .iter()
            .filter(|event| match event {
                ClassificationProgressEvent::FixtureStarted {
                    lane: event_lane, ..
                }
                | ClassificationProgressEvent::LaneCompleted {
                    lane: event_lane, ..
                } => *event_lane == lane,
            })
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(
            lane_events,
            vec![
                ClassificationProgressEvent::FixtureStarted {
                    lane,
                    root: "tests/functional".to_owned(),
                    fixture: "tests/functional/a.py".to_owned(),
                    ordinal: 1,
                    total: 2,
                },
                ClassificationProgressEvent::FixtureStarted {
                    lane,
                    root: "tests/functional".to_owned(),
                    fixture: "tests/functional/b.py".to_owned(),
                    ordinal: 2,
                    total: 2,
                },
                ClassificationProgressEvent::LaneCompleted {
                    lane,
                    root: "tests/functional".to_owned(),
                    total: 2,
                },
            ]
        );
    }
}

#[test]
fn classify_suite_cli_streams_progress_to_stderr_and_keeps_json_on_stdout() {
    let (suite, pin) = create_pinned_suite();
    let output = Command::new(env!("CARGO_BIN_EXE_maledictus"))
        .args(["conformance", "classify-suite", "--suite"])
        .arg(suite.path())
        .arg("--pin")
        .arg(&pin)
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["total"], 2);

    let progress = String::from_utf8(output.stderr).unwrap();
    let lines = progress.lines().collect::<Vec<_>>();
    assert_eq!(lines.len(), 10, "{progress}");
    assert!(
        lines[9].starts_with("[classify-suite] complete: 2 fixtures in "),
        "{progress}"
    );
    for lane in ["scalar", "heap", "reference"] {
        let lane_lines = lines[..9]
            .iter()
            .filter(|line| line.starts_with(&format!("[classify-suite] {lane} ")))
            .copied()
            .collect::<Vec<_>>();
        assert_eq!(
            lane_lines,
            vec![
                format!("[classify-suite] {lane} tests/functional 1/2: tests/functional/a.py"),
                format!("[classify-suite] {lane} tests/functional 2/2: tests/functional/b.py"),
                format!("[classify-suite] {lane} tests/functional complete: 2/2"),
            ]
        );
    }
}
