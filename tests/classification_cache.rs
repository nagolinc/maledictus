use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Barrier};

use maledictus::conformance::{
    ClassificationProgressEvent, classify_pinned_combined_suite,
    classify_pinned_combined_suite_parallel_with_progress_and_cache,
    classify_pinned_combined_suite_with_progress_and_cache,
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

fn create_pinned_suite(
    fixtures: &[(&str, &str)],
    extra_sources: &[(&str, &str)],
) -> (tempfile::TempDir, PathBuf) {
    let directory = tempfile::tempdir().unwrap();
    for (relative, source) in fixtures.iter().chain(extra_sources) {
        let path = directory.path().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }

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
            "pinned classification cache suite",
        ],
    );
    let commit = run_git(directory.path(), &["rev-parse", "HEAD"]);
    let pin = directory.path().join("pin.json");
    fs::write(
        &pin,
        serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "maledictus-upstream-suite/v1",
            "project": "classification cache test",
            "repository": "https://example.invalid/classification-cache.git",
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

fn collect_json_files(directory: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_json_files(&path, files);
        } else if path.extension().and_then(|extension| extension.to_str()) == Some("json") {
            files.push(path);
        }
    }
    files.sort();
}

fn cached_report(
    suite: &Path,
    pin: &Path,
    cache: &Path,
) -> (
    maledictus::conformance::CombinedClassificationReport,
    Vec<ClassificationProgressEvent>,
) {
    let mut events = Vec::new();
    let report =
        classify_pinned_combined_suite_with_progress_and_cache(suite, pin, cache, &mut |event| {
            events.push(event)
        })
        .unwrap();
    (report, events)
}

fn parallel_cached_report(
    suite: &Path,
    pin: &Path,
    cache: &Path,
) -> (
    maledictus::conformance::CombinedClassificationReport,
    Vec<ClassificationProgressEvent>,
) {
    let mut events = Vec::new();
    let report = classify_pinned_combined_suite_parallel_with_progress_and_cache(
        suite,
        pin,
        cache,
        &mut |event| events.push(event),
    )
    .unwrap();
    (report, events)
}

#[test]
fn cached_and_fresh_results_share_canonical_report_and_progress_reconciliation() {
    let (suite, pin) = create_pinned_suite(&[("tests/functional/a.py", "")], &[]);
    let cache = repository_cache_directory("classification-cache-canonical-");
    let cache_root = cache.path().join("classify-suite");

    let (first, first_events) = cached_report(suite.path(), &pin, &cache_root);
    let uncached = classify_pinned_combined_suite(suite.path(), &pin).unwrap();
    assert_eq!(first, uncached);

    let mut first_entries = Vec::new();
    collect_json_files(&cache_root, &mut first_entries);
    assert_eq!(first_entries.len(), 3, "one immutable result per lane");
    let first_bytes = first_entries
        .iter()
        .map(|path| (path.clone(), fs::read(path).unwrap()))
        .collect::<Vec<_>>();

    let (second, second_events) = cached_report(suite.path(), &pin, &cache_root);
    assert_eq!(second, first);
    assert_eq!(second_events, first_events);
    let mut second_entries = Vec::new();
    collect_json_files(&cache_root, &mut second_entries);
    assert_eq!(second_entries, first_entries);
    for (path, bytes) in first_bytes {
        assert_eq!(fs::read(path).unwrap(), bytes, "cache hit rewrote an entry");
    }
}

#[test]
fn cold_parallel_and_sequential_reports_are_byte_exact_and_warm_cache_is_immutable() {
    let (suite, pin) = create_pinned_suite(
        &[("tests/functional/a.py", ""), ("tests/functional/b.py", "")],
        &[],
    );
    let sequential_cache = repository_cache_directory("classification-cache-sequential-");
    let parallel_cache = repository_cache_directory("classification-cache-parallel-");
    let (sequential, _) = cached_report(
        suite.path(),
        &pin,
        &sequential_cache.path().join("classify-suite"),
    );
    let parallel_root = parallel_cache.path().join("classify-suite");
    let (parallel, _) = parallel_cached_report(suite.path(), &pin, &parallel_root);

    assert_eq!(parallel, sequential);
    assert_eq!(
        serde_json::to_vec(&parallel).unwrap(),
        serde_json::to_vec(&sequential).unwrap(),
        "parallel scheduling changed canonical report bytes"
    );

    let mut cold_entries = Vec::new();
    collect_json_files(&parallel_root, &mut cold_entries);
    assert_eq!(
        cold_entries.len(),
        6,
        "one cold result per fixture and lane"
    );
    let cold_bytes = cold_entries
        .iter()
        .map(|path| (path.clone(), fs::read(path).unwrap()))
        .collect::<Vec<_>>();

    let (warm, _) = parallel_cached_report(suite.path(), &pin, &parallel_root);
    assert_eq!(warm, parallel);
    let mut warm_entries = Vec::new();
    collect_json_files(&parallel_root, &mut warm_entries);
    assert_eq!(warm_entries, cold_entries);
    for (path, bytes) in cold_bytes {
        assert_eq!(fs::read(path).unwrap(), bytes, "warm hit rewrote an entry");
    }
}

#[test]
fn concurrent_parallel_runs_publish_a_reusable_shared_cache() {
    let (suite, pin) = create_pinned_suite(&[("tests/functional/a.py", "")], &[]);
    let oracle = classify_pinned_combined_suite(suite.path(), &pin).unwrap();
    let cache = repository_cache_directory("classification-cache-concurrent-");
    let cache_root = cache.path().join("classify-suite");
    let start = Arc::new(Barrier::new(2));

    let (first, second) = std::thread::scope(|scope| {
        let suite = suite.path();
        let pin = &pin;
        let cache_root = &cache_root;
        let first_start = Arc::clone(&start);
        let first = scope.spawn(move || {
            first_start.wait();
            classify_pinned_combined_suite_parallel_with_progress_and_cache(
                suite,
                pin,
                cache_root,
                &mut |_| {},
            )
        });
        let second_start = Arc::clone(&start);
        let second = scope.spawn(move || {
            second_start.wait();
            classify_pinned_combined_suite_parallel_with_progress_and_cache(
                suite,
                pin,
                cache_root,
                &mut |_| {},
            )
        });
        (first.join().unwrap(), second.join().unwrap())
    });
    assert_eq!(first.unwrap(), oracle);
    assert_eq!(second.unwrap(), oracle);

    let mut published_entries = Vec::new();
    collect_json_files(&cache_root, &mut published_entries);
    let published_bytes = published_entries
        .iter()
        .map(|path| (path.clone(), fs::read(path).unwrap()))
        .collect::<Vec<_>>();
    let (warm, _) = parallel_cached_report(suite.path(), &pin, &cache_root);
    assert_eq!(warm, oracle);
    let mut warm_entries = Vec::new();
    collect_json_files(&cache_root, &mut warm_entries);
    assert_eq!(warm_entries, published_entries);
    for (path, bytes) in published_bytes {
        assert_eq!(fs::read(path).unwrap(), bytes);
    }
}

#[test]
fn corrupt_and_partial_entries_are_misses_and_never_classification_results() {
    let (suite, pin) = create_pinned_suite(&[("tests/functional/a.py", "")], &[]);
    let cache = repository_cache_directory("classification-cache-corrupt-");
    let cache_root = cache.path().join("classify-suite");
    let (expected, _) = cached_report(suite.path(), &pin, &cache_root);

    let mut entries = Vec::new();
    collect_json_files(&cache_root, &mut entries);
    assert_eq!(entries.len(), 3);
    let corrupted = entries[0].clone();
    fs::write(&corrupted, b"{\"schema\":").unwrap();

    let (after_corruption, _) = cached_report(suite.path(), &pin, &cache_root);
    assert_eq!(after_corruption, expected);
    let mut after_corruption_entries = Vec::new();
    collect_json_files(&cache_root, &mut after_corruption_entries);
    assert_eq!(after_corruption_entries.len(), 4);

    let partial = corrupted.parent().unwrap().join("interrupted-write.tmp");
    fs::write(&partial, b"partial cache bytes").unwrap();
    let (after_partial, _) = cached_report(suite.path(), &pin, &cache_root);
    assert_eq!(after_partial, expected);
    let mut after_partial_entries = Vec::new();
    collect_json_files(&cache_root, &mut after_partial_entries);
    assert_eq!(after_partial_entries, after_corruption_entries);
}

#[test]
fn source_provider_and_pinned_root_inventory_changes_invalidate_prior_entries() {
    let (suite, pin) = create_pinned_suite(
        &[(
            "tests/functional/a.py",
            "from resources.helper import value\nassert value == 1\n",
        )],
        &[
            ("tests/resources/__init__.py", ""),
            ("tests/resources/helper.py", "value: int = 1\n"),
        ],
    );
    let cache = repository_cache_directory("classification-cache-inputs-");
    let cache_root = cache.path().join("classify-suite");
    let _ = cached_report(suite.path(), &pin, &cache_root);
    let mut initial_entries = Vec::new();
    collect_json_files(&cache_root, &mut initial_entries);
    assert_eq!(initial_entries.len(), 3);

    fs::write(
        suite.path().join("tests/resources/helper.py"),
        "value: int = 2\n",
    )
    .unwrap();
    let _ = cached_report(suite.path(), &pin, &cache_root);
    let mut source_changed_entries = Vec::new();
    collect_json_files(&cache_root, &mut source_changed_entries);
    assert_eq!(source_changed_entries.len(), 6);

    fs::write(suite.path().join("tests/functional/b.py"), "").unwrap();
    let (inventory_changed, _) = cached_report(suite.path(), &pin, &cache_root);
    assert_eq!(inventory_changed.total, 2);
    let mut inventory_changed_entries = Vec::new();
    collect_json_files(&cache_root, &mut inventory_changed_entries);
    assert_eq!(inventory_changed_entries.len(), 12);
}

#[test]
fn cache_root_outside_repository_cache_is_rejected_before_writing() {
    let (suite, pin) = create_pinned_suite(&[("tests/functional/a.py", "")], &[]);
    let outside = tempfile::tempdir().unwrap();
    let rejected = classify_pinned_combined_suite_with_progress_and_cache(
        suite.path(),
        &pin,
        &outside.path().join("classify-suite"),
        &mut |_| {},
    )
    .unwrap_err();
    assert!(
        rejected.contains("must be below repository .cache"),
        "{rejected}"
    );
    assert!(!outside.path().join("classify-suite").exists());
}
