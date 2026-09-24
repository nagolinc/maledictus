use std::path::Path;

use maledictus::conformance::{ConformanceMatchKind, check_pinned_heap_fixture};

const FIXTURES: &[&str] = &[
    "tests/obligations/verification/chalice2silver/issues/chalice2silver-82.py",
    "tests/obligations/verification/chalice2silver/issues/chalice2silver-83.py",
    "tests/obligations/verification/chalice2silver/returningObligations.py",
    "tests/obligations/verification/test_must_invoke.py",
];
const TERMINATION_CHANNEL_FIXTURE: &str =
    "tests/sif-true/verification/test_termination_channels.py";

fn assert_exact_pinned_heap_fixture(fixture: &str) {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_heap_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("heap classifier refused {fixture}: {error}"));
    assert!(result.passed, "{fixture}: {result:#?}");
    assert_eq!(result.expected, result.actual, "{fixture}: {result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SemanticVerification,
        "{fixture}: {result:#?}"
    );
}

#[test]
fn loop_back_obligations_match_the_pinned_lock_and_io_transfer_semantics() {
    for fixture in FIXTURES {
        assert_exact_pinned_heap_fixture(fixture);
    }
}

#[test]
fn termination_loop_promise_failure_projects_at_the_pinned_loop_boundary() {
    assert_exact_pinned_heap_fixture(TERMINATION_CHANNEL_FIXTURE);
}
