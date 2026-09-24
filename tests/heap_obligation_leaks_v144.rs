use std::io::Write;
use std::path::Path;

use maledictus::conformance::{
    ConformanceMatchKind, ExpectedDiagnostic, check_pinned_heap_fixture,
};

const METHOD_FIXTURE: &str = "tests/obligations/verification/test_method_leak_check.py";
const LOOP_FIXTURE: &str = "tests/obligations/verification/test_loop_leak_check.py";
const CALL_FIXTURE: &str = "tests/obligations/verification/chalice2silver/leakCheckCall.py";

fn diagnostic(code: &str, line: u32) -> ExpectedDiagnostic {
    ExpectedDiagnostic {
        code: code.to_owned(),
        line,
    }
}

fn assert_pinned_diagnostics(fixture: &str, expected: &[ExpectedDiagnostic]) {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_heap_fixture(&suite, &pin, fixture)
        .unwrap_or_else(|error| panic!("heap classifier refused {fixture}: {error}"));

    assert!(result.passed, "{fixture}: {result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SemanticVerification,
        "{fixture}: {result:#?}"
    );
    for expected_diagnostic in expected {
        assert!(
            result.expected.contains(expected_diagnostic),
            "missing pinned expectation {expected_diagnostic:?}: {result:#?}"
        );
        assert!(
            result.actual.contains(expected_diagnostic),
            "missing semantic diagnostic {expected_diagnostic:?}: {result:#?}"
        );
    }
}

fn assert_synthesized_pinned_conformance(source: &str, case_name: &str) {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let fixture_directory = suite.join("tests/obligations/verification");
    let mut fixture_file = tempfile::Builder::new()
        .prefix(&format!("maledictus-v144-{case_name}-"))
        .suffix(".py")
        .tempfile_in(&fixture_directory)
        .unwrap_or_else(|error| panic!("cannot create synthesized fixture {case_name}: {error}"));
    fixture_file
        .write_all(source.as_bytes())
        .unwrap_or_else(|error| panic!("cannot write synthesized fixture {case_name}: {error}"));
    fixture_file
        .flush()
        .unwrap_or_else(|error| panic!("cannot flush synthesized fixture {case_name}: {error}"));

    let fixture = fixture_file
        .path()
        .strip_prefix(&suite)
        .unwrap_or_else(|error| panic!("synthesized fixture escaped pinned suite: {error}"))
        .to_string_lossy()
        .replace('\\', "/");
    let result = check_pinned_heap_fixture(&suite, &pin, &fixture)
        .unwrap_or_else(|error| panic!("heap classifier refused {case_name}: {error}"));
    assert!(result.passed, "{case_name}: {result:#?}");
    assert_eq!(result.expected, result.actual, "{case_name}: {result:#?}");
    assert_eq!(
        result.analysis_kind,
        ConformanceMatchKind::SemanticVerification,
        "{case_name}: {result:#?}"
    );
}

#[test]
fn method_and_call_leaks_are_reported_at_their_exact_pinned_boundaries() {
    assert_pinned_diagnostics(
        METHOD_FIXTURE,
        &[
            diagnostic("leak_check.failed:caller.has_unsatisfied_obligations", 18),
            diagnostic("leak_check.failed:method_body.leaks_obligations", 26),
            diagnostic("leak_check.failed:method_body.leaks_obligations", 32),
            diagnostic("leak_check.failed:caller.has_unsatisfied_obligations", 43),
            diagnostic("leak_check.failed:method_body.leaks_obligations", 51),
            diagnostic("leak_check.failed:method_body.leaks_obligations", 57),
        ],
    );
}

#[test]
fn loop_context_and_loop_body_leaks_are_reported_at_exact_pinned_boundaries() {
    assert_pinned_diagnostics(
        LOOP_FIXTURE,
        &[
            diagnostic(
                "leak_check.failed:loop_context.has_unsatisfied_obligations",
                17,
            ),
            diagnostic(
                "leak_check.failed:loop_context.has_unsatisfied_obligations",
                25,
            ),
            diagnostic("leak_check.failed:method_body.leaks_obligations", 30),
            diagnostic("leak_check.failed:method_body.leaks_obligations", 39),
            diagnostic("leak_check.failed:loop_body.leaks_obligations", 71),
            diagnostic("leak_check.failed:loop_body.leaks_obligations", 81),
        ],
    );
}

#[test]
fn call_boundary_leaks_preserve_each_exact_pinned_location() {
    assert_pinned_diagnostics(
        CALL_FIXTURE,
        &[
            diagnostic("leak_check.failed:caller.has_unsatisfied_obligations", 42),
            diagnostic("leak_check.failed:caller.has_unsatisfied_obligations", 76),
            diagnostic("leak_check.failed:method_body.leaks_obligations", 81),
            diagnostic("leak_check.failed:caller.has_unsatisfied_obligations", 94),
        ],
    );
}

#[test]
fn releasing_through_an_alias_discharges_the_original_objects_obligation() {
    assert_synthesized_pinned_conformance(
        r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import MustRelease

def release_alias(lock: Lock[object]) -> None:
    Requires(MustRelease(lock, 1))
    alias = lock
    alias.release()

#:: ExpectedOutput(leak_check.failed:method_body.leaks_obligations)
def unreleased_alias_control(lock: Lock[object]) -> None:
    Requires(MustRelease(lock, 1))
    alias = lock
"#,
        "alias-release",
    );
}

#[test]
fn a_distinct_object_cannot_discharge_another_objects_obligation() {
    assert_synthesized_pinned_conformance(
        r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import MustRelease

#:: ExpectedOutput(leak_check.failed:method_body.leaks_obligations)
def wrong_release(left: Lock[object], right: Lock[object]) -> None:
    Requires(MustRelease(left, 1))
    #:: ExpectedOutput(call.precondition:insufficient.permission)
    right.release()
"#,
        "distinct-release",
    );
}

#[test]
fn every_reachable_return_path_must_discharge_or_transfer_the_obligation() {
    assert_synthesized_pinned_conformance(
        r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import MustRelease

#:: ExpectedOutput(leak_check.failed:method_body.leaks_obligations)
def conditional_release(lock: Lock[object], release_now: bool) -> None:
    Requires(MustRelease(lock, 1))
    if release_now:
        lock.release()
        return
    return
"#,
        "all-return-paths",
    );
}

#[test]
fn finally_discharges_obligations_on_normal_return_and_exceptional_exit() {
    assert_synthesized_pinned_conformance(
        r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import MustRelease

class Failure(Exception):
    pass

def release_on_every_exit(lock: Lock[object], fail: bool) -> None:
    Requires(MustRelease(lock, 1))
    Exsures(Failure, True)
    try:
        if fail:
            raise Failure()
        return
    finally:
        lock.release()

#:: ExpectedOutput(leak_check.failed:method_body.leaks_obligations)
def exceptional_exit_without_finally(lock: Lock[object]) -> None:
    Requires(MustRelease(lock, 1))
    Exsures(Failure, True)
    raise Failure()
"#,
        "finally-all-exits",
    );
}

#[test]
fn break_and_continue_paths_preserve_the_obligation_until_its_discharge() {
    assert_synthesized_pinned_conformance(
        r#"from nagini_contracts.contracts import *
from nagini_contracts.lock import Lock
from nagini_contracts.obligations import MustRelease, MustTerminate

def release_after_loop(lock: Lock[object], skip_once: bool) -> None:
    Requires(MustRelease(lock, 3))
    index = 0
    while index < 2:
        Invariant(index >= 0 and index <= 2)
        Invariant(MustRelease(lock, 3 - index))
        Invariant(MustTerminate(3 - index))
        index += 1
        if skip_once and index == 1:
            continue
        break
    lock.release()

def loop_without_obligation_invariant(lock: Lock[object]) -> None:
    Requires(MustRelease(lock, 1))
    index = 0
    #:: ExpectedOutput(leak_check.failed:loop_context.has_unsatisfied_obligations)
    while index < 2:
        index += 1
    lock.release()
"#,
        "break-continue",
    );
}
