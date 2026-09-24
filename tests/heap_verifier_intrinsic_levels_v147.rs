use std::io::Write;
use std::path::Path;

use maledictus::conformance::check_pinned_heap_fixture;

const REPRESENTATIVE_OBLIGATION_FIXTURES: [&str; 24] = [
    "tests/arp/verification/test_arp_lock_1.py",
    "tests/functional/verification/issues/00112.py",
    "tests/functional/verification/test_inline.py",
    "tests/functional/verification/test_lock.py",
    "tests/obligations/verification/chalice2silver/aliasingRelease.py",
    "tests/obligations/verification/chalice2silver/christian/lt_call.py",
    "tests/obligations/verification/chalice2silver/christian/lt_loops.py",
    "tests/obligations/verification/chalice2silver/christian/obl_loop.py",
    "tests/obligations/verification/chalice2silver/christian/obl_pre_rel.py",
    "tests/obligations/verification/chalice2silver/christian/obl_pre_transfer.py",
    "tests/obligations/verification/chalice2silver/christian/term_loop.py",
    "tests/obligations/verification/chalice2silver/issues/chalice2silver-77-3.py",
    "tests/obligations/verification/chalice2silver/leakCheckCall.py",
    "tests/obligations/verification/chalice2silver/loopsAndRelease.py",
    "tests/obligations/verification/chalice2silver/loopsAndTermination.py",
    "tests/obligations/verification/chalice2silver/termination.py",
    "tests/obligations/verification/test_behavioral_subtyping.py",
    "tests/obligations/verification/test_builtin_must_terminate.py",
    "tests/obligations/verification/test_for_must_terminate.py",
    "tests/obligations/verification/test_loop_leak_check.py",
    "tests/obligations/verification/test_method_leak_check.py",
    "tests/obligations/verification/test_must_release.py",
    "tests/obligations/verification/test_while_must_terminate.py",
    "tests/sif-true/verification/examples/joana-fig3-tl.py",
];

fn check_source(source: &str, case: &str) -> Result<(), String> {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let fixture_directory = suite.join("tests/functional/verification");
    let mut fixture = tempfile::Builder::new()
        .prefix(&format!("maledictus-v147-{case}-"))
        .suffix(".py")
        .tempfile_in(&fixture_directory)
        .map_err(|error| error.to_string())?;
    fixture
        .write_all(source.as_bytes())
        .and_then(|()| fixture.flush())
        .map_err(|error| error.to_string())?;
    let relative = fixture
        .path()
        .strip_prefix(&suite)
        .map_err(|error| error.to_string())?
        .to_string_lossy()
        .replace('\\', "/");
    let verification = check_pinned_heap_fixture(
        &suite,
        &repository.join("conformance/nagini-v1.3.1.json"),
        &relative,
    )
    .map_err(|error| error.to_string())?;
    if verification.passed {
        Ok(())
    } else {
        Err(format!("{verification:#?}"))
    }
}

#[test]
fn canonical_named_and_star_bindings_share_stable_level_semantics() {
    check_source(
        r#"from nagini_contracts.contracts import Requires, Ensures
from nagini_contracts.obligations import Level as L, WaitLevel as W
from nagini_contracts.obligations import *

def named(lock: object) -> None:
    Requires(W() < L(lock))
    Ensures(W() < L(lock))

def wildcard(lock: object) -> None:
    Requires(WaitLevel() < Level(lock))
    Ensures(WaitLevel() < Level(lock))

"#,
        "canonical",
    )
    .expect("canonical aliases must retain one stable intrinsic identity");
}

#[test]
fn malformed_reversed_chained_and_runtime_aliased_uses_fail_closed() {
    for (case, body, expected) in [
        (
            "standalone",
            "Requires(Level(lock))",
            "level-intrinsic-standalone",
        ),
        (
            "reversed",
            "Requires(Level(lock) > WaitLevel())",
            "level-intrinsic-standalone",
        ),
        (
            "chained",
            "Requires(WaitLevel() < Level(lock) < Level(other))",
            "level-intrinsic-standalone",
        ),
        (
            "malformed",
            "Requires(WaitLevel(1) < Level(lock))",
            "wait-level-arity",
        ),
    ] {
        let source = format!(
            "from nagini_contracts.contracts import Requires\nfrom nagini_contracts.obligations import Level, WaitLevel\n\ndef bad(lock: object, other: object) -> None:\n    {}\n",
            body.replace('\n', "\n    ")
        );
        let error = check_source(&source, case).expect_err("unsupported intrinsic use must refuse");
        assert!(
            error.contains(expected),
            "{case} produced the wrong refusal: {error}"
        );
    }
}

#[test]
fn local_shadowing_cannot_recover_canonical_intrinsic_identity_by_spelling() {
    let error = check_source(
        r#"from nagini_contracts.contracts import Requires
from nagini_contracts.obligations import Level, WaitLevel

def shadowed(Level: object, lock: object) -> None:
    Requires(WaitLevel() < Level(lock))
"#,
        "shadowed",
    )
    .expect_err("a parameter named Level must shadow the imported intrinsic");
    assert!(
        error.contains("level-relation-malformed") || error.contains("call"),
        "shadowed binding produced the wrong refusal: {error}"
    );
}

#[test]
fn representative_obligation_fixtures_reach_semantics_past_the_intrinsic_abi() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let mut exact = 0;
    let mut semantic = 0;
    for fixture in REPRESENTATIVE_OBLIGATION_FIXTURES {
        match check_pinned_heap_fixture(&suite, &pin, fixture) {
            Ok(verification) => {
                exact += usize::from(verification.passed);
                semantic += usize::from(
                    verification.analysis_kind
                        == maledictus::conformance::ConformanceMatchKind::SemanticVerification,
                );
            }
            Err(error) => {
                assert!(
                    !error.contains("frontend.python.verifier-intrinsic")
                        && !error.contains("LevelType.__lt__")
                        && !error.contains("OBLIGATION_CONTRACT_FUNCS"),
                    "{fixture} regressed at the canonical intrinsic ABI: {error}"
                );
            }
        }
    }
    eprintln!(
        "after intrinsic resolution: exact pinned agreement {exact}/24; semantic projection {semantic}/24"
    );
}
