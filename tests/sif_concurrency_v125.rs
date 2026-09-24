use std::path::Path;
use std::{fs, path::PathBuf};

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture, load_pin,
};
use maledictus::{InformationFlowVerificationProfile, validate_contract_positions_with_profile};

const CONCURRENCY_IN_SIF: &str = "invalid.program:concurrency.in.sif";

fn validate(
    source: &str,
    profile: InformationFlowVerificationProfile,
) -> Result<(), maledictus::ContractPositionFailure> {
    validate_contract_positions_with_profile(source, "program.py", profile)
}

fn assert_sif_rejection(source: &str, line: u32) {
    let failure = validate(
        source,
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .unwrap_err();
    assert_eq!(failure.code, CONCURRENCY_IN_SIF, "{failure:#?}");
    assert_eq!(failure.line, line, "{failure:#?}");
}

#[test]
fn sif_rejects_only_source_bound_lock_and_thread_receiver_operations() {
    assert_sif_rejection(
        "from nagini_contracts.lock import Lock\nclass Cell:\n    pass\nclass CellLock(Lock[Cell]):\n    pass\ndef run(lock: CellLock) -> None:\n    lock.acquire()\n",
        7,
    );
    assert_sif_rejection(
        "from nagini_contracts.lock import Lock as Guard\nclass Cell:\n    pass\nclass Parent(Guard[Cell]):\n    pass\nclass Child(Parent):\n    pass\ndef run(lock: Child) -> None:\n    lock.release()\n",
        9,
    );
    assert_sif_rejection(
        "from nagini_contracts.thread import Thread as Worker\nclass ChildWorker(Worker):\n    pass\ndef run(worker: ChildWorker) -> None:\n    worker.start()\n",
        5,
    );
}

#[test]
fn module_aliases_annotations_and_constructor_assignments_preserve_provenance() {
    assert_sif_rejection(
        "import nagini_contracts.lock as locks\nclass Cell:\n    pass\ndef run() -> None:\n    lock: locks.Lock[Cell] = locks.Lock(Cell())\n    lock.acquire()\n",
        6,
    );
    assert_sif_rejection(
        "from nagini_contracts import thread as threading\ndef run() -> None:\n    worker = threading.Thread()\n    worker.start()\n",
        4,
    );
}

#[test]
fn ordinary_mode_and_unproven_same_named_methods_remain_accepted() {
    let lock_source = "from nagini_contracts.lock import Lock\nclass Cell:\n    pass\nclass CellLock(Lock[Cell]):\n    pass\ndef run(lock: CellLock) -> None:\n    lock.acquire()\n";
    validate(lock_source, InformationFlowVerificationProfile::Ordinary).unwrap();

    let unrelated = "class Local:\n    def acquire(self) -> None:\n        pass\n    def release(self) -> None:\n        pass\n    def start(self) -> None:\n        pass\ndef run(value: Local) -> None:\n    value.acquire()\n    value.release()\n    value.start()\n";
    validate(
        unrelated,
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .unwrap();

    let mismatched = "from nagini_contracts.lock import Lock\nfrom nagini_contracts.thread import Thread\nclass Cell:\n    pass\ndef run(lock: Lock[Cell], worker: Thread) -> None:\n    lock.start()\n    worker.acquire()\n    worker.release()\n";
    validate(
        mismatched,
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .unwrap();
}

#[test]
fn concurrent_sif_profiles_accept_source_bound_concurrency_but_still_check_low_contracts() {
    let lock_source = "from nagini_contracts.contracts import Low, Requires\nfrom nagini_contracts.lock import Lock\nclass Cell:\n    pass\nclass CellLock(Lock[Cell]):\n    pass\ndef run(lock: CellLock, public: bool) -> None:\n    Requires(Low(public))\n    lock.acquire()\n";
    validate(
        lock_source,
        InformationFlowVerificationProfile::PossibilisticSecureInformationFlow,
    )
    .unwrap();
    validate(
        lock_source,
        InformationFlowVerificationProfile::ProbabilisticSecureInformationFlow,
    )
    .unwrap();

    assert_sif_rejection(lock_source, 9);
}

#[test]
fn rebound_provider_names_do_not_create_false_concurrency_provenance() {
    let source = "from nagini_contracts.lock import Lock\nclass Local:\n    def acquire(self) -> None:\n        pass\nLock = Local\ndef run(value: Lock) -> None:\n    value.acquire()\n";
    validate(
        source,
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .unwrap();
}

#[test]
fn agreeing_if_branches_join_to_a_proven_type_but_partial_or_conflicting_branches_do_not() {
    assert_sif_rejection(
        "from nagini_contracts.lock import Lock\nclass Cell:\n    pass\ndef run(flag: bool) -> None:\n    if flag:\n        value = Lock(Cell())\n    else:\n        value = Lock(Cell())\n    value.acquire()\n",
        9,
    );

    for source in [
        "from nagini_contracts.lock import Lock\nclass Cell:\n    pass\ndef run(flag: bool) -> None:\n    if flag:\n        value = Lock(Cell())\n    value.acquire()\n",
        "from nagini_contracts.lock import Lock\nfrom nagini_contracts.thread import Thread\nclass Cell:\n    pass\nclass Worker(Thread):\n    pass\ndef run(flag: bool) -> None:\n    if flag:\n        value = Lock(Cell())\n    else:\n        value = Worker()\n    value.acquire()\n",
    ] {
        validate(
            source,
            InformationFlowVerificationProfile::SecureInformationFlow,
        )
        .unwrap();
    }
}

#[test]
fn exactly_annotated_source_fields_carry_concurrency_provenance() {
    assert_sif_rejection(
        "from nagini_contracts.lock import Lock\nclass Cell:\n    pass\nclass Holder:\n    lock: Lock[Cell]\n    def run(self) -> None:\n        self.lock.acquire()\n",
        7,
    );
    assert_sif_rejection(
        "from nagini_contracts.thread import Thread\nclass Holder:\n    def __init__(self, worker: Thread) -> None:\n        self.worker: Thread = worker\n    def run(self) -> None:\n        self.worker.start()\n",
        6,
    );

    let unrelated = "class Local:\n    def acquire(self) -> None:\n        pass\nclass Holder:\n    lock: Local\n    def run(self) -> None:\n        self.lock.acquire()\n";
    validate(
        unrelated,
        InformationFlowVerificationProfile::SecureInformationFlow,
    )
    .unwrap();
}

#[test]
fn suite_pin_requires_one_explicit_profile_for_every_fixture_root() {
    fn write_pin(directory: &Path, profiles: serde_json::Value) -> PathBuf {
        let path = directory.join("pin.json");
        let pin = serde_json::json!({
            "schema": "maledictus-upstream-suite/v1",
            "project": "Nagini",
            "repository": "https://example.invalid/nagini.git",
            "tag": "v1.3.1",
            "commit": "0123456789abcdef0123456789abcdef01234567",
            "license": "MPL-2.0",
            "test_entrypoint": "tests.py",
            "fixture_roots": ["tests/ordinary", "tests/sif"],
            "fixture_profiles": profiles,
            "conformance_environment": {
                "python": {"implementation": "cpython", "major": 3, "minor": 12},
                "nagini_tag": "v1.3.1",
                "nagini_commit": "0123456789abcdef0123456789abcdef01234567",
                "annotation_profiles": [
                    {"root": "tests/ordinary", "phase": "verification", "backend": "silicon"},
                    {"root": "tests/sif", "phase": "verification", "backend": "silicon"}
                ]
            }
        });
        fs::write(&path, serde_json::to_vec_pretty(&pin).unwrap()).unwrap();
        path
    }

    let directory = tempfile::tempdir().unwrap();
    let incomplete = write_pin(
        directory.path(),
        serde_json::json!([{
            "root": "tests/sif",
            "information_flow": "secure-information-flow"
        }]),
    );
    assert!(load_pin(&incomplete).is_err());

    let complete = write_pin(
        directory.path(),
        serde_json::json!([
            {"root": "tests/ordinary", "information_flow": "ordinary"},
            {"root": "tests/sif", "information_flow": "secure-information-flow"}
        ]),
    );
    let pin = load_pin(&complete).unwrap();
    assert_eq!(pin.fixture_profiles.len(), 2);
}

#[test]
fn exact_three_pinned_sif_concurrency_fixtures_match_every_frontend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/sif-true/translation/test_lock_1.py",
        "tests/sif-true/translation/test_lock_2.py",
        "tests/sif-true/translation/test_threads.py",
    ] {
        let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("scalar {fixture}: {error}"));
        assert!(scalar.passed, "scalar {fixture}: {scalar:#?}");
        assert_eq!(
            scalar.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection,
            "scalar {fixture}: {scalar:#?}"
        );

        let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("heap {fixture}: {error}"));
        assert!(heap.passed, "heap {fixture}: {heap:#?}");
        assert_eq!(
            heap.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection,
            "heap {fixture}: {heap:#?}"
        );

        let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(reference.passed, "reference {fixture}: {reference:#?}");
    }
}

#[test]
fn exact_five_pinned_possibilistic_concurrency_fixtures_reach_verification() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/sif-poss/verification/examples/cav2021-fig12.py",
        "tests/sif-poss/verification/examples/cav2021-fig9.py",
        "tests/sif-poss/verification/examples/no_obligations/cav2021-fig7.py",
        "tests/sif-poss/verification/examples/no_obligations/cav2021-fig8.py",
        "tests/sif-poss/verification/test_lock.py",
    ] {
        let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture);
        match scalar {
            Ok(result) => {
                assert!(result.passed, "scalar {fixture}: {result:#?}");
                assert_ne!(
                    result.analysis_kind,
                    ConformanceMatchKind::SourceWellformednessRejection,
                    "scalar {fixture}: {result:#?}"
                );
            }
            Err(error) => assert!(
                !error.contains(CONCURRENCY_IN_SIF),
                "scalar {fixture} was rejected by the wrong profile: {error}"
            ),
        }

        let heap = check_pinned_heap_fixture(&suite, &pin, fixture);
        match heap {
            Ok(result) => {
                assert!(result.passed, "heap {fixture}: {result:#?}");
                assert_ne!(
                    result.analysis_kind,
                    ConformanceMatchKind::SourceWellformednessRejection,
                    "heap {fixture}: {result:#?}"
                );
            }
            Err(error) => assert!(
                !error.contains(CONCURRENCY_IN_SIF),
                "heap {fixture} was rejected by the wrong profile: {error}"
            ),
        }

        let reference = check_pinned_reference_fixture(&suite, &pin, fixture);
        match reference {
            Ok(result) => assert!(result.passed, "reference {fixture}: {result:#?}"),
            Err(error) => assert!(
                !error.contains(CONCURRENCY_IN_SIF),
                "reference {fixture} was rejected by the wrong profile: {error}"
            ),
        }
    }
}
