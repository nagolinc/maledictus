use std::{fs, path::Path};

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture, classify_pinned_heap_tree, classify_pinned_reference_tree,
    classify_pinned_scalar_tree, load_pin,
};

const ACTIVE_SILICON_FIXTURES: [&str; 13] = [
    "tests/arp/verification/test_chalice_basic.py",
    "tests/arp/verification/test_arp_thread.py",
    "tests/arp/verification/test_rd_expr.py",
    "tests/arp/verification/test_rd.py",
    "tests/arp/translation/test_acc_func.py",
    "tests/io/verification/test_defining_variable_types.py",
    "tests/io/translation/test_decorators_6.py",
    "tests/functional/verification/test_equality.py",
    "tests/functional/verification/issues/00028.py",
    "tests/functional/verification/issues/00026.py",
    "tests/functional/verification/float_ieee32/test_float_long.py",
    "tests/functional/verification/examples/VerifyThis22_Challenge2.py",
    "tests/functional/translation/issues/00039.py",
];

const INACTIVE_CARBON_FIXTURES: [&str; 5] = [
    "tests/arp/verification/test_acc_func.py",
    "tests/arp/verification/test_arp_read_write.py",
    "tests/arp/verification/test_arp_lock_2.py",
    "tests/functional/verification/float_ieee32/test_float.py",
    "tests/sif-prob/verification/examples/no_obligations/secc-cddc.py",
];

#[test]
fn exact_active_ignore_file_fixtures_are_profile_ignored_in_every_frontend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    for fixture in ACTIVE_SILICON_FIXTURES {
        let scalar = check_pinned_scalar_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("scalar {fixture}: {error}"));
        assert!(!scalar.passed, "scalar {fixture}: {scalar:#?}");
        assert_eq!(scalar.analysis_kind, ConformanceMatchKind::ProfileIgnored);
        let scalar_audit = scalar.annotation_profile.as_ref().unwrap();
        assert!(scalar_audit.ignored);
        assert!(
            scalar_audit
                .ignore_file_conditions
                .iter()
                .any(|item| item.active)
        );

        let heap = check_pinned_heap_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("heap {fixture}: {error}"));
        assert!(!heap.passed, "heap {fixture}: {heap:#?}");
        assert_eq!(heap.analysis_kind, ConformanceMatchKind::ProfileIgnored);
        assert_eq!(heap.annotation_profile.as_ref(), Some(scalar_audit));

        let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(!reference.passed, "reference {fixture}: {reference:#?}");
        assert_eq!(reference.annotation_profile.as_ref(), Some(scalar_audit));
    }
}

#[test]
fn profile_ignored_is_counted_separately_and_never_as_a_match() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let root = "tests/arp/translation";

    let scalar = classify_pinned_scalar_tree(&suite, &pin, root).unwrap();
    let heap = classify_pinned_heap_tree(&suite, &pin, root).unwrap();
    let reference = classify_pinned_reference_tree(&suite, &pin, root).unwrap();
    for (matched, ignored, status) in [
        (
            scalar.matched,
            scalar.profile_ignored,
            &scalar.fixtures[0].status,
        ),
        (heap.matched, heap.profile_ignored, &heap.fixtures[0].status),
        (
            reference.matched,
            reference.profile_ignored,
            &reference.fixtures[0].status,
        ),
    ] {
        assert_eq!(matched, 0);
        assert_eq!(ignored, 1);
        assert_eq!(status, "profile-ignored");
    }
}

#[test]
fn carbon_only_annotations_are_inactive_under_the_pinned_silicon_profile() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    for fixture in INACTIVE_CARBON_FIXTURES {
        match check_pinned_scalar_fixture(&suite, &pin, fixture) {
            Ok(result) => {
                assert_ne!(result.analysis_kind, ConformanceMatchKind::ProfileIgnored);
                let audit = result.annotation_profile.as_ref().unwrap();
                assert!(!audit.ignored);
                assert!(audit.ignore_file_conditions.iter().all(|item| !item.active));
            }
            Err(error) => assert!(
                !error.contains("IgnoreFile annotations require"),
                "inactive condition was refused instead of executing normally for {fixture}: {error}"
            ),
        }
    }
}

#[test]
fn annotation_environment_pin_is_exact_and_fail_closed() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("pin.json");
    let base = serde_json::json!({
        "schema": "maledictus-upstream-suite/v1",
        "project": "Nagini",
        "repository": "https://example.invalid/nagini.git",
        "tag": "v1.3.1",
        "commit": "0123456789abcdef0123456789abcdef01234567",
        "license": "MPL-2.0",
        "test_entrypoint": "tests.py",
        "fixture_roots": ["tests/functional"],
        "fixture_profiles": [
            {"root": "tests/functional", "information_flow": "ordinary"}
        ],
        "conformance_environment": {
            "python": {"implementation": "cpython", "major": 3, "minor": 12},
            "nagini_tag": "v1.3.1",
            "nagini_commit": "0123456789abcdef0123456789abcdef01234567",
            "annotation_profiles": [
                {"root": "tests/functional", "phase": "verification", "backend": "silicon"},
                {"root": "tests/functional/translation", "phase": "translation", "backend": "any"}
            ]
        }
    });
    fs::write(&path, serde_json::to_vec_pretty(&base).unwrap()).unwrap();
    load_pin(&path).unwrap();

    let mut mismatched = base.clone();
    mismatched["conformance_environment"]["nagini_commit"] =
        serde_json::json!("ffffffffffffffffffffffffffffffffffffffff");
    fs::write(&path, serde_json::to_vec_pretty(&mismatched).unwrap()).unwrap();
    assert!(load_pin(&path).unwrap_err().contains("exact pinned Nagini"));

    let mut incomplete = base.clone();
    incomplete["conformance_environment"]["annotation_profiles"] = serde_json::json!([]);
    fs::write(&path, serde_json::to_vec_pretty(&incomplete).unwrap()).unwrap();
    assert!(
        load_pin(&path)
            .unwrap_err()
            .contains("no explicit base annotation profile")
    );

    let mut incompatible = base;
    incompatible["conformance_environment"]["annotation_profiles"][0]["backend"] =
        serde_json::json!("any");
    fs::write(&path, serde_json::to_vec_pretty(&incompatible).unwrap()).unwrap();
    assert!(
        load_pin(&path)
            .unwrap_err()
            .contains("incompatible phase/backend")
    );
}
