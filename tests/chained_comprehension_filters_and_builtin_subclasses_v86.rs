use std::{fs, path::Path};

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile};
use maledictus::python_contracts::{ContractVerification, verify_contract_module};

const BUILTIN_SUBCLASS_UNSUPPORTED: &str =
    "unsupported:Subclassing builtin type is currently not supported.";

fn verify(source: &str, path: &str) -> ContractVerification {
    verify_contract_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it was refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn analyze(source: &str) -> maledictus::FrontendAnalysis {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("program.py"), source).unwrap();
    maledictus::analyze_python_frontend(&ProofRequest {
        schema: PROTOCOL_SCHEMA.to_owned(),
        source_root: directory.path().display().to_string(),
        source_fingerprint: "0".repeat(64),
        proof_obligation: "no-undeclared-exceptional-exit".to_owned(),
        files: vec![SourceFile {
            path: "program.py".to_owned(),
            language: "python".to_owned(),
            symbols: Vec::new(),
        }],
        external_contract_overlays: Vec::new(),
        python_callable_bindings: Vec::new(),
        cross_language_bindings: Vec::new(),
    })
}

fn assert_all_assertions_proved(verification: &ContractVerification, expected: usize) {
    assert!(verification.passed, "{verification:#?}");
    let assertions = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":assert:"))
        .collect::<Vec<_>>();
    assert_eq!(assertions.len(), expected, "{verification:#?}");
    assert!(
        assertions.iter().all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn chained_filters_have_exact_list_set_and_dictionary_semantics() {
    let verification = verify(
        r#"from typing import Dict, List, Set

def run() -> None:
    values = [-2, -1, 0, 1, 2, 3]
    selected = [x * 10 for x in values if x >= 0 if x < 3 if x != 1]  # type: List[int]
    assert len(selected) == 2
    assert selected[0] == 0
    assert selected[1] == 20

    unique = {x % 3 for x in values if x >= 0 if x < 3}  # type: Set[int]
    assert len(unique) == 3
    assert 0 in unique and 1 in unique and 2 in unique

    last = {x % 2: x for x in values if x >= 0 if x < 4}  # type: Dict[int, int]
    assert len(last) == 2
    assert last[0] == 2
    assert last[1] == 3
"#,
        "v86_chained_comprehension_filters.py",
    );

    assert_all_assertions_proved(&verification, 8);
}

#[test]
fn every_filter_is_type_checked_and_effect_checked() {
    for (source, expected_code) in [
        (
            "from typing import List\ndef run() -> None:\n    values = [1, 2]\n    result = [x for x in values if x > 0 if x + 1]  # type: List[int]\n",
            "frontend.python.contracts.expected-bool",
        ),
        (
            "from typing import List\ndef effect(value: int) -> bool:\n    return value > 0\ndef run() -> None:\n    values = [1, 2]\n    result = [x for x in values if x > 0 if effect(x)]  # type: List[int]\n",
            "frontend.python.contracts.comprehension-filter-effect-unsupported",
        ),
    ] {
        let failure = verify_contract_module(source, "v86_bad_filter.py", &[])
            .expect_err("invalid chained filter unexpectedly verified");
        assert_eq!(failure.code, expected_code, "{failure:#?}");
    }
}

#[test]
fn native_and_typing_collection_bases_are_rejected_at_the_class_boundary() {
    for (source, expected_line) in [
        ("class Invalid(str):\n    pass\n", 1),
        ("class Invalid(list[int]):\n    pass\n", 1),
        (
            "from typing import List as SequenceBase\nclass Invalid(SequenceBase[int]):\n    pass\n",
            2,
        ),
    ] {
        let analysis = analyze(source);
        let diagnostic = analysis
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code == BUILTIN_SUBCLASS_UNSUPPORTED)
            .unwrap_or_else(|| panic!("missing builtin-subclass diagnostic: {analysis:#?}"));
        assert_eq!(diagnostic.line, Some(expected_line), "{analysis:#?}");
    }
}

#[test]
fn extendable_and_shadowed_names_do_not_acquire_builtin_identity() {
    for source in [
        "class IntegerSubtype(int):\n    pass\n",
        "class Base:\n    pass\nstr = Base\nclass Derived(str):\n    pass\n",
        "class list:\n    pass\nclass Derived(list):\n    pass\n",
    ] {
        let analysis = analyze(source);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != BUILTIN_SUBCLASS_UNSUPPORTED),
            "{source}\n{analysis:#?}"
        );
    }
}

#[test]
fn both_pinned_nonextendable_builtin_subclass_fixtures_match_all_frontends() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for fixture in [
        "tests/functional/translation/test_builtin_subclass_1.py",
        "tests/functional/translation/test_builtin_subclass_2.py",
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

        let reference = check_pinned_reference_fixture(&suite, &pin, fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(reference.passed, "reference {fixture}: {reference:#?}");
    }
}
