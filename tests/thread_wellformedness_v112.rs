use std::{fs, path::Path};

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::{
    analyze_python_frontend,
    protocol::{PROTOCOL_SCHEMA, ProofRequest, SourceFile},
};

const INVALID_THREAD_CREATION: &str = "invalid.program:invalid.thread.creation";
const INVALID_THREAD_START: &str = "invalid.program:invalid.thread.start";
const INVALID_THREAD_JOIN: &str = "invalid.program:invalid.thread.join";
const INVALID_GET_METHOD_USE: &str = "invalid.program:invalid.get.method.use";
const INVALID_ARG_USE: &str = "invalid.program:invalid.arg.use";

fn analyze(source: &str) -> maledictus::FrontendAnalysis {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("program.py"), source).unwrap();
    analyze_python_frontend(&ProofRequest {
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

fn assert_early_refusal(source: &str, expected: &str) {
    let analysis = analyze(source);
    assert_eq!(
        analysis.disposition,
        maledictus::FrontendDisposition::Unsupported
    );
    assert!(analysis.files.is_empty(), "{analysis:#?}");
    assert!(analysis.obligations.is_empty(), "{analysis:#?}");
    assert_eq!(analysis.diagnostics.len(), 1, "{analysis:#?}");
    assert_eq!(analysis.diagnostics[0].code, expected, "{analysis:#?}");
}

#[test]
fn thread_creation_resolves_target_kind_and_tuple_arity() {
    for source in [
        "from nagini_contracts.contracts import Pure\nfrom nagini_contracts.thread import Thread\n@Pure\ndef target(value: int) -> int:\n    return value\ndef run() -> Thread:\n    return Thread(target=target, args=(1,))\n",
        "from nagini_contracts.contracts import Predicate\nfrom nagini_contracts.thread import Thread\n@Predicate\ndef target(value: int) -> bool:\n    return True\ndef run() -> Thread:\n    return Thread(target=target, args=(1,))\n",
        "from nagini_contracts.thread import Thread\ndef target(value: int) -> None:\n    pass\ndef run() -> Thread:\n    return Thread(args=(1,))\n",
        "from nagini_contracts.thread import Thread\ndef target(value: int) -> None:\n    pass\ndef run() -> Thread:\n    return Thread(target=target, args=(1, 2))\n",
        "from nagini_contracts.thread import Thread\ndef target(value: int) -> None:\n    pass\ndef run() -> Thread:\n    return Thread(target=target, args=[1])\n",
    ] {
        assert_early_refusal(source, INVALID_THREAD_CREATION);
    }
}

#[test]
fn lifecycle_options_must_be_impure_targets_and_start_targets_must_be_obligation_free() {
    assert_early_refusal(
        "from nagini_contracts.contracts import Pure\nfrom nagini_contracts.thread import Thread\n@Pure\ndef target() -> int:\n    return 1\ndef run(thread: Thread) -> None:\n    thread.start(target)\n",
        INVALID_THREAD_START,
    );
    assert_early_refusal(
        "from nagini_contracts.contracts import Pure\nfrom nagini_contracts.thread import Thread\n@Pure\ndef target() -> int:\n    return 1\ndef run(thread: Thread) -> None:\n    thread.join(target)\n",
        INVALID_THREAD_JOIN,
    );
    assert_early_refusal(
        "from nagini_contracts.contracts import Ensures\nfrom nagini_contracts.obligations import MustTerminate\nfrom nagini_contracts.thread import Thread\ndef target() -> None:\n    Ensures(MustTerminate(1))\ndef run(thread: Thread) -> None:\n    thread.start(target)\n",
        INVALID_THREAD_START,
    );
}

#[test]
fn thread_contract_helpers_are_limited_to_their_semantic_positions() {
    assert_early_refusal(
        "from nagini_contracts.contracts import Requires\nfrom nagini_contracts.thread import Thread, getMethod\ndef consume(value: object) -> bool:\n    return True\ndef run(thread: Thread) -> None:\n    Requires(consume(getMethod(thread)))\n",
        INVALID_GET_METHOD_USE,
    );
    assert_early_refusal(
        "from nagini_contracts.contracts import Requires\nfrom nagini_contracts.thread import arg\ndef run(value: object) -> None:\n    Requires(arg(0) == value)\n",
        INVALID_ARG_USE,
    );
}

#[test]
fn aliases_are_semantic_but_unrelated_or_shadowed_names_are_not_thread_api_calls() {
    assert_early_refusal(
        "from nagini_contracts.contracts import Pure\nfrom nagini_contracts.thread import Thread as Worker\n@Pure\ndef target() -> int:\n    return 1\ndef run() -> Worker:\n    return Worker(target=target, args=())\n",
        INVALID_THREAD_CREATION,
    );

    let unrelated = analyze(
        "class Worker:\n    def start(self, value: int) -> None:\n        pass\ndef target() -> None:\n    pass\ndef run(worker: Worker) -> None:\n    worker.start(1)\n",
    );
    assert!(
        unrelated.diagnostics.iter().all(|diagnostic| !diagnostic
            .code
            .starts_with("invalid.program:invalid.thread")),
        "{unrelated:#?}"
    );

    let shadowed = analyze(
        "from nagini_contracts.thread import Thread\nclass Local:\n    pass\nThread = Local\ndef run() -> Local:\n    return Thread()\n",
    );
    assert!(
        shadowed
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != INVALID_THREAD_CREATION),
        "{shadowed:#?}"
    );
}

#[test]
fn valid_get_method_comparison_and_arg_inside_get_old_are_not_misclassified() {
    let analysis = analyze(
        "from nagini_contracts.contracts import Requires\nfrom nagini_contracts.thread import Thread, getMethod, getOld, arg\ndef target(value: object) -> None:\n    pass\ndef run(thread: Thread) -> None:\n    Requires(getMethod(thread) == target)\n    Requires(getOld(thread, arg(0)) is not None)\n",
    );
    assert!(
        analysis.diagnostics.iter().all(|diagnostic| !matches!(
            diagnostic.code.as_str(),
            INVALID_GET_METHOD_USE | INVALID_ARG_USE
        )),
        "{analysis:#?}"
    );
}

#[test]
fn all_nine_pinned_thread_restrictions_match_every_frontend_exactly() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    for number in 1..=9 {
        let fixture = format!("tests/functional/translation/test_thread_{number}.py");
        let scalar = check_pinned_scalar_fixture(&suite, &pin, &fixture)
            .unwrap_or_else(|error| panic!("scalar {fixture}: {error}"));
        assert!(scalar.passed, "scalar {fixture}: {scalar:#?}");
        assert_eq!(
            scalar.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection,
            "scalar {fixture}: {scalar:#?}"
        );

        let heap = check_pinned_heap_fixture(&suite, &pin, &fixture)
            .unwrap_or_else(|error| panic!("heap {fixture}: {error}"));
        assert!(heap.passed, "heap {fixture}: {heap:#?}");
        assert_eq!(
            heap.analysis_kind,
            ConformanceMatchKind::SourceWellformednessRejection,
            "heap {fixture}: {heap:#?}"
        );

        let reference = check_pinned_reference_fixture(&suite, &pin, &fixture)
            .unwrap_or_else(|error| panic!("reference {fixture}: {error}"));
        assert!(reference.passed, "reference {fixture}: {reference:#?}");
    }
}

#[test]
fn early_thread_failures_never_export_a_proof_file() {
    let analysis = analyze(
        "from nagini_contracts.contracts import Pure\nfrom nagini_contracts.thread import Thread\n@Pure\ndef target() -> int:\n    return 1\ndef run() -> Thread:\n    return Thread(target=target, args=())\n",
    );
    assert_eq!(
        analysis.disposition,
        maledictus::FrontendDisposition::Unsupported
    );
    assert!(analysis.files.is_empty(), "{analysis:#?}");
    assert!(analysis.obligations.is_empty(), "{analysis:#?}");
    assert!(analysis.solver.is_none(), "{analysis:#?}");
}
