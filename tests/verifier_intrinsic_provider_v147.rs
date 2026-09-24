use std::path::Path;

use maledictus::python_verifier_intrinsics::{
    CANONICAL_OBLIGATIONS_MODULE, VerifierIntrinsicKind, VerifierIntrinsicType,
    is_canonical_obligations_provider_path, validate_canonical_obligations_provider,
};

const PROVIDER: &str = include_str!("../.upstream/nagini/src/nagini_contracts/obligations.py");

#[test]
fn canonical_pinned_obligations_provider_exports_typed_intrinsics() {
    let provider =
        validate_canonical_obligations_provider(PROVIDER, "src/nagini_contracts/obligations.py")
            .expect("the pinned Nagini obligations ABI must be recognized exactly");

    assert_eq!(provider.module, CANONICAL_OBLIGATIONS_MODULE);
    assert_eq!(
        provider.public_exports.into_iter().collect::<Vec<_>>(),
        vec![
            "Level",
            "LevelType",
            "MustRelease",
            "MustTerminate",
            "WaitLevel",
        ]
    );
    assert_eq!(
        provider.functions["Level"].kind,
        VerifierIntrinsicKind::Level
    );
    assert_eq!(
        provider.functions["Level"].result,
        VerifierIntrinsicType::Level
    );
    assert_eq!(
        provider.functions["WaitLevel"].canonical_identity,
        "nagini_contracts.obligations.WaitLevel"
    );
    assert_eq!(
        provider.classes["LevelType"].methods["__lt__"].result,
        VerifierIntrinsicType::Bool
    );
    assert!(provider.classes["BaseLock"].methods.is_empty());
}

#[test]
fn only_exact_canonical_provider_path_selects_intrinsic_origin() {
    let root = Path::new("C:/pinned/nagini");
    assert!(is_canonical_obligations_provider_path(
        root,
        CANONICAL_OBLIGATIONS_MODULE,
        Path::new("C:/pinned/nagini/src/nagini_contracts/obligations.py")
    ));
    for (module, path) in [
        (
            "nagini_contracts.obligations",
            "C:/pinned/nagini/tests/nagini_contracts/obligations.py",
        ),
        (
            "application.obligations",
            "C:/pinned/nagini/src/nagini_contracts/obligations.py",
        ),
        (
            "nagini_contracts.obligations",
            "C:/other/nagini/src/nagini_contracts/obligations.py",
        ),
    ] {
        assert!(
            !is_canonical_obligations_provider_path(root, module, Path::new(path)),
            "module {module:?} at {path:?} must remain ordinary source"
        );
    }
}

#[test]
fn canonical_provider_rejects_import_export_and_rebinding_drift() {
    for (name, source) in [
        (
            "typing alias",
            PROVIDER.replace(
                "from typing import Union",
                "from typing import Union as Either",
            ),
        ),
        (
            "thread alias",
            PROVIDER.replace(
                "from nagini_contracts.thread import Thread",
                "from nagini_contracts.thread import Thread as Worker",
            ),
        ),
        (
            "metadata export order",
            PROVIDER.replace("'MustTerminate'", "'MustTerminateRenamed'"),
        ),
        ("rebinding", format!("{PROVIDER}\nLevel = WaitLevel\n")),
        (
            "star exports",
            PROVIDER.replace("__all__ = (", "__all__ = ('BaseLock',"),
        ),
    ] {
        assert!(
            validate_canonical_obligations_provider(&source, &format!("{name}.py")).is_err(),
            "{name} must invalidate the verifier ABI"
        );
    }
}

#[test]
fn canonical_provider_rejects_class_and_signature_drift() {
    for (name, source) in [
        (
            "base class",
            PROVIDER.replace("class BaseLock:", "class BaseLock(object):"),
        ),
        (
            "comparison annotation",
            PROVIDER.replace(
                "def __lt__(self, other: 'LevelType') -> bool:",
                "def __lt__(self, other: 'LevelType') -> int:",
            ),
        ),
        (
            "level union",
            PROVIDER.replace(
                "def Level(l: Union[BaseLock, Thread]) -> LevelType:",
                "def Level(l: BaseLock) -> LevelType:",
            ),
        ),
        (
            "release default",
            PROVIDER.replace(
                "def MustRelease(lock: BaseLock, measure: int = None) -> bool:",
                "def MustRelease(lock: BaseLock, measure: int = 1) -> bool:",
            ),
        ),
        (
            "termination parameter",
            PROVIDER.replace(
                "def MustTerminate(measure: int) -> bool:",
                "def MustTerminate(value: int) -> bool:",
            ),
        ),
    ] {
        assert!(
            validate_canonical_obligations_provider(&source, &format!("{name}.py")).is_err(),
            "{name} must invalidate the verifier ABI"
        );
    }
}

#[test]
fn canonical_provider_rejects_executable_intrinsic_bodies() {
    for (name, source) in [
        (
            "level comparison",
            PROVIDER.replace(
                "        \"\"\"We allow to compare only ``LevelType`` objects.\"\"\"",
                "        return True",
            ),
        ),
        (
            "wait level",
            PROVIDER.replace(
                "    \"\"\"The wait level of the current thread.\"\"\"",
                "    raise RuntimeError()",
            ),
        ),
        (
            "must terminate",
            PROVIDER.replace(
                "    \"\"\"An obligation to terminate in ``measure`` steps.\"\"\"",
                "    return measure > 0",
            ),
        ),
    ] {
        let error = validate_canonical_obligations_provider(&source, &format!("{name}.py"))
            .expect_err("executable verifier-library behavior must not become an intrinsic");
        assert_eq!(
            error.code,
            "frontend.python.verifier-intrinsic.executable-body-refused"
        );
    }
}
