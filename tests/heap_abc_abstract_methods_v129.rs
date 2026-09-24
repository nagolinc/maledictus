use std::path::PathBuf;

use maledictus::conformance::{
    ConformanceMatchKind, check_pinned_heap_fixture, check_pinned_reference_fixture,
    check_pinned_scalar_fixture,
};
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::verify_heap_module;
use maledictus::vc::ObligationStatus;

const TARGET: &str = "tests/functional/verification/test_abc.py";

fn refusal(source: &str) -> ContractFailure {
    verify_heap_module(source, "abc.py", &[]).unwrap_err()
}

#[test]
fn abstract_contracts_participate_in_behavioral_subtyping() {
    let source = r#"
from nagini_contracts.contracts import *
from abc import ABC, ABCMeta, abstractmethod

class Base(ABC):
    def __init__(self) -> None:
        pass
    @abstractmethod
    def value(self) -> int:
        Ensures(Result() > 7)
        pass

class Strong(Base):
    def value(self) -> int:
        Ensures(Result() > 8)
        return 9

class Weak(Base):
    def value(self) -> int:
        Ensures(Result() > 5)
        return 6

class MetaBase(metaclass=ABCMeta):
    @abstractmethod
    def other(self) -> int:
        Ensures(Result() > 3)
        pass

class MetaConcrete(MetaBase):
    def other(self) -> int:
        Ensures(Result() > 4)
        return 5
"#;
    let result = verify_heap_module(source, "abc_overrides.py", &[]).unwrap();
    let failed = result
        .obligations
        .iter()
        .filter(|obligation| obligation.status != ObligationStatus::Proved)
        .collect::<Vec<_>>();
    assert_eq!(failed.len(), 1, "{result:#?}");
    assert_eq!(failed[0].status, ObligationStatus::Refuted, "{result:#?}");
    assert!(
        failed[0].id.contains("override:Weak.value:Base"),
        "{result:#?}"
    );
}

#[test]
fn abstractness_is_inherited_until_a_concrete_override() {
    let abstract_source = r#"
from nagini_contracts.contracts import *
from abc import ABC, abstractmethod
class Base(ABC):
    @abstractmethod
    def value(self) -> int:
        Ensures(Result() > 0)
        pass
class StillAbstract(Base):
    def __init__(self) -> None:
        pass
class Factory:
    def create(self) -> StillAbstract:
        return StillAbstract()
"#;
    let failure = refusal(abstract_source);
    assert_eq!(
        failure.code,
        "frontend.python.heap.abstract-class-instantiation"
    );

    let concrete_source = r#"
from nagini_contracts.contracts import *
from abc import ABC, abstractmethod
class Base(ABC):
    def __init__(self) -> None:
        pass
    @abstractmethod
    def value(self) -> int:
        Ensures(Result() > 0)
        pass
class Concrete(Base):
    def __init__(self) -> None:
        pass
    def value(self) -> int:
        Ensures(Result() > 0)
        return 1
class Factory:
    def create(self) -> Concrete:
        return Concrete()
"#;
    verify_heap_module(concrete_source, "abc_concrete.py", &[]).unwrap();
}

#[test]
fn canonical_provenance_and_declarative_bodies_are_required() {
    let cases = [
        (
            "from abc import ABC, abstractmethod as am\nclass Base(ABC):\n    @am\n    def value(self) -> int:\n        pass\n",
            "frontend.python.heap.abc-import-unsupported",
        ),
        (
            "class Base:\n    @abstractmethod\n    def value(self) -> int:\n        pass\n",
            "frontend.python.heap.abc-binding-unproven",
        ),
        (
            "from abc import abstractmethod\nclass Base:\n    @abstractmethod\n    def value(self) -> int:\n        pass\n",
            "frontend.python.heap.abstract-method-owner-unsupported",
        ),
        (
            "from abc import ABC, abstractmethod\nabstractmethod = 1\nclass Base(ABC):\n    @abstractmethod\n    def value(self) -> int:\n        pass\n",
            "frontend.python.heap.abc-binding-collision",
        ),
        (
            "from abc import ABC, abstractmethod\nclass Base(ABC):\n    @abstractmethod\n    def value(self) -> int:\n        return 1\n",
            "frontend.python.heap.abstract-method-body-unsupported",
        ),
        (
            "from abc import ABC\nclass Base(ABC, object):\n    pass\n",
            "frontend.python.heap.multiple-or-dynamic-inheritance-unsupported",
        ),
        (
            "class Meta:\n    pass\nclass Base(metaclass=Meta):\n    pass\n",
            "frontend.python.heap.class-shape-unsupported",
        ),
    ];
    for (source, expected) in cases {
        let failure = refusal(source);
        assert_eq!(failure.code, expected, "{source}\n{failure:#?}");
    }
}

#[test]
fn exact_pinned_abc_fixture_converts_and_the_metaclass_cohort_stays_matched() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let target = check_pinned_heap_fixture(&suite, &pin, TARGET).unwrap();
    assert!(target.passed, "{target:#?}");
    assert_eq!(target.expected, target.actual, "{target:#?}");
    assert_eq!(target.actual.len(), 1, "{target:#?}");
    assert_eq!(
        target.analysis_kind,
        ConformanceMatchKind::SemanticVerification
    );

    let metaclass = check_pinned_heap_fixture(
        &suite,
        &pin,
        "tests/functional/translation/test_metaclass.py",
    )
    .unwrap();
    assert!(metaclass.passed, "{metaclass:#?}");
    assert_eq!(metaclass.expected, metaclass.actual, "{metaclass:#?}");

    assert!(check_pinned_scalar_fixture(&suite, &pin, TARGET).is_err());
    assert!(check_pinned_reference_fixture(&suite, &pin, TARGET).is_err());
}
