use std::path::Path;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::verify_contract_module;

const RECURSIVE_TERMINATION_FIXTURE: &str =
    "tests/obligations/verification/chalice2silver/christian/lt_fib.py";

fn recursive_termination_source() -> &'static str {
    "from nagini_contracts.contracts import Requires\nfrom nagini_contracts.obligations import *\n\nclass Counter:\n    def calculate(self, value: int) -> int:\n        Requires(MustTerminate(value))\n        if value <= 1:\n            return 1\n        elif value == 2:\n            return 2\n        else:\n            previous = self.calculate(value - 1)\n            earlier = self.calculate(value - 2)\n            return earlier + previous\n"
}

fn assert_not_verified(source: &str) {
    assert!(
        !verify_contract_module(source, "recursive_termination_drift.py", &[])
            .is_ok_and(|verification| verification.passed),
        "unsupported or non-decreasing recursion verified:\n{source}"
    );
}

#[test]
fn recursive_integer_measures_are_positive_and_strictly_decreasing() {
    let verified = verify_contract_module(
        recursive_termination_source(),
        "recursive_termination.py",
        &[],
    )
    .unwrap();
    assert!(verified.passed, "{verified:#?}");
    assert_eq!(verified.functions, ["Counter.calculate"]);
    assert_eq!(verified.obligations.len(), 4, "{verified:#?}");
    assert!(
        verified
            .obligations
            .iter()
            .all(|obligation| obligation.id.contains("recursive-call"))
    );
}

#[test]
fn recursive_termination_rejects_open_dispatch_effects_and_bad_measures() {
    for changed in [
        recursive_termination_source().replace("class Counter:", "class Counter(Base):"),
        recursive_termination_source().replace(
            "Requires(MustTerminate(value))",
            "Requires(MustTerminate(value))\n        self.state = value",
        ),
        recursive_termination_source().replace("value - 1", "value + 1"),
        recursive_termination_source().replace("value - 2", "value - 4"),
        recursive_termination_source().replace("self.calculate(value - 1)", "other(value - 1)"),
        recursive_termination_source()
            .replace("return earlier + previous", "return earlier + earlier"),
        recursive_termination_source().replace(
            "from nagini_contracts.obligations import *",
            "from nagini_contracts.obligations import MustTerminate",
        ),
    ] {
        assert_not_verified(&changed);
    }
}

#[test]
fn exact_pinned_lt_fib_fixture_matches() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_scalar_fixture(&suite, &pin, RECURSIVE_TERMINATION_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
}
