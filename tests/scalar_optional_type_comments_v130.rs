use std::path::Path;

use maledictus::conformance::check_pinned_scalar_fixture;
use maledictus::python_contracts::verify_contract_module;

const OPTIONAL_TYPE_COMMENT_FIXTURE: &str = "tests/functional/verification/issues/00044.py";

#[test]
fn optional_type_comments_accept_none_and_the_exact_member_type() {
    let source = "from typing import Optional\n\ndef values() -> None:\n    absent = None  # type: Optional[int]\n    present = 7  # type: Optional[int]\n    assert absent == None\n    assert present == 7\n";
    let result = verify_contract_module(source, "optional_values.py", &[]).unwrap();
    assert!(result.passed, "{result:#?}");
}

#[test]
fn optional_type_comments_fail_closed_for_wrong_or_unknown_members() {
    for (source, expected_code) in [
        (
            "from typing import Optional\n\ndef wrong() -> None:\n    value = 'seven'  # type: Optional[int]\n",
            "frontend.python.contracts.type-mismatch",
        ),
        (
            "from typing import Optional\n\ndef wrong() -> None:\n    value = None  # type: Optional[complex]\n",
            "frontend.python.contracts.type-comment-unsupported",
        ),
        (
            "def wrong() -> None:\n    value = None  # type: int\n",
            "frontend.python.contracts.type-mismatch",
        ),
    ] {
        let error = verify_contract_module(source, "invalid_optional.py", &[]).unwrap_err();
        assert_eq!(error.code, expected_code, "{error:#?}");
    }
}

#[test]
fn exact_pinned_optional_type_comment_fixture_matches() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let result = check_pinned_scalar_fixture(&suite, &pin, OPTIONAL_TYPE_COMMENT_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar fixture was refused: {error}"));

    assert!(result.passed, "{result:#?}");
    assert!(result.expected.is_empty(), "{result:#?}");
    assert_eq!(result.actual, result.expected, "{result:#?}");
}
