#[test]
fn issue_00049_finite_dict_keys_matches_nagini() {
    let source = concat!(
        "# Any copyright is dedicated to the Public Domain.\n",
        "# http://creativecommons.org/publicdomain/zero/1.0/\n",
        "\n",
        "def test() -> None:\n",
        "    a = {1: '1'}\n",
        "    b = a.keys()\n",
    );
    let result = maledictus::conformance::check_scalar_source(
        source,
        "tests/functional/verification/issues/00049.py",
    )
    .unwrap();
    assert!(result.passed);
    assert!(result.expected.is_empty());
    assert!(result.actual.is_empty());
}
