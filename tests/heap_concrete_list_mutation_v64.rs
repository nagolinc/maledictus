use std::path::PathBuf;

use maledictus::conformance::check_pinned_heap_fixture;
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refusal(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("unsupported concrete-list mutation must refuse before proof issuance")
}

#[test]
fn finite_local_list_store_append_and_membership_update_the_exact_value() {
    let verification = verify(
        r#"def run() -> None:
    values = [1, 2, 3]
    values[-1] = values[0] + values[1]
    values.append(4)
    list.append(values, 5)
    assert values[2] == 3
    assert values[-1] == 5
    assert len(values) == 5
    assert 4 in values
    assert 9 not in values
"#,
        "v64_concrete_list_mutation.py",
    );

    assert!(verification.passed, "{verification:#?}");
    assert_eq!(
        verification
            .obligations
            .iter()
            .filter(|obligation| obligation.id.contains(":assert:"))
            .count(),
        5,
        "{verification:#?}"
    );
}

#[test]
fn canonical_int_add_preserves_python_bool_as_int_behavior() {
    let verification = verify(
        r#"def run() -> None:
    total = int.__add__(True, 4)
    assert total == 5
"#,
        "v64_canonical_int_add.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn list_mutation_refuses_dynamic_indices_aliases_bad_elements_and_shadowed_builtins() {
    for (source, path, code) in [
        (
            "def run(index: int) -> None:\n    values = [1, 2]\n    values[index] = 3\n",
            "v64_dynamic_store_index.py",
            "frontend.python.heap.list-mutation-index-unsupported",
        ),
        (
            "def run() -> None:\n    values = [1, 2]\n    alias = values\n    values.append(3)\n",
            "v64_aliased_append.py",
            "frontend.python.heap.list-mutation-alias-unsupported",
        ),
        (
            "def run() -> None:\n    values = [1, 2]\n    wrapped = (values,)\n    values.append(3)\n",
            "v64_nested_aliased_append.py",
            "frontend.python.heap.list-mutation-alias-unsupported",
        ),
        (
            "def run() -> None:\n    values = [1, 2]\n    values.append('wrong')\n",
            "v64_append_element_mismatch.py",
            "frontend.python.heap.list-mutation-element-type-mismatch",
        ),
        (
            "def run(list: int) -> None:\n    values = [1, 2]\n    list.append(values, 3)\n",
            "v64_shadowed_list.py",
            "frontend.python.heap.builtin-method-shadowed",
        ),
        (
            "def run(int: int) -> None:\n    total = int.__add__(1, 2)\n",
            "v64_shadowed_int.py",
            "frontend.python.heap.builtin-method-shadowed",
        ),
    ] {
        let failure = refusal(source, path);
        assert_eq!(failure.code, code, "{path}: {failure:#?}");
    }
}

#[test]
fn builtin_method_arity_and_out_of_range_stores_fail_closed() {
    for (source, path, code) in [
        (
            "def run() -> None:\n    values = [1]\n    values.append(2, 3)\n",
            "v64_append_arity.py",
            "frontend.python.heap.list-append-arguments-unsupported",
        ),
        (
            "def run() -> None:\n    total = int.__add__(1)\n",
            "v64_int_add_arity.py",
            "frontend.python.heap.builtin-method-arguments-unsupported",
        ),
        (
            "def run() -> None:\n    values = [1]\n    values[1] = 2\n",
            "v64_store_out_of_range.py",
            "frontend.python.heap.sequence-index-out-of-range",
        ),
    ] {
        let failure = refusal(source, path);
        assert_eq!(failure.code, code, "{path}: {failure:#?}");
    }
}

#[test]
fn exact_upstream_concrete_list_fixtures_match() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (fixture, expected_diagnostics) in [
        ("tests/sif-true/translation/test_lists.py", 0),
        ("tests/functional/verification/issues/00242.py", 2),
    ] {
        let result = check_pinned_heap_fixture(
            &repository.join(".upstream/nagini"),
            &repository.join("conformance/nagini-v1.3.1.json"),
            fixture,
        )
        .unwrap_or_else(|error| panic!("exact upstream fixture {fixture} was refused: {error}"));

        assert!(result.passed, "{result:#?}");
        assert_eq!(result.expected, result.actual);
        assert_eq!(result.actual.len(), expected_diagnostics);
    }
}
