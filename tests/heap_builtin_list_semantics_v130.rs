use std::path::PathBuf;

use maledictus::conformance::{check_heap_source, check_pinned_heap_fixture};
use maledictus::python_contracts::ContractFailure;
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to verify, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refusal(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("unsupported list behavior must refuse before proof issuance")
}

#[test]
fn canonical_constructors_create_empty_and_independent_copy_allocations() {
    let result = verify(
        r#"from typing import List
def run() -> None:
    empty = list()  # type: List[int]
    source = [1, 2, 3]
    copied = list(source)
    assert len(empty) == 0
    assert copied is not source
    source[0] = 9
    copied[1] = 8
    assert source[0] == 9
    assert source[1] == 2
    assert copied[0] == 1
    assert copied[1] == 8
"#,
        "builtin_list_copy.py",
    );
    assert!(result.passed, "{result:#?}");
}

#[test]
fn exact_extend_concat_and_repeat_preserve_order_and_source_values() {
    let result = verify(
        r#"def run() -> None:
    left = [1, 2]
    right = [3, 4]
    combined = left + right
    repeated = left * 3
    reflected = 2 * right
    left.extend(right)
    assert left == [1, 2, 3, 4]
    assert right == [3, 4]
    assert combined == [1, 2, 3, 4]
    assert repeated == [1, 2, 1, 2, 1, 2]
    assert reflected == [3, 4, 3, 4]
    assert left is not combined
"#,
        "builtin_list_operations.py",
    );
    assert!(result.passed, "{result:#?}");
}

#[test]
fn aliases_shadows_dynamic_iterables_and_unsupported_shapes_fail_closed() {
    let cases = [
        (
            "def run() -> None:\n    values = [1, 2]\n    alias = values\n    values.append(3)\n",
            "list_alias.py",
            "frontend.python.heap.list-mutation-alias-unsupported",
        ),
        (
            "from typing import List\ndef run(list: int) -> None:\n    values = list()  # type: List[int]\n",
            "list_shadow.py",
            "frontend.python.heap.builtin-list-shadowed",
        ),
        (
            "def run() -> None:\n    values = list(1)\n",
            "list_noniterable.py",
            "frontend.python.heap.list-constructor-iterable-unsupported",
        ),
        (
            "def run() -> None:\n    values = [1]\n    copied = list(values, values)\n",
            "list_arity.py",
            "frontend.python.heap.list-constructor-arguments-unsupported",
        ),
        (
            "def make() -> list[int]:\n    return [1]\ndef run() -> None:\n    copied = list(make())\n",
            "list_effectful_iterable.py",
            "frontend.python.heap.list-constructor-iterable-unsupported",
        ),
        (
            "def run(count: int) -> None:\n    values = [1] * count\n",
            "list_symbolic_repeat.py",
            "frontend.python.heap.list-repeat-operand-type-mismatch",
        ),
        (
            "def run() -> None:\n    values = [1]\n    values.extend(2)\n",
            "list_extend_noniterable.py",
            "frontend.python.heap.list-extend-iterable-unsupported",
        ),
    ];
    for (source, path, expected) in cases {
        let failure = refusal(source, path);
        assert_eq!(failure.code, expected, "{path}: {failure:#?}");
    }
}

#[test]
fn annotation_lexer_ignores_commented_code_and_string_lookalikes() {
    let source = r##"def run() -> None:
    marker = "#:: ExpectedOutput(assert.failed:assertion.false)"
    #:: ExpectedOutput(assert.failed:assertion.false)
    assert False
    #     #:: ExpectedOutput(assert.failed:assertion.false)
    #     assert False
"##;
    let result = check_heap_source(source, "annotation_comment_boundary.py").unwrap();
    assert!(result.passed, "{result:#?}");
    assert_eq!(result.expected, result.actual, "{result:#?}");
    assert_eq!(result.expected.len(), 1, "{result:#?}");
}

#[test]
fn exact_list_fixture_converts_and_the_constructor_cohort_stays_fail_closed() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");
    let target =
        check_pinned_heap_fixture(&suite, &pin, "tests/functional/verification/test_lists.py")
            .unwrap();
    assert!(target.passed, "{target:#?}");
    assert_eq!(target.expected, target.actual, "{target:#?}");
    assert_eq!(target.actual.len(), 12, "{target:#?}");

    let pbyteseq = check_pinned_heap_fixture(
        &suite,
        &pin,
        "tests/functional/verification/test_pbyteseq.py",
    )
    .expect_err("PByteSeq runtime semantics remain outside exact builtin-list construction");
    assert!(
        pbyteseq.starts_with("frontend.python.heap.expression-unsupported:"),
        "{pbyteseq}"
    );
}
