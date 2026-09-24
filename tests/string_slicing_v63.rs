use maledictus::python_contracts::{ContractFailure, verify_contract_module};
use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify_heap(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it refused with {}: {}",
            failure.code, failure.message
        )
    })
}

fn refuse_heap(source: &str, path: &str) -> ContractFailure {
    verify_heap_module(source, path, &[])
        .expect_err("unsupported string slicing must refuse before proof issuance")
}

#[test]
fn static_string_slices_follow_python_bounds_steps_and_unicode_code_points() {
    let verification = verify_heap(
        r#"def run() -> None:
    text = "aé🙂z"
    whole = text[:]
    middle = text[1:3]
    reverse = text[::-1]
    stride = text[::2]
    clipped = text[-100:100]
    empty = text[3:1]
    nested = text[1:][::-1]
    ascii_middle = "abcdef"[1:4]
    assert whole == "aé🙂z"
    assert len(whole) == 4
    assert middle == "é🙂"
    assert len(middle) == 2
    assert reverse == "z🙂éa"
    assert stride == "a🙂"
    assert clipped == text
    assert empty == ""
    assert nested == "z🙂é"
    assert len(ascii_middle) == 3
    assert ascii_middle == "bcd"
"#,
        "v63_static_string_slices.py",
    );

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn scalar_and_heap_frontends_share_exact_static_string_slice_semantics() {
    let source = r#"from nagini_contracts.contracts import *

def selected() -> str:
    Ensures(Result() == "db")
    return "abcdef"[3:0:-2]

def empty() -> str:
    Ensures(Result() == "")
    return "abcdef"[:-1:-1]
"#;

    let scalar = verify_contract_module(source, "v63_scalar_string_slices.py", &[])
        .unwrap_or_else(|failure| panic!("scalar string slicing refused: {failure:#?}"));
    assert!(scalar.passed, "{scalar:#?}");

    let heap = verify_heap(source, "v63_heap_string_slices.py");
    assert!(heap.passed, "{heap:#?}");
}

#[test]
fn symbolic_values_dynamic_bounds_zero_steps_and_indexing_remain_fail_closed() {
    for (source, code) in [
        (
            "def run(value: str) -> str:\n    return value[:]\n",
            "frontend.python.heap.slice-symbolic-sequence-unsupported",
        ),
        (
            "def run(start: int) -> str:\n    value = 'abc'\n    return value[start:]\n",
            "frontend.python.heap.slice-bound-unsupported",
        ),
        (
            "def run() -> str:\n    return 'abc'[::0]\n",
            "frontend.python.heap.slice-step-zero",
        ),
        (
            "def run() -> None:\n    value = 'abc'[0]\n",
            "frontend.python.heap.subscript-type-unsupported",
        ),
    ] {
        let failure = refuse_heap(source, "v63_string_slice_adversary.py");
        assert_eq!(failure.code, code, "{failure:#?}");
    }

    let scalar = verify_contract_module(
        "def run(value: str) -> str:\n    return value[:]\n",
        "v63_scalar_symbolic_string_slice.py",
        &[],
    )
    .expect_err("the scalar frontend must also refuse symbolic string slicing");
    assert_eq!(
        scalar.code, "frontend.python.contracts.slice-symbolic-sequence-unsupported",
        "{scalar:#?}"
    );
}
