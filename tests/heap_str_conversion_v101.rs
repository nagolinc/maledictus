use std::path::Path;

use maledictus::conformance::{
    check_pinned_heap_fixture, check_pinned_reference_fixture, check_pinned_scalar_fixture,
};
use maledictus::python_heap_contracts::verify_heap_module;

const STR_CONVERSION_FIXTURE: &str = "tests/functional/verification/issues/00282.py";

#[test]
fn canonical_str_converts_exact_primitives_with_python_spelling() {
    let verification = verify_heap_module(
        r#"def run(flag: bool, text: str) -> None:
    assert str() == ''
    assert str(0) == '0'
    assert str(-2048) == '-2048'
    assert str(True) == 'True'
    assert str(False) == 'False'
    assert str(flag) == ('True' if flag else 'False')
    assert str(text) == text
"#,
        "primitive_str_conversion.py",
        &[],
    )
    .expect("canonical str conversion should lower supported primitive values");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn exact_module_constants_flow_through_str_conversion() {
    let verification = verify_heap_module(
        r#"from nagini_contracts.contracts import Assert

ANSWER = 42

def run() -> None:
    converted = str(ANSWER)
    Assert(converted == '42')
"#,
        "module_constant_str_conversion.py",
        &[],
    )
    .expect("exact module constants should retain their value through str conversion");
    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn string_conversion_preserves_heap_read_permissions() {
    let verification = verify_heap_module(
        r#"from nagini_contracts.contracts import Acc, Assert, Ensures, Requires

class Cell:
    text: str

    def __init__(self, text: str) -> None:
        self.text = text
        Ensures(Acc(self.text))
        Ensures(self.text == text)

def run(cell: Cell) -> None:
    Requires(Acc(cell.text))
    Assert(str(cell.text) == cell.text)
"#,
        "field_string_conversion.py",
        &[],
    )
    .expect("string conversion should retain the field-read obligation");
    assert!(verification.passed, "{verification:#?}");

    let missing_permission = verify_heap_module(
        r#"from nagini_contracts.contracts import Assert

class Cell:
    text: str

def run(cell: Cell) -> None:
    Assert(str(cell.text) == cell.text)
"#,
        "field_string_conversion_without_permission.py",
        &[],
    )
    .expect("missing read permission should be an ordinary refuted obligation");
    assert!(!missing_permission.passed, "{missing_permission:#?}");
}

#[test]
fn symbolic_integer_and_malformed_str_calls_fail_closed() {
    let symbolic = verify_heap_module(
        "def run(value: int) -> None:\n    converted = str(value)\n",
        "symbolic_integer_str.py",
        &[],
    )
    .expect_err("symbolic integer formatting is not represented by the current proof terms");
    assert_eq!(
        symbolic.code,
        "frontend.python.heap.str-conversion-symbolic-unsupported"
    );

    let too_many = verify_heap_module(
        "def run() -> None:\n    converted = str(1, 2)\n",
        "str_too_many_arguments.py",
        &[],
    )
    .expect_err("str has a fixed zero-or-one-argument signature");
    assert_eq!(too_many.code, "frontend.python.heap.str-arguments");

    let keyword = verify_heap_module(
        "def run() -> None:\n    converted = str(object=1)\n",
        "str_keyword_argument.py",
        &[],
    )
    .expect_err("the canonical str object argument is positional-only");
    assert_eq!(keyword.code, "frontend.python.heap.str-arguments");
}

#[test]
fn lexical_shadowing_never_invokes_the_canonical_str_model() {
    let shadowed = verify_heap_module(
        "def run() -> None:\n    str = 1\n    converted = str(2)\n",
        "shadowed_str.py",
        &[],
    )
    .expect_err("a lexical value named str is not the canonical builtin");
    assert_eq!(shadowed.code, "frontend.python.heap.str-shadowed");
}

#[test]
fn upstream_string_identity_fixture_stays_closed_in_the_heap_backend() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let suite = repository.join(".upstream/nagini");
    let pin = repository.join("conformance/nagini-v1.3.1.json");

    let heap = check_pinned_heap_fixture(&suite, &pin, STR_CONVERSION_FIXTURE)
        .expect_err("string allocation identity cannot be replaced by value equality");
    assert!(
        heap.contains("frontend.python.heap.string-identity-unsupported"),
        "{heap}"
    );

    let scalar = check_pinned_scalar_fixture(&suite, &pin, STR_CONVERSION_FIXTURE)
        .unwrap_or_else(|error| panic!("scalar {STR_CONVERSION_FIXTURE}: {error}"));
    assert!(scalar.passed, "{scalar:#?}");
    assert_eq!(scalar.expected, scalar.actual, "{scalar:#?}");

    let reference = check_pinned_reference_fixture(&suite, &pin, STR_CONVERSION_FIXTURE)
        .expect_err("primitive module statements remain outside the reference backend");
    assert!(
        reference.contains("frontend.python.references.module-runtime-state-unsupported"),
        "{reference}"
    );
}
