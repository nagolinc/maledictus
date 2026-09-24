use maledictus::python_heap_contracts::verify_heap_module;

#[test]
fn constructors_are_not_rejected_after_sixty_four_paths() {
    let mut source = String::from(
        "from nagini_contracts.contracts import *\n\nclass Cell:\n    value: int\n    def __init__(self, a: bool, b: bool, c: bool, d: bool, e: bool, f: bool, g: bool) -> None:\n        Ensures(Acc(self.value))\n",
    );
    for flag in ["a", "b", "c", "d", "e", "f", "g"] {
        source.push_str(&format!(
            "        if {flag}:\n            pass\n        else:\n            pass\n"
        ));
    }
    source.push_str("        self.value = 0\n");

    let result = verify_heap_module(&source, "constructor_many_paths.py", &[])
        .expect("constructor path exploration must not have an arbitrary fixed cutoff");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn reusable_pure_summaries_are_not_rejected_after_sixty_four_paths() {
    let mut source = String::from(
        "from nagini_contracts.contracts import *\n\n@Pure\ndef choose(a: bool, b: bool, c: bool, d: bool, e: bool, f: bool, g: bool) -> int:\n",
    );
    for flag in ["a", "b", "c", "d", "e", "f", "g"] {
        source.push_str(&format!(
            "    if {flag}:\n        selected_{flag} = 1\n    else:\n        selected_{flag} = 0\n"
        ));
    }
    source.push_str(
        "    return selected_a * 64 + selected_b * 32 + selected_c * 16 + selected_d * 8 + selected_e * 4 + selected_f * 2 + selected_g\n\nclass Marker:\n    pass\n\ndef run(a: bool, b: bool, c: bool, d: bool, e: bool, f: bool, g: bool) -> None:\n    answer = choose(a, b, c, d, e, f, g)\n    Assert(Implies(a and b and c and d and e and f and g, answer == 127))\n    Assert(Implies(not a and not b and not c and not d and not e and not f and not g, answer == 0))\n",
    );

    let result = verify_heap_module(&source, "pure_summary_many_paths.py", &[])
        .expect("pure-summary path exploration must not have an arbitrary fixed cutoff");
    assert!(result.passed, "{result:#?}");
}

#[test]
fn match_statements_are_not_rejected_after_sixty_four_cases() {
    let mut source = String::from(
        "from nagini_contracts.contracts import *\n\ndef choose(value: int) -> int:\n    match value:\n",
    );
    for value in 0..70 {
        source.push_str(&format!(
            "        case {value}:\n            return {value}\n"
        ));
    }
    source.push_str("        case _:\n            return value\n");

    let result = verify_heap_module(&source, "match_many_cases.py", &[])
        .expect("match path exploration must not have an arbitrary fixed cutoff");
    assert!(result.passed, "{result:#?}");
}
