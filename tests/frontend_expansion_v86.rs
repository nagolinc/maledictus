use maledictus::python_contracts::verify_contract_module;
use maledictus::python_heap_contracts::verify_heap_module;

#[test]
fn scalar_frontend_proves_finite_expansions_beyond_the_former_boundary() {
    let verification = verify_contract_module(
        "from nagini_contracts.contracts import *\n\ndef range_length() -> int:\n    Ensures(Result() == 5000)\n    return len(range(5000))\n\ndef repeated_bytes() -> bytes:\n    Ensures(len(Result()) == 5000)\n    return b'x' * 5000\n\ndef final_iteration() -> int:\n    Ensures(Result() == 4096)\n    result = -1\n    for value in range(4097):\n        result = value\n    return result\n",
        "scalar_expansions.py",
        &[],
    )
    .unwrap_or_else(|failure| {
        panic!(
            "scalar expansion unexpectedly refused with {}: {}",
            failure.code, failure.message
        )
    });

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn heap_frontend_proves_a_static_range_beyond_the_former_boundary() {
    let verification = verify_heap_module(
        "from nagini_contracts.contracts import *\n\nclass Marker:\n    pass\n\ndef range_length() -> int:\n    Ensures(Result() == 5000)\n    return len(range(5000))\n",
        "heap_range_expansion.py",
        &[],
    )
    .unwrap_or_else(|failure| {
        panic!(
            "heap range expansion unexpectedly refused with {}: {}",
            failure.code, failure.message
        )
    });

    assert!(verification.passed, "{verification:#?}");
}

#[test]
fn scalar_frontend_reports_machine_size_and_allocation_failures() {
    let oversized_range = verify_contract_module(
        "def invalid() -> int:\n    return len(range(-170141183460469231731687303715884105727, 170141183460469231731687303715884105727))\n",
        "oversized_scalar_range.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        oversized_range.code,
        "frontend.python.contracts.range-expansion-size-overflow"
    );

    let unallocatable_repeat = verify_contract_module(
        "def invalid() -> bytes:\n    return b'x' * 9223372036854775807\n",
        "unallocatable_bytes_repeat.py",
        &[],
    )
    .unwrap_err();
    assert_eq!(
        unallocatable_repeat.code,
        "frontend.python.contracts.bytes-repeat-allocation-failed"
    );
    assert!(
        unallocatable_repeat.message.contains("9223372036854775807"),
        "{}",
        unallocatable_repeat.message
    );
}

#[test]
fn heap_frontend_reports_machine_size_failure_for_static_ranges() {
    let failure = verify_heap_module(
        "class Marker:\n    pass\n\ndef invalid() -> int:\n    return len(range(-170141183460469231731687303715884105727, 170141183460469231731687303715884105727))\n",
        "oversized_heap_range.py",
        &[],
    )
    .unwrap_err();

    assert_eq!(
        failure.code,
        "frontend.python.heap.range-expansion-size-overflow"
    );

    let unallocatable_source = format!(
        "class Marker:\n    pass\n\ndef invalid() -> int:\n    return len(range(0, {}))\n",
        usize::MAX
    );
    let failure =
        verify_heap_module(&unallocatable_source, "unallocatable_heap_range.py", &[]).unwrap_err();
    assert_eq!(
        failure.code,
        "frontend.python.heap.range-expansion-allocation-failed"
    );
    assert!(
        failure.message.contains(&usize::MAX.to_string()),
        "{}",
        failure.message
    );
}
