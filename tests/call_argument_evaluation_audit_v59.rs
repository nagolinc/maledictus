use maledictus::python_heap_contracts::{HeapContractVerification, verify_heap_module};

fn verify_heap(source: &str, path: &str) -> HeapContractVerification {
    verify_heap_module(source, path, &[]).unwrap_or_else(|failure| {
        panic!(
            "expected {path} to lower, but it was refused with {}: {}",
            failure.code, failure.message
        )
    })
}

#[test]
fn an_earlier_heap_read_is_frozen_before_a_later_argument_mutates_the_heap() {
    let verification = verify_heap(
        r#"from nagini_contracts.contracts import *

class Counter:
    value: int

    def __init__(self) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == 1)
        self.value = 1

    def advance(self) -> int:
        Requires(Acc(self.value))
        Requires(self.value == 1)
        Ensures(Acc(self.value))
        Ensures(self.value == 2)
        Ensures(Result() == 2)
        self.value = 2
        return 2

def encode(first: int, second: int) -> int:
    return first * 10 + second

def run() -> None:
    counter = Counter()
    result = encode(counter.value, counter.advance())
    Assert(result == 12)
    Assert(counter.value == 2)
"#,
        "v59_read_before_effectful_argument.py",
    );

    assert!(verification.passed, "{verification:#?}");
    let assertions = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":assert:"))
        .collect::<Vec<_>>();
    assert_eq!(assertions.len(), 2, "{verification:#?}");
    assert!(
        assertions.iter().all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn fixed_star_tuple_elements_are_evaluated_left_to_right_exactly_once() {
    let verification = verify_heap(
        r#"from nagini_contracts.contracts import *

class Counter:
    value: int

    def __init__(self) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == 0)
        self.value = 0

    def first(self) -> int:
        Requires(Acc(self.value))
        Requires(self.value == 0)
        Ensures(Acc(self.value))
        Ensures(self.value == 1)
        Ensures(Result() == 1)
        self.value = 1
        return 1

    def second(self) -> int:
        Requires(Acc(self.value))
        Requires(self.value == 1)
        Ensures(Acc(self.value))
        Ensures(self.value == 2)
        Ensures(Result() == 2)
        self.value = 2
        return 2

    def third(self) -> int:
        Requires(Acc(self.value))
        Requires(self.value == 2)
        Ensures(Acc(self.value))
        Ensures(self.value == 3)
        Ensures(Result() == 3)
        self.value = 3
        return 3

def encode(first: int, second: int, *, third: int) -> int:
    return first * 100 + second * 10 + third

def run() -> None:
    counter = Counter()
    result = encode(*(counter.first(), counter.second()), third=counter.third())
    Assert(result == 123)
    Assert(counter.value == 3)
"#,
        "v59_fixed_star_effectful_elements.py",
    );

    assert!(verification.passed, "{verification:#?}");
    let assertions = verification
        .obligations
        .iter()
        .filter(|obligation| obligation.id.contains(":assert:"))
        .collect::<Vec<_>>();
    assert_eq!(assertions.len(), 2, "{verification:#?}");
    assert!(
        assertions.iter().all(|obligation| obligation.satisfied()),
        "{verification:#?}"
    );
}

#[test]
fn an_effectful_receiver_expression_refuses_before_outer_binding() {
    let failure = verify_heap_module(
        r#"from nagini_contracts.contracts import *

class Leaf:
    value: int

    def __init__(self) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == 2)
        self.value = 2

    @Pure
    def read(self) -> int:
        return 2

class Holder:
    leaf: Leaf
    stage: int

    def __init__(self) -> None:
        Ensures(Acc(self.leaf))
        Ensures(Acc(self.leaf.value))
        Ensures(Acc(self.stage))
        Ensures(self.stage == 0)
        self.leaf = Leaf()
        self.stage = 0

    def prepare_receiver(self) -> Leaf:
        Requires(Acc(self.leaf))
        Requires(Acc(self.leaf.value))
        Requires(Acc(self.stage))
        Requires(self.stage == 0)
        Ensures(Acc(self.leaf))
        Ensures(Acc(self.leaf.value))
        Ensures(Acc(self.stage))
        Ensures(self.stage == 1)
        self.stage = 1
        return self.leaf

def run() -> None:
    holder = Holder()
    result = holder.prepare_receiver().read()
    Assert(result == 2)
    Assert(holder.stage == 1)
"#,
        "v59_effectful_receiver_once.py",
        &[],
    )
    .expect_err("effectful receiver chains are outside the direct receiver call-binding seam");

    assert_eq!(
        failure.code, "frontend.python.heap.reference-chain-member-unresolved",
        "{failure:#?}"
    );
}

#[test]
fn explicit_exceptional_constructors_cannot_be_abstracted_as_argument_values() {
    let class_and_constructor = r#"from nagini_contracts.contracts import *

class Failure(Exception):
    pass

class Item:
    def __init__(self) -> None:
        Exsures(Failure, True)

class Consumer:
    def accept(self, item: object) -> int:
        return 1
"#;

    let method_source = format!(
        "{class_and_constructor}\ndef run() -> None:\n    consumer = Consumer()\n    observed = consumer.accept(Item())\n"
    );
    let method_failure = verify_heap_module(
        &method_source,
        "v59_exceptional_constructor_method_argument.py",
        &[],
    )
    .expect_err("an explicit exceptional constructor cannot be an abstract method argument");
    assert_eq!(
        method_failure.code, "frontend.python.heap.call-argument-constructor-effects-unsupported",
        "{method_failure:#?}"
    );

    let scalar_source = format!(
        "{class_and_constructor}\ndef accept(item: object) -> int:\n    return 1\n\ndef run() -> None:\n    observed = accept(Item())\n"
    );
    let scalar_failure = verify_heap_module(
        &scalar_source,
        "v59_exceptional_constructor_scalar_argument.py",
        &[],
    )
    .expect_err("an explicit exceptional constructor cannot be an abstract scalar argument");
    assert_eq!(
        scalar_failure.code, "frontend.python.heap.call-argument-constructor-effects-unsupported",
        "{scalar_failure:#?}"
    );
}
