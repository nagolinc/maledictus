use maledictus::python_heap_contracts::{
    parse_external_heap_contract_module, verify_heap_module_with_imports,
};

const PROVIDER: &str = r#"from nagini_contracts.contracts import Acc, ContractOnly, Ensures, Exsures, Requires, Result

class Resource:
    @ContractOnly
    def __enter__(self) -> 'Resource':
        Ensures(Result() is self)
        Exsures(Exception, True)
        ...

    @ContractOnly
    def write(self, value: str) -> int:
        Ensures(Result() == 7)
        Exsures(Exception, True)
        ...

    @ContractOnly
    def __exit__(self, exc_type: object, exc: object, tb: object) -> None:
        Exsures(Exception, True)
        ...

class Path:
    @ContractOnly
    def __init__(self, value: str) -> None:
        Exsures(Exception, True)
        ...

    @ContractOnly
    def __truediv__(self, child: str) -> 'Path':
        Exsures(Exception, True)
        ...

    @ContractOnly
    def open(self, mode: str, buffering: int = -1, encoding: str | None = None) -> Resource:
        Exsures(Exception, True)
        ...

class Arguments:
    @ContractOnly
    def __init__(self) -> None:
        ...

    @ContractOnly
    def text(self) -> str:
        Exsures(Exception, True)
        ...
"#;

fn check(
    source: &str,
    provider: &str,
) -> maledictus::python_heap_contracts::HeapContractVerification {
    let provider = parse_external_heap_contract_module(provider, "provider.py", "native").unwrap();
    verify_heap_module_with_imports(source, "worker.py", &["work".to_owned()], &[provider]).unwrap()
}

fn exception_only_on(provider: &str, method: &str) -> String {
    let mut result = String::new();
    let mut preserve = false;
    for line in provider.lines() {
        if line.trim_start().starts_with("def ") {
            preserve = line.contains(method);
        }
        if !line.contains("Exsures(") || preserve {
            result.push_str(line);
            result.push('\n');
        }
    }
    result
}

#[test]
fn native_constructor_chain_is_evaluated_inside_the_context_boundary() {
    let source = "from native import Path\nfrom nagini_contracts.contracts import Ensures, Result\n\ndef work() -> int:\n    Ensures(Result() == 7 or Result() == 0)\n    try:\n        with Path('events').open('a', encoding='utf-8') as stream:\n            return stream.write('text')\n    except Exception:\n        return 0\n";
    let result = check(source, PROVIDER);
    assert!(result.passed, "{result:#?}");
    let result = check(&source.replace("Result() == 7", "Result() == 8"), PROVIDER);
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains(":postcondition:") && !item.satisfied()),
        "{result:#?}"
    );
}

#[test]
fn native_method_receiver_can_be_a_permission_checked_source_field() {
    let source = "from native import Path\nfrom nagini_contracts.contracts import Acc, Requires\n\nclass Holder:\n    path: Path\n\ndef work(holder: Holder) -> Holder:\n    Requires(Acc(holder.path) and holder.path is not None)\n    try:\n        with holder.path.open('a', encoding='utf-8') as stream:\n            count = stream.write('text')\n            assert count == 7\n    except Exception:\n        return holder\n    return holder\n";
    let result = check(source, PROVIDER);
    assert!(result.passed, "{result:#?}");
    let result = check(
        &source.replace(
            "    Requires(Acc(holder.path) and holder.path is not None)\n",
            "",
        ),
        PROVIDER,
    );
    assert!(!result.passed, "{result:#?}");
    let result = check(
        &source.replace(" and holder.path is not None", ""),
        PROVIDER,
    );
    assert!(!result.passed, "{result:#?}");
}

#[test]
fn native_context_argument_exceptions_are_not_swallowed() {
    let source = "from native import Path, Arguments\n\ndef work() -> int:\n    arguments = Arguments()\n    try:\n        path = Path('events')\n        with path.open(arguments.text(), encoding=arguments.text()) as stream:\n            return stream.write('text')\n    except Exception:\n        return 0\n";
    let result = check(source, PROVIDER);
    assert!(result.passed, "{result:#?}");
    let unhandled = "from native import Path, Arguments\n\ndef work() -> int:\n    arguments = Arguments()\n    path = Path('events')\n    with path.open(arguments.text(), encoding='utf-8') as stream:\n        return stream.write('text')\n";
    let result = check(unhandled, &exception_only_on(PROVIDER, "def text("));
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains("exception-undeclared") && !item.satisfied()),
        "{result:#?}"
    );
}

#[test]
fn native_context_enter_and_exit_failures_remain_obligations() {
    let source = "from native import Path\n\ndef work() -> int:\n    path = Path('events')\n    with path.open('a', encoding='utf-8') as stream:\n        return stream.write('text')\n";
    for retained in ["def __enter__", "def __exit__"] {
        let provider = exception_only_on(PROVIDER, retained);
        let result = check(source, &provider);
        assert!(!result.passed, "{retained}: {result:#?}");
        assert!(
            result
                .obligations
                .iter()
                .any(|item| item.id.contains("exception-undeclared") && !item.satisfied()),
            "{result:#?}"
        );
    }
}

#[test]
fn native_path_division_composes_with_inline_open_without_rewriting_source() {
    for receiver in [
        "(directory / 'events.jsonl')",
        "(Path('directory') / 'events.jsonl')",
    ] {
        let source = format!(
            "from native import Path\nfrom nagini_contracts.contracts import Ensures, Result\n\ndef work() -> int:\n    Ensures(Result() == 7 or Result() == 0)\n    try:\n        directory = Path('directory')\n        with {receiver}.open('a', encoding='utf-8') as stream:\n            return stream.write('text')\n    except Exception:\n        return 0\n"
        );
        let result = check(&source, PROVIDER);
        assert!(result.passed, "{receiver}: {result:#?}");
        let result = check(&source.replace("Result() == 7", "Result() == 8"), PROVIDER);
        assert!(!result.passed, "{result:#?}");
    }
}

#[test]
fn native_division_does_not_enable_reflected_object_or_source_override_dispatch() {
    let provider = parse_external_heap_contract_module(PROVIDER, "provider.py", "native").unwrap();
    let sources = [
        (
            "frontend.python.heap.native-division-operand-unsupported",
            "from native import Path\n\nclass Other:\n    def __rtruediv__(self, left: Path) -> 'Other':\n        return self\n\ndef work(path: Path, other: Other) -> Path:\n    with (path / other).open('a') as stream:\n        count = stream.write('text')\n    return path\n",
        ),
        (
            "frontend.python.heap.native-division-dispatch-unsupported",
            "from native import Path\n\nclass Derived(Path):\n    def __truediv__(self, child: str) -> Path:\n        return self\n\ndef work(path: Path) -> Path:\n    with (path / 'events').open('a') as stream:\n        count = stream.write('text')\n    return path\n",
        ),
    ];
    for (expected, source) in sources {
        let error = maledictus::python_heap_contracts::verify_heap_module_selection_with_imports_for_conformance(
            source, "worker.py", std::slice::from_ref(&provider), &["work".to_owned()].into_iter().collect(),
        ).unwrap_err();
        assert_eq!(error.code, expected, "{error:#?}");
    }
}

#[test]
fn native_division_cannot_treat_not_implemented_as_a_completed_result() {
    let contract = "from nagini_contracts.contracts import ContractOnly\n\nclass NotImplementedType:\n    pass\n\nclass NativeDivision:\n    @ContractOnly\n    def __truediv__(self, child: str) -> NotImplementedType:\n        ...\n";
    let provider =
        parse_external_heap_contract_module(contract, "types_contract.py", "types").unwrap();
    let source = "from types import NativeDivision\n\ndef work(value: NativeDivision) -> NativeDivision:\n    with (value / 'child'):\n        return value\n";
    let error =
        verify_heap_module_with_imports(source, "worker.py", &["work".to_owned()], &[provider])
            .unwrap_err();
    assert_eq!(
        error.code, "frontend.python.heap.native-division-dispatch-unsupported",
        "{error:#?}"
    );
}

#[test]
fn native_complex_method_calls_do_not_hide_unselected_source_overrides() {
    let source = "from native import Path, Resource, Arguments\n\nclass Derived(Path):\n    def open(self, mode: str) -> Resource:\n        raise Exception()\n\ndef work(path: Path) -> Path:\n    arguments = Arguments()\n    with path.open(arguments.text()) as stream:\n        count = stream.write('text')\n    return path\n";
    let contract = PROVIDER.replace(
        "def open(self, mode: str, buffering: int = -1, encoding: str | None = None)",
        "def open(self, mode: str)",
    );
    let provider = parse_external_heap_contract_module(&contract, "provider.py", "native").unwrap();
    let error = maledictus::python_heap_contracts::verify_heap_module_selection_with_imports_for_conformance(
        source, "worker.py", &[provider], &["work".to_owned()].into_iter().collect(),
    ).unwrap_err();
    assert_eq!(
        error.code, "frontend.python.heap.native-call-dispatch-unsupported",
        "{error:#?}"
    );
}

#[test]
fn primitive_string_subclasses_with_reflected_hooks_are_not_silently_erased() {
    let source = "from native import Path\n\nclass SpecialText(str):\n    def __rtruediv__(self, path: Path) -> str:\n        return 'changed'\n\ndef work(path: Path, text: str) -> Path:\n    try:\n        with (path / text).open('a') as stream:\n            count = stream.write('text')\n    except Exception:\n        return path\n    return path\n";
    let provider = parse_external_heap_contract_module(PROVIDER, "provider.py", "native").unwrap();
    let result = maledictus::python_heap_contracts::verify_heap_module_selection_with_imports_for_conformance(
        source, "worker.py", &[provider], &["work".to_owned()].into_iter().collect(),
    ).unwrap();
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id == "module:undefined-base:SpecialText" && !item.satisfied()),
        "{result:#?}"
    );
}

#[test]
fn native_receiver_division_arguments_and_context_effects_are_ordered_exactly_once() {
    let methods = [
        ("receiver(self)", "'Machine'", true),
        ("child(self)", "str", false),
        ("__truediv__(self, child: str)", "'Machine'", true),
        ("mode(self)", "str", false),
        ("encoding(self)", "str", false),
        ("open(self, mode: str, encoding: str)", "'Machine'", true),
        ("__enter__(self)", "'Machine'", true),
        (
            "__exit__(self, exc_type: object, exc: object, tb: object)",
            "None",
            false,
        ),
    ];
    let mut provider = "from nagini_contracts.contracts import Acc, ContractOnly, Ensures, Exsures, Requires, Result\n\n".to_owned();
    for index in 1..=methods.len() {
        provider.push_str(&format!("class Step{index}(Exception):\n    pass\n\n"));
    }
    provider.push_str("class Machine:\n    state: int\n\n    @ContractOnly\n    def __init__(self) -> None:\n        Ensures(Acc(self.state) and self.state == 0)\n        ...\n");
    for (index, (signature, result, identity)) in methods.iter().enumerate() {
        let next = index + 1;
        provider.push_str(&format!("\n    @ContractOnly\n    def {signature} -> {result}:\n        Requires(Acc(self.state) and self.state == {index})\n        Ensures(Acc(self.state) and self.state == {next})\n"));
        if *identity {
            provider.push_str("        Ensures(Result() is self)\n");
        }
        provider.push_str(&format!(
            "        Exsures(Step{next}, Acc(self.state) and self.state == {next})\n        ...\n"
        ));
    }
    let exceptions = (1..=methods.len())
        .map(|index| format!("Step{index}"))
        .collect::<Vec<_>>()
        .join(", ");
    let mut source = format!(
        "from native import Machine, {exceptions}\n\ndef work() -> int:\n    machine = Machine()\n    try:\n        with (machine.receiver() / machine.child()).open(machine.mode(), encoding=machine.encoding()) as entered:\n            assert entered is machine\n            assert machine.state == 7\n"
    );
    for index in 1..=methods.len() {
        source.push_str(&format!("    except Step{index}:\n        assert machine.state == {index}\n        return {index}\n"));
    }
    source.push_str("    assert machine.state == 8\n    return 0\n");
    let result = check(&source, &provider);
    assert!(result.passed, "{result:#?}");
    let wrong_handler = source.replace(
        "except Step4:\n        assert machine.state == 4",
        "except Step4:\n        assert machine.state == 5",
    );
    let result = check(&wrong_handler, &provider);
    assert!(!result.passed, "{result:#?}");
    assert!(
        result
            .obligations
            .iter()
            .any(|item| item.id.contains(":assert:") && !item.satisfied()),
        "{result:#?}"
    );
}
