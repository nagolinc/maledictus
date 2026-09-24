from nagini_contracts.contracts import ContractOnly


class Widget:
    pass


@ContractOnly
def make() -> Widget:
    ...


@ContractOnly
def consume(value: Widget) -> None:
    ...
