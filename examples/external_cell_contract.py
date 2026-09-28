from nagini_contracts.contracts import Acc, ContractOnly, Ensures, Requires, Result


class Cell:
    value: int

    @ContractOnly
    def __init__(self, initial: int) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == initial)
        ...

    @ContractOnly
    def get(self) -> int:
        Requires(Acc(self.value))
        Ensures(Acc(self.value))
        Ensures(Result() == self.value)
        ...

    @ContractOnly
    def __enter__(self) -> "Cell":
        Requires(Acc(self.value))
        Ensures(Acc(self.value))
        Ensures(Result() is self)
        ...

    @ContractOnly
    def __exit__(
        self,
        exception_type: object,
        exception: object,
        traceback: object,
    ) -> bool:
        Requires(Acc(self.value))
        Ensures(Acc(self.value))
        ...


@ContractOnly
def open_cell(initial: int) -> Cell:
    Ensures(Acc(Result().value))
    Ensures(Result().value == initial)
    ...
