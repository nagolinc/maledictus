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
