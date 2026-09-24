from nagini_contracts.contracts import Acc, Ensures, Requires, Result


class Cell:
    value: int

    def __init__(self, initial: int) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == initial)
        self.value = initial

    def get(self) -> int:
        Requires(Acc(self.value))
        Ensures(Acc(self.value))
        Ensures(Result() == self.value)
        return self.value
