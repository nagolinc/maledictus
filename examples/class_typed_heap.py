from nagini_contracts.contracts import Acc, Assert, Ensures, Requires, Result


class Cell:
    value: int

    def get(self) -> int:
        Requires(Acc(self.value))
        Ensures(Acc(self.value))
        Ensures(Result() == self.value)
        return self.value


def inspect(cell: Cell, expected: int) -> None:
    Requires(Acc(cell.value))
    Requires(cell.value == expected)
    observed = cell.get()
    copied: int = cell.value
    Assert(cell.value == observed)
    Assert(cell.value == copied)
    Ensures(Acc(cell.value))
    Ensures(cell.value == expected)
