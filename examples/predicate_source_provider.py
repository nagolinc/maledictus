from nagini_contracts.contracts import *


LIMIT = 1


class Cell:
    value: int

    def __init__(self) -> None:
        Ensures(Acc(self.value))
        Ensures(self.value == LIMIT)
        self.value = LIMIT


@Predicate
def state(cell: Cell) -> bool:
    return Acc(cell.value) and cell.value == LIMIT
