from nagini_contracts.contracts import *
from predicate_source_provider import Cell, state


LIMIT = 100


def verify_state() -> None:
    cell = Cell()
    Fold(state(cell))
    Unfold(state(cell))
    Assert(cell.value == 1)
