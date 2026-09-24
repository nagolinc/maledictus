from nagini_contracts.contracts import *
from source_leaf import increment


def run(value: int) -> int:
    Requires(value > 0)
    Ensures(Result() == value + 1)
    return increment(value)
