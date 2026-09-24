from nagini_contracts.contracts import *


def increment(value: int) -> int:
    Requires(value > 0)
    Ensures(Result() == value + 1)
    return value + 1
