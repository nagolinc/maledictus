from nagini_contracts.contracts import *


def successor(value: int) -> int:
    Requires(value > 0)
    Ensures(Result() > value)
    next_value = value + 1
    assert next_value > 0
    return next_value

