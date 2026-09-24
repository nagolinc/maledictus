from provider import successor
from nagini_contracts.contracts import *


def adapted_successor(value: int) -> int:
    Requires(value > 0)
    Ensures(Result() == value + 1)
    return successor(value)
