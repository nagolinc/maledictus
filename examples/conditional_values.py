from nagini_contracts.contracts import *
from typing import List


def conjunction(left: int, right: int) -> int:
    Ensures(Implies(left == 0, Result() == left))
    Ensures(Implies(left != 0, Result() == right))
    return left and right


def disjunction(left: int, right: int) -> int:
    Ensures(Implies(left != 0, Result() == left))
    Ensures(Implies(left == 0, Result() == right))
    return left or right


def choose(flag: bool) -> int:
    Ensures(Implies(flag, Result() == 4))
    Ensures(Implies(not flag, Result() == 7))
    return 4 if flag else 7


def ordered(left: int, middle: int, right: int) -> bool:
    Ensures(Implies(Result(), left < right))
    return left < middle < right


def first_or_default(values: List[int]) -> int:
    return values[0] if len(values) > 0 else -1


def short_circuit(values: List[int]) -> bool:
    return False and values[0] > 0


def finite_total() -> int:
    total = 0
    for value in range(1, 4):
        total += value
    assert 2 in range(1, 4)
    assert 5 not in range(1, 4)
    return total
