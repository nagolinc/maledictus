from nagini_contracts.contracts import *
from typing import List


def preserve(values: List[int]) -> List[int]:
    Ensures(Result() == values)
    Ensures(len(Result()) == len(values))
    return values


def first(values: List[int]) -> int:
    Requires(len(values) > 0)
    return values[0]


def first_or_default(values: List[int]) -> int:
    try:
        return values[0]
    except IndexError:
        return -1


def run() -> int:
    values: List[int] = [3, 8]
    assert len(values) == 2
    assert values[-1] == 8
    same = preserve(values)
    assert same == values
    return values[0]
