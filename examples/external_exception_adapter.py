from nagini_contracts.contracts import *
from typed_provider import maybe_value


def recovered_value(flag: bool) -> int:
    Ensures(Implies(flag, Result() == 2))
    Ensures(Implies(not flag, Result() == 1))
    try:
        return maybe_value(flag)
    except ValueError:
        return 2
