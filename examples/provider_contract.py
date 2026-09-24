from nagini_contracts.contracts import *


@ContractOnly
def successor(value: int) -> int:
    Requires(value > 0)
    Ensures(Result() == value + 1)
    ...
