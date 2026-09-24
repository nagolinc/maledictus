from nagini_contracts.contracts import *


@ContractOnly
def maybe_value(flag: bool) -> int:
    Ensures(not flag and Result() == 1)
    Exsures(ValueError, flag)
    ...
