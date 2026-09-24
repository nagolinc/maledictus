from collections.abc import Callable
from typing import ParamSpec, TypeVar

_Parameters = ParamSpec("_Parameters")
_Return = TypeVar("_Return")

def operation(
    function: Callable[_Parameters, _Return],
) -> Callable[_Parameters, _Return]: ...
