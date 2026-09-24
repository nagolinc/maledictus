from nagini_contracts.contracts import Assert
from object_source_adapter import passthrough
from object_source_provider import Widget


def checked_passthrough(value: Widget) -> None:
    returned = passthrough(value)
    Assert(returned is not None)
