from nagini_contracts.contracts import Assert
from object_provider import Widget, consume, make


def checked_widget() -> None:
    widget = make()
    Assert(widget is not None)
    consume(widget)
