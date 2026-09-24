from object_source_provider import Widget, identity


def passthrough(value: Widget) -> Widget:
    return identity(value)
