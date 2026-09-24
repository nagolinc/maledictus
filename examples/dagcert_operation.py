from dataclasses import dataclass

from dagcert.runtime import operation


@dataclass(frozen=True, slots=True)
class WorkInput:
    value: int


@dataclass(frozen=True, slots=True)
class WorkCompleted:
    value: int


@operation
def work(request: WorkInput) -> WorkCompleted:
    return WorkCompleted(request.value + 1)
