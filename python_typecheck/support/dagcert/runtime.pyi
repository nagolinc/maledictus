from contextlib import AbstractContextManager
from dataclasses import dataclass
from typing import Callable, Generic, ParamSpec, TypeAlias, TypeVar

P = ParamSpec("P")
R = TypeVar("R")

class OperationTypeViolation(TypeError): ...
class ExternalMonitorError(RuntimeError): ...

@dataclass(frozen=True, slots=True)
class UnhandledException:
    exception_type: str
    message: str

@dataclass(frozen=True, slots=True)
class ExternalSuccess(Generic[R]):
    value: R

@dataclass(frozen=True, slots=True)
class ExternalRaised:
    boundary_id: str
    exception_type: str
    message: str

@dataclass(frozen=True, slots=True)
class ExternalTypeViolation:
    boundary_id: str
    expected_type: str
    observed_type: str
    message: str

@dataclass(frozen=True, slots=True)
class ExternalBoundaryEvent:
    boundary_id: str
    elapsed_ms: float
    outcome_type: str
    succeeded: bool
    recorded_at: float
    expected_type: str
    observed_type: str | None = ...
    exception_type: str | None = ...
    message: str | None = ...

ExternalResult: TypeAlias = ExternalSuccess[R] | ExternalRaised | ExternalTypeViolation

def operation(function: Callable[P, R]) -> Callable[P, R]: ...
def external_boundary(
    boundary_id: str,
) -> Callable[[Callable[P, R]], Callable[P, ExternalResult[R]]]: ...
def monitor_external_boundaries(
    observer: Callable[[ExternalBoundaryEvent], None],
) -> AbstractContextManager[None]: ...
def runtime_violations() -> tuple[ExternalBoundaryEvent, ...]: ...
def clear_runtime_violations() -> None: ...
def outcome_type(value: object) -> str: ...
