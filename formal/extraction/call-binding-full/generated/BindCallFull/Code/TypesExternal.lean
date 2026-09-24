-- Generated Aeneas external type boundary for fallible system allocation.
import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

namespace alloc.collections

/-- Opaque standard-library allocation failure carried only on the rejected branch. -/
axiom TryReserveError : Type

end alloc.collections
