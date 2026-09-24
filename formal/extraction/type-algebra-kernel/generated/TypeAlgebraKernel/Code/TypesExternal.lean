import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-- Concrete representation for the standard-library uninitialized storage marker.  None of the
    selected source functions observes an uninitialized value; vector models expose only initialized
    elements. -/
@[rust_type "core::mem::maybe_uninit::MaybeUninit"]
def core.mem.maybe_uninit.MaybeUninit (T : Type) : Type := T
