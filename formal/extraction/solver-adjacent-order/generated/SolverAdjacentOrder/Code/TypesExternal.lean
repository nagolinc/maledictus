import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

namespace SolverAdjacentOrder

abbrev ModelVec (T : Type) : Type := List T

end SolverAdjacentOrder

@[rust_type "core::num::niche_types::NonZeroI128Inner"]
def core.num.niche_types.NonZeroI128Inner : Type := Unit

@[rust_type "core::num::nonzero::NonZero"]
abbrev core.num.nonzero.NonZero (T : Type) (_Clause0_NonZeroInner : Type) : Type := T
