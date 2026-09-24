-- Constructive external type model for the production Term::sort extraction.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/- Extraction-local constructive model for vectors. Using `List` makes the
    recursive `Sort` and `Term` occurrences strictly positive in Lean. The
    generated artifact's refinement theorem relates this model to Rust's
    length-bounded `Vec`. -/
namespace VcTermSort
def ModelVec (T : Type) : Type := List T
end VcTermSort

/-- Constructive model of Rust's private niche marker. It carries no runtime
    data and is used only as the phantom second argument of `NonZero`. -/
@[rust_type "core::num::niche_types::NonZeroI128Inner"]
def core.num.niche_types.NonZeroI128Inner : Type := Unit

/-- The source-owned sort kernel stores but never observes a `NonZeroI128`.
    Modeling its runtime integer payload directly is exact for that closure;
    including zero here strengthens the all-input theorem rather than assuming
    Rust's constructor invariant. -/
@[rust_type "core::num::nonzero::NonZero"]
def core.num.nonzero.NonZero (T : Type) (_NonZeroInner : Type) : Type := T

/-- The extracted code observes only set insertion and its fresh/not-fresh bit.
    A duplicate-free list is therefore a complete constructive representation. -/
@[rust_type "alloc::collections::btree::set::BTreeSet"]
def alloc.collections.btree.set.BTreeSet (T : Type) (_A : Type) : Type := List T
