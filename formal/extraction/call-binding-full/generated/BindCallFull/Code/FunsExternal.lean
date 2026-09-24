-- Generated Aeneas external boundary completed with total standard-library models.
import Aeneas
import BindCallFull.Code.Types

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

open BindCallFull

@[rust_fun
  "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone
    {T : Type} (cloneCloneInst : core.clone.Clone T) :
    Option T → Result (Option T)
  | none => ok none
  | some value => do
      let cloned ← cloneCloneInst.clone value
      ok (some cloned)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::err"]
def core.result.Result.err
    {T : Type} {E : Type} : core.result.Result T E → Result (Option E)
  | .Ok _ => ok none
  | .Err error => ok (some error)

@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqString.eq
    (left right : String) : Result Bool :=
  ok (left == right)

@[rust_fun "alloc::string::{alloc::string::String}::is_empty"]
def alloc.string.String.is_empty (value : String) : Result Bool :=
  ok value.isEmpty

@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (value : String) : Result String :=
  ok value

/-- The real allocator is deliberately left as an external boundary. The unconditional helper
proofs do not depend on this declaration, and the binder refinement continues to quantify over its
explicit allocator seam rather than assuming allocation succeeds. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::try_reserve_exact"]
axiom alloc.vec.Vec.try_reserve_exact
    {T : Type} (A : Type) :
    alloc.vec.Vec T → Std.Usize →
      Result ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T)
