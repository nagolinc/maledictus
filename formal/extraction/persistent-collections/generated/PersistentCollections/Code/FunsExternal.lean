-- Constructive external models for the source-bound persistent collection extraction.
import Aeneas
import PersistentCollections.Code.Types

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace PersistentCollections

@[rust_fun "core::option::{core::option::Option<@T>}::or"]
def core.option.Option.or {T : Type} : Option T → Option T → Result (Option T)
  | some value, _ => .ok (some value)
  | none, fallback => .ok fallback

@[rust_fun
  "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone
    {T : Type} (cloneInst : core.clone.Clone T) :
    Option T → Result (Option T)
  | none => .ok none
  | some value => do
      let cloned ← cloneInst.clone value
      .ok (some cloned)

private def sliceIterAllRemaining
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool)
    (slice : Slice T) : List T → Nat → F →
      Result (Bool × core.slice.iter.Iter T)
  | [], index, function => .ok (true, ⟨slice, index⟩)
  | value :: remaining, index, function => do
      let (accepted, nextFunction) ← fnMut.call_mut function value
      if accepted then
        sliceIterAllRemaining fnMut slice remaining (index + 1) nextFunction
      else
        .ok (false, ⟨slice, index + 1⟩)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::all"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T) :=
  fun iterator function =>
    sliceIterAllRemaining fnMut iterator.slice
      (iterator.slice.val.drop iterator.i) iterator.i function

private theorem sliceIterAllRemaining_ne_div
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool)
    (callDoesNotDiverge : ∀ function value, fnMut.call_mut function value ≠ .div)
    (slice : Slice T) (remaining : List T) (index : Nat) (function : F) :
    sliceIterAllRemaining fnMut slice remaining index function ≠ .div := by
  induction remaining generalizing index function with
  | nil => simp [sliceIterAllRemaining]
  | cons value remaining induction =>
      cases observed : fnMut.call_mut function value with
      | fail error => simp [sliceIterAllRemaining, observed]
      | div => exact (callDoesNotDiverge function value observed).elim
      | ok pair =>
          obtain ⟨accepted, nextFunction⟩ := pair
          cases accepted <;> simp [sliceIterAllRemaining, observed, induction]

theorem slice_iter_all_ne_div
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool)
    (callDoesNotDiverge : ∀ function value, fnMut.call_mut function value ≠ .div)
    (iterator : core.slice.iter.Iter T) (function : F) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
      fnMut iterator function ≠ .div := by
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
  exact sliceIterAllRemaining_ne_div fnMut callDoesNotDiverge _ _ _ _

private def sliceIterPositionRemainingBounded
    {T P : Type} (fnMut : core.ops.function.FnMut P T Bool)
    (slice : Slice T) : (remaining : List T) → Nat → (offset : Nat) → P →
      (offset + remaining.length ≤ slice.val.length) →
      Result ((Option Usize) × core.slice.iter.Iter T)
  | [], index, _, function, _ => .ok (none, ⟨slice, index⟩)
  | value :: remaining, index, offset, function, bounded => do
      let (accepted, nextFunction) ← fnMut.call_mut function value
      if accepted then
        .ok (some (Usize.ofNatCore offset (by
          have sliceBound := slice.property
          simp at bounded
          scalar_tac)), ⟨slice, index + 1⟩)
      else
        sliceIterPositionRemainingBounded fnMut slice remaining
          (index + 1) (offset + 1) nextFunction (by
            simp at bounded ⊢
            omega)

private theorem sliceIterPositionRemainingBounded_ne_div
    {T P : Type} (fnMut : core.ops.function.FnMut P T Bool)
    (callDoesNotDiverge : ∀ function value, fnMut.call_mut function value ≠ .div)
    (slice : Slice T) (remaining : List T) (index offset : Nat) (function : P)
    (bounded : offset + remaining.length ≤ slice.val.length) :
    sliceIterPositionRemainingBounded fnMut slice remaining index offset
      function bounded ≠ .div := by
  induction remaining generalizing index offset function with
  | nil => simp [sliceIterPositionRemainingBounded]
  | cons value remaining induction =>
      cases observed : fnMut.call_mut function value with
      | fail error => simp [sliceIterPositionRemainingBounded, observed]
      | div => exact (callDoesNotDiverge function value observed).elim
      | ok pair =>
          obtain ⟨accepted, nextFunction⟩ := pair
          cases accepted <;>
            simp [sliceIterPositionRemainingBounded, observed, induction]

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::position"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.position
    {T P : Type} (fnMut : core.ops.function.FnMut P T Bool) :
    core.slice.iter.Iter T → P →
      Result ((Option Usize) × core.slice.iter.Iter T) :=
  fun iterator function =>
    sliceIterPositionRemainingBounded fnMut iterator.slice
      (iterator.slice.val.drop iterator.i) iterator.i 0 function (by
        simp [List.length_drop])

theorem slice_iter_position_ne_div
    {T P : Type} (fnMut : core.ops.function.FnMut P T Bool)
    (callDoesNotDiverge : ∀ function value, fnMut.call_mut function value ≠ .div)
    (iterator : core.slice.iter.Iter T) (function : P) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.position
      fnMut iterator function ≠ .div := by
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.position
  exact sliceIterPositionRemainingBounded_ne_div
    fnMut callDoesNotDiverge _ _ _ _ _ _

@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqString.eq
    (left right : String) : Result Bool := .ok (left == right)

@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone
    (value : String) : Result String := .ok value

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::remove"]
def alloc.vec.Vec.remove {T : Type} (_allocator : Type) :
    alloc.vec.Vec T → Usize → Result (T × alloc.vec.Vec T) :=
  fun values index =>
    if inBounds : index.val < values.val.length then
      let removed := values.val[index.val]
      let remaining := values.val.eraseIdx index.val
      .ok (removed, ⟨remaining, by
        exact le_trans (List.length_eraseIdx_le values.val index.val) values.property⟩)
    else
      .fail .panic

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::append"]
def alloc.vec.Vec.append {T : Type} (_allocator : Type) :
    alloc.vec.Vec T → alloc.vec.Vec T →
      Result (alloc.vec.Vec T × alloc.vec.Vec T) :=
  fun left right =>
    if bounded : left.val.length + right.val.length ≤ Usize.max then
      .ok (⟨left.val ++ right.val, by simp [bounded]⟩, alloc.vec.Vec.new T)
    else
      .fail .panic

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
def alloc.vec.Vec.is_empty {T : Type} (_allocator : Type) :
    alloc.vec.Vec T → Result Bool :=
  fun values => .ok values.val.isEmpty

@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    {T : Type} (_allocator : Type) :
    alloc.vec.Vec T → Result (core.slice.iter.Iter T) :=
  fun values => .ok ⟨alloc.vec.Vec.deref values, 0⟩

end PersistentCollections
