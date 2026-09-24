import Aeneas
import SolverAdjacentOrder.Code.Types

open Aeneas Aeneas.Std Result ControlFlow Error

namespace SolverAdjacentOrder

def stringBytes (value : String) : List Std.U8 :=
  value.toByteArray.toList.map (fun byte =>
    ⟨byte.toNat, by
      cases byte
      simp only [UInt8.toNat_ofBitVec, UScalarTy.U8_numBits_eq, Nat.reducePow]
      omega⟩)

def ModelVec.asVec {T : Type} (values : ModelVec T) : alloc.vec.Vec T :=
  ⟨values.take Usize.max, List.length_take_le _ _⟩

def ModelVec.len {T : Type} (values : ModelVec T) : Usize :=
  alloc.vec.Vec.len values.asVec

def ModelVec.index {T I Output : Type}
    (inst : core.slice.index.SliceIndex I (Slice T) Output)
    (values : ModelVec T) (index : I) : Result Output :=
  alloc.vec.Vec.index inst values.asVec index

def ModelVec.deref {T : Type} (values : ModelVec T) : Slice T :=
  alloc.vec.Vec.deref values.asVec

def runLoopFuel {State Output : Type} :
    Nat -> (State -> Result (ControlFlow State Output)) -> State -> Result Output
  | 0, _, _ => .fail .panic
  | fuel + 1, body, state => do
      let flow <- body state
      match flow with
      | .done output => .ok output
      | .cont next => runLoopFuel fuel body next

@[rust_fun "core::slice::{[@T]}::split_first"]
def core.slice.Slice.split_first {T : Type} :
    Slice T -> Result (Option (T × Slice T)) := fun values =>
  match h : values.val with
  | [] => .ok none
  | head :: tail =>
      .ok (some (head, ⟨tail, by
        have smaller : tail.length < Usize.max := by simpa [h] using values.property
        omega⟩))

@[rust_fun "alloc::boxed::{core::cmp::PartialEq<Box<@T>, Box<@T>>}::ne"]
def Box.Insts.CoreCmpPartialEqBox.ne
    {T : Type} (_A : Type) (inst : core.cmp.PartialEq T T) :
    T -> T -> Result Bool := inst.ne

@[rust_fun "alloc::boxed::{core::convert::AsRef<Box<@T>, @T>}::as_ref"]
def Box.Insts.CoreConvertAsRef.as_ref
    {T : Type} (_A : Type) (value : T) : Result T := .ok value

@[rust_fun "alloc::string::{core::cmp::PartialEq<alloc::string::String, str>}::ne"]
def alloc.string.String.Insts.CoreCmpPartialEqStr.ne :
    String -> Str -> Result Bool := fun left right =>
  .ok (stringBytes left != right.val)

@[rust_fun "alloc::string::{core::cmp::PartialEq<alloc::string::String, str>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqStr.eq :
    String -> Str -> Result Bool := fun left right =>
  .ok (stringBytes left == right.val)

@[rust_fun "alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref"]
def alloc.string.String.Insts.CoreOpsDerefDerefStr.deref :
    String -> Result Str := fun value =>
  if bounded : (stringBytes value).length ≤ Usize.max then
    .ok ⟨stringBytes value, bounded⟩
  else
    .fail .panic

def vc.Term.Insts.CoreCmpPartialEqTerm.eq :
    vc.Term -> vc.Term -> Result _root_.Bool := fun left right => .ok (left == right)

end SolverAdjacentOrder
