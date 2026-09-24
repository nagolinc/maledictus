import Aeneas
import TypeAlgebraKernel.Code.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

open TypeAlgebraKernel

@[rust_fun
  "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone
    {T : Type} (cloneCloneInst : core.clone.Clone T) :
    Option T → Result (Option T)
  | none => .ok none
  | some value => do
      let cloned ← cloneCloneInst.clone value
      .ok (some cloned)

@[rust_fun "core::option::{core::option::Option<@T>}::as_deref"]
def core.option.Option.as_deref
    {T Clause0_Target : Type}
    (derefInst : core.ops.deref.Deref T Clause0_Target) :
    Option T → Result (Option Clause0_Target)
  | none => .ok none
  | some value => do
      let target ← derefInst.deref value
      .ok (some target)

@[rust_fun "core::str::traits::{core::cmp::PartialEq<str, str>}::eq"]
def Str.Insts.CoreCmpPartialEqStr.eq (left right : Str) : Result Bool :=
  .ok (left == right)

@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqString.eq
    (left right : String) : Result Bool :=
  .ok (left == right)

@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (value : String) : Result String :=
  .ok value

@[rust_fun
  "alloc::string::{core::convert::From<alloc::string::String, &'0 str>}::from"]
def alloc.string.String.Insts.CoreConvertFromShared0Str.from
    (value : Str) : Result String :=
  let bytes := ByteArray.mk <|
    (value.val.map (fun byte => UInt8.ofBitVec byte.bv)).toArray
  match String.fromUTF8? bytes with
  | some string => .ok string
  | none => .fail .panic

@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, &'0 str>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqShared0Str.eq
    (left : String) (right : Str) : Result Bool :=
  if bounded : left.toByteArray.size ≤ U32.max then
    .ok (toStr left bounded == right)
  else
    .fail .panic

@[rust_fun
  "alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref"]
def alloc.string.String.Insts.CoreOpsDerefDerefStr.deref
    (value : String) : Result Str :=
  if bounded : value.toByteArray.size ≤ U32.max then
    .ok (toStr value bounded)
  else
    .fail .panic

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

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::pop"]
def alloc.vec.Vec.pop {T : Type} (_allocator : Type) :
    alloc.vec.Vec T → Result (Option T × alloc.vec.Vec T) :=
  fun values =>
    match values.val.getLast? with
    | none => .ok (none, values)
    | some value =>
      let remaining := values.val.dropLast
      .ok (some value, ⟨remaining, by
        have shortened : remaining.length ≤ values.val.length := by
          simp [remaining]
        exact shortened.trans values.property⟩)

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
def alloc.vec.Vec.is_empty {T : Type} (_allocator : Type) :
    alloc.vec.Vec T → Result Bool :=
  fun values => .ok values.val.isEmpty
