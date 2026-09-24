import Aeneas
import KernelExitEffects.Code.Types

open Aeneas Aeneas.Std Result ControlFlow Error

namespace KernelExitEffects

def iteratorAny
    {T F : Type}
    (fnMut : core.ops.function.FnMut F T Bool)
    (iter : core.slice.iter.Iter T)
    (predicate : F) : Result (Bool × core.slice.iter.Iter T) :=
  if within : iter.i < iter.slice.len then
    let withinValues : iter.i < iter.slice.val.length := by simpa using within
    do
      let item := iter.slice.val[iter.i]'withinValues
      let (matched, nextPredicate) <- fnMut.call_mut predicate item
      let nextIter := { iter with i := iter.i + 1 }
      if matched then .ok (true, nextIter)
      else iteratorAny fnMut nextIter nextPredicate
  else
    .ok (false, iter)
termination_by iter.slice.val.length - iter.i
decreasing_by omega

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
    {T F : Type}
    (fnMut : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T -> F -> Result (Bool × core.slice.iter.Iter T) :=
  iteratorAny fnMut

@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqString.eq
    (left right : String) : Result Bool :=
  .ok (left == right)

@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (value : String) : Result String :=
  .ok value

end KernelExitEffects
