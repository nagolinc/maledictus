import Maledictus.Kernel

namespace Maledictus

/-!
# Closed dataclass-default heap algebra

This file models the bounded allocation and aliasing rules used for canonical dataclass defaults.
A default factory allocates a new list reference, while an explicitly supplied list reference is
stored unchanged. List mutation is indexed by allocation identity, so every alias observes the
same updated contents. Frozen metadata rejects field writes.

These are constructive algebraic facts. This file deliberately makes no claim that the Rust
frontend has been extracted into, or refined against, this model.
-/

structure DataclassListRef where
  allocation : Nat
  deriving DecidableEq

structure DataclassHeap where
  nextAllocation : Nat
  intLists : Nat → List Int

structure FreshListResult where
  reference : DataclassListRef
  heap : DataclassHeap

def updateIntList
    (lists : Nat → List Int) (allocation : Nat) (values : List Int) : Nat → List Int :=
  fun queried => if queried = allocation then values else lists queried

def allocateFreshIntList (heap : DataclassHeap) : FreshListResult :=
  { reference := { allocation := heap.nextAllocation }
    heap :=
      { nextAllocation := heap.nextAllocation + 1
        intLists := updateIntList heap.intLists heap.nextAllocation [] } }

def readIntList (heap : DataclassHeap) (reference : DataclassListRef) : List Int :=
  heap.intLists reference.allocation

def appendIntList
    (heap : DataclassHeap) (reference : DataclassListRef) (value : Int) : DataclassHeap :=
  { heap with
    intLists := updateIntList heap.intLists reference.allocation
      (readIntList heap reference ++ [value]) }

inductive DataclassFieldValue where
  | intValue (value : Int)
  | boolValue (value : Bool)
  | stringValue (value : String)
  | intListValue (reference : DataclassListRef)
  deriving DecidableEq

inductive DataclassDefault where
  | required
  | value (value : DataclassFieldValue)
  | freshIntList
  deriving DecidableEq

def bindDataclassField
    (heap : DataclassHeap)
    (default : DataclassDefault)
    (supplied : Option DataclassFieldValue) :
    Option (DataclassFieldValue × DataclassHeap) :=
  match supplied with
  | some value => some (value, heap)
  | none =>
      match default with
      | .required => none
      | .value value => some (value, heap)
      | .freshIntList =>
          let allocated := allocateFreshIntList heap
          some (.intListValue allocated.reference, allocated.heap)

def dataclassListIdentity (left right : DataclassListRef) : Bool :=
  left == right

def dataclassFieldWriteAllowed (frozen : Bool) : Bool :=
  !frozen

theorem fresh_factory_starts_empty (heap : DataclassHeap) :
    readIntList (allocateFreshIntList heap).heap
      (allocateFreshIntList heap).reference = [] := by
  simp [readIntList, allocateFreshIntList, updateIntList]

theorem consecutive_factories_have_distinct_references (heap : DataclassHeap) :
    let first := allocateFreshIntList heap
    let second := allocateFreshIntList first.heap
    Not (first.reference = second.reference) := by
  simp [allocateFreshIntList]

theorem supplied_list_alias_is_preserved
    (heap : DataclassHeap) (reference : DataclassListRef) (default : DataclassDefault) :
    bindDataclassField heap default (some (.intListValue reference)) =
      some (.intListValue reference, heap) := by
  rfl

theorem required_field_without_argument_is_rejected (heap : DataclassHeap) :
    bindDataclassField heap .required none = none := by
  rfl

theorem immutable_default_is_reused
    (heap : DataclassHeap) (value : DataclassFieldValue) :
    bindDataclassField heap (.value value) none = some (value, heap) := by
  rfl

theorem append_is_observed_through_every_equal_alias
    (heap : DataclassHeap) (left right : DataclassListRef) (value : Int)
    (same : left = right) :
    readIntList (appendIntList heap left value) right =
      readIntList heap right ++ [value] := by
  subst right
  simp [readIntList, appendIntList, updateIntList]

theorem distinct_fresh_lists_do_not_alias (heap : DataclassHeap) :
    let first := allocateFreshIntList heap
    let second := allocateFreshIntList first.heap
    dataclassListIdentity first.reference second.reference = false := by
  simp [dataclassListIdentity, allocateFreshIntList]

theorem explicit_same_reference_has_identity (reference : DataclassListRef) :
    dataclassListIdentity reference reference = true := by
  simp [dataclassListIdentity]

theorem frozen_dataclass_write_is_rejected :
    dataclassFieldWriteAllowed true = false := by
  rfl

theorem mutable_dataclass_write_is_permitted :
    dataclassFieldWriteAllowed false = true := by
  rfl

end Maledictus
