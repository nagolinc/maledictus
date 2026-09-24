import Maledictus.VC

namespace Maledictus

/-!
# Total builtin `sorted` summary

The executable scalar frontend accepts the canonical one-argument Python builtin only for a
homogeneous list whose elements have builtin total ordering.  Its modular result is fresh: the
only fact currently exported is preservation of length.  That is deliberately an over-
approximation; it cannot manufacture element equality, identity, or ordering facts.

This file proves the corresponding finite model and refusal algebra.  It does not prove Python
AST recognition, Python's concrete ordering implementation, Z3 sequence lowering, or Rust/Lean
implementation correspondence.
-/

def builtinSortableElement : ValueSort → Bool
  | .bool | .int | .string | .bytes => true
  | _ => false

structure SortedCallShape where
  canonicalBuiltin : Bool
  argumentCount : Nat
  keywordCount : Nat
  repeatedRegion : Bool
  elementSort : ValueSort

def authorizeSortedCall (shape : SortedCallShape) : Option ValueSort :=
  if !shape.canonicalBuiltin then none
  else if shape.argumentCount != 1 then none
  else if shape.keywordCount != 0 then none
  else if shape.repeatedRegion then none
  else if !builtinSortableElement shape.elementSort then none
  else some shape.elementSort

theorem canonical_primitive_sorted_call_authorizes
    (shape : SortedCallShape)
    (canonical : shape.canonicalBuiltin = true)
    (oneArgument : shape.argumentCount = 1)
    (noKeywords : shape.keywordCount = 0)
    (notRepeated : shape.repeatedRegion = false)
    (sortable : builtinSortableElement shape.elementSort = true) :
    authorizeSortedCall shape = some shape.elementSort := by
  simp [authorizeSortedCall, canonical, oneArgument, noKeywords, notRepeated, sortable]

theorem shadowed_sorted_refuses
    (shape : SortedCallShape) (shadowed : shape.canonicalBuiltin = false) :
    authorizeSortedCall shape = none := by
  simp [authorizeSortedCall, shadowed]

theorem repeated_sorted_refuses
    (shape : SortedCallShape) (repeated : shape.repeatedRegion = true) :
    authorizeSortedCall shape = none := by
  by_cases canonical : shape.canonicalBuiltin
  · by_cases oneArgument : shape.argumentCount = 1
    · by_cases noKeywords : shape.keywordCount = 0
      · simp [authorizeSortedCall, canonical, oneArgument, noKeywords, repeated]
      · simp [authorizeSortedCall, canonical, oneArgument, noKeywords]
    · simp [authorizeSortedCall, canonical, oneArgument]
  · simp [authorizeSortedCall, canonical]

theorem unsortable_element_refuses
    (shape : SortedCallShape) (unsortable : builtinSortableElement shape.elementSort = false) :
    authorizeSortedCall shape = none := by
  by_cases canonical : shape.canonicalBuiltin
  · by_cases oneArgument : shape.argumentCount = 1
    · by_cases noKeywords : shape.keywordCount = 0
      · by_cases repeated : shape.repeatedRegion
        · simp [authorizeSortedCall, canonical, oneArgument, noKeywords, repeated]
        · simp [authorizeSortedCall, canonical, oneArgument, noKeywords, repeated, unsortable]
      · simp [authorizeSortedCall, canonical, oneArgument, noKeywords]
    · simp [authorizeSortedCall, canonical, oneArgument]
  · simp [authorizeSortedCall, canonical]

def orderedInsert (before : α → α → Bool) (value : α) : List α → List α
  | [] => [value]
  | head :: tail =>
      if before value head then value :: head :: tail
      else head :: orderedInsert before value tail

theorem ordered_insert_length
    (before : α → α → Bool) (value : α) (values : List α) :
    (orderedInsert before value values).length = values.length + 1 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      by_cases earlier : before value head
      · simp [orderedInsert, earlier]
      · simp [orderedInsert, earlier, inductionHypothesis, Nat.add_assoc]

def modeledSorted (before : α → α → Bool) : List α → List α
  | [] => []
  | head :: tail => orderedInsert before head (modeledSorted before tail)

theorem modeled_sorted_preserves_length (before : α → α → Bool) (values : List α) :
    (modeledSorted before values).length = values.length := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [modeledSorted, ordered_insert_length, inductionHypothesis]

def sameLengthSortedAbstraction (source result : List α) : Prop :=
  result.length = source.length

theorem modeled_sorted_satisfies_same_length_abstraction
    (before : α → α → Bool) (source : List α) :
    sameLengthSortedAbstraction source (modeledSorted before source) := by
  exact modeled_sorted_preserves_length before source

theorem same_length_abstraction_does_not_require_identity
    (source result : List α) (sameLength : result.length = source.length) :
    sameLengthSortedAbstraction source result := by
  exact sameLength

end Maledictus
