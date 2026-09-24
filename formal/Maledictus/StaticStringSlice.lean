import Maledictus.StaticSliceNormalization

namespace Maledictus

/-!
# Executable static Python string slicing

This file models a Python string as a sequence of Unicode code points, not UTF-8 or UTF-16 code
units.  It reuses the executable Python index normalization in `StaticSliceNormalization` and then
materializes exactly those in-bounds positions.  Repeated slices evaluate left to right against the
result of the preceding slice.

The theorems below prove properties of this Lean model.  They do not prove that the Rust frontend
recognizes or lowers Python syntax to this model; that remains a separate correspondence obligation.
-/

structure PythonCodePoint where
  value : Nat
  isCodePoint : value <= 0x10ffff
  deriving DecidableEq, Repr

abbrev StaticPythonString := List PythonCodePoint

structure StaticStringSlice where
  lower : Option Int
  upper : Option Int
  step : StaticSliceStep
  deriving DecidableEq, Repr

def selectStaticStringIndices
    (source : StaticPythonString) (indices : List Nat)
    (bounded : forall index, index ∈ indices -> index < source.length) :
    StaticPythonString :=
  indices.attach.map fun entry =>
    source.get ⟨entry.1, bounded entry.1 entry.2⟩

def evaluateStaticStringSlice
    (source : StaticPythonString) (slice : StaticStringSlice) :
    Option StaticPythonString :=
  match indicesEq : staticSliceIndices slice.lower slice.upper slice.step source.length with
  | none => none
  | some indices =>
      some (selectStaticStringIndices source indices fun index member =>
        every_static_slice_index_is_in_bounds
          slice.lower slice.upper slice.step source.length index
          ⟨indices, indicesEq, member⟩)

def evaluateStaticStringSlices :
    StaticPythonString -> List StaticStringSlice -> Option StaticPythonString
  | source, [] => some source
  | source, slice :: remaining =>
      (evaluateStaticStringSlice source slice).bind fun sliced =>
        evaluateStaticStringSlices sliced remaining

theorem selected_static_string_length
    (source : StaticPythonString) (indices : List Nat)
    (bounded : forall index, index ∈ indices -> index < source.length) :
    (selectStaticStringIndices source indices bounded).length = indices.length := by
  simp [selectStaticStringIndices]

theorem selected_static_string_code_point_came_from_source
    (source : StaticPythonString) (indices : List Nat)
    (bounded : forall index, index ∈ indices -> index < source.length)
    (point : PythonCodePoint)
    (member : point ∈ selectStaticStringIndices source indices bounded) :
    point ∈ source := by
  simp only [selectStaticStringIndices, List.mem_map] at member
  obtain ⟨entry, _, pointEq⟩ := member
  rw [← pointEq]
  exact List.get_mem source ⟨entry.1, bounded entry.1 entry.2⟩

theorem indices_for_static_slice_plan_do_not_grow
    (length : Nat) (plan : StaticSlicePlan) :
    (indicesForPlan length plan).length <= length := by
  cases plan with
  | positive start stop step =>
      exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  | negative start stop magnitude =>
      exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem static_slice_indices_do_not_grow
    (lower upper : Option Int) (step : StaticSliceStep) (length : Nat)
    (indices : List Nat)
    (indicesEq : staticSliceIndices lower upper step length = some indices) :
    indices.length <= length := by
  cases planEq : normalizeStaticSlice lower upper step length with
  | none =>
      simp [staticSliceIndices, planEq] at indicesEq
  | some plan =>
      simp [staticSliceIndices, planEq] at indicesEq
      subst indices
      exact indices_for_static_slice_plan_do_not_grow length plan

theorem evaluated_static_string_length_does_not_grow
    (source output : StaticPythonString) (slice : StaticStringSlice)
    (evaluated : evaluateStaticStringSlice source slice = some output) :
    output.length <= source.length := by
  unfold evaluateStaticStringSlice at evaluated
  split at evaluated
  · contradiction
  · rename_i indices indicesEq
    injection evaluated with outputEq
    rw [← outputEq, selected_static_string_length]
    exact static_slice_indices_do_not_grow
      slice.lower slice.upper slice.step source.length indices indicesEq

theorem evaluated_static_string_code_point_came_from_source
    (source output : StaticPythonString) (slice : StaticStringSlice)
    (evaluated : evaluateStaticStringSlice source slice = some output)
    (point : PythonCodePoint) (member : point ∈ output) :
    point ∈ source := by
  unfold evaluateStaticStringSlice at evaluated
  split at evaluated
  · contradiction
  · rename_i indices indicesEq
    injection evaluated with outputEq
    rw [← outputEq] at member
    exact selected_static_string_code_point_came_from_source source indices _ point member

theorem zero_step_static_string_slice_refuses
    (source : StaticPythonString) (lower upper : Option Int) :
    evaluateStaticStringSlice source ⟨lower, upper, .literal 0⟩ = none := by
  simp [evaluateStaticStringSlice, staticSliceIndices, normalizeStaticSlice]

@[simp] theorem repeated_static_string_slices_empty
    (source : StaticPythonString) :
    evaluateStaticStringSlices source [] = some source := rfl

@[simp] theorem repeated_static_string_slices_cons
    (source : StaticPythonString) (slice : StaticStringSlice)
    (remaining : List StaticStringSlice) :
    evaluateStaticStringSlices source (slice :: remaining) =
      (evaluateStaticStringSlice source slice).bind fun sliced =>
        evaluateStaticStringSlices sliced remaining := rfl

theorem repeated_static_string_slices_do_not_grow
    (slices : List StaticStringSlice) (source output : StaticPythonString)
    (evaluated : evaluateStaticStringSlices source slices = some output) :
    output.length <= source.length := by
  induction slices generalizing source output with
  | nil =>
      simp at evaluated
      subst output
      exact Nat.le_refl source.length
  | cons slice remaining inductionHypothesis =>
      simp only [repeated_static_string_slices_cons] at evaluated
      cases firstEq : evaluateStaticStringSlice source slice with
      | none => simp [firstEq] at evaluated
      | some intermediate =>
          simp [firstEq] at evaluated
          exact Nat.le_trans
            (inductionHypothesis intermediate output evaluated)
            (evaluated_static_string_length_does_not_grow source intermediate slice firstEq)

theorem repeated_static_string_code_point_came_from_source
    (slices : List StaticStringSlice) (source output : StaticPythonString)
    (evaluated : evaluateStaticStringSlices source slices = some output)
    (point : PythonCodePoint) (member : point ∈ output) :
    point ∈ source := by
  induction slices generalizing source output with
  | nil =>
      simp at evaluated
      subst output
      exact member
  | cons slice remaining inductionHypothesis =>
      simp only [repeated_static_string_slices_cons] at evaluated
      cases firstEq : evaluateStaticStringSlice source slice with
      | none => simp [firstEq] at evaluated
      | some intermediate =>
          simp [firstEq] at evaluated
          have intermediateMember :=
            inductionHypothesis intermediate output evaluated member
          exact evaluated_static_string_code_point_came_from_source
            source intermediate slice firstEq point intermediateMember

private def codePoint (value : Nat) (valid : value <= 0x10ffff := by omega) :
    PythonCodePoint :=
  ⟨value, valid⟩

theorem executable_string_slice_covers_omitted_negative_and_clipped_bounds :
    let source := [codePoint 0x41, codePoint 0x3bb, codePoint 0x1f600,
      codePoint 0x42, codePoint 0x1f642]
    evaluateStaticStringSlice source ⟨some (-100), some 100, .omitted⟩ = some source ∧
      evaluateStaticStringSlice source ⟨none, none, .literal (-1)⟩ =
        some source.reverse := by
  native_decide

theorem executable_string_slice_supports_both_nonzero_step_directions :
    let source := [codePoint 0x41, codePoint 0x3bb, codePoint 0x1f600,
      codePoint 0x42, codePoint 0x1f642]
    evaluateStaticStringSlice source ⟨some 0, none, .literal 2⟩ =
        some [codePoint 0x41, codePoint 0x1f600, codePoint 0x1f642] ∧
      evaluateStaticStringSlice source ⟨none, none, .literal (-2)⟩ =
        some [codePoint 0x1f642, codePoint 0x1f600, codePoint 0x41] := by
  native_decide

theorem executable_nested_string_slices_are_repeated_evaluation :
    let source := [codePoint 0x41, codePoint 0x3bb, codePoint 0x1f600,
      codePoint 0x42, codePoint 0x1f642]
    let first : StaticStringSlice := ⟨some 1, none, .literal 2⟩
    let second : StaticStringSlice := ⟨none, none, .literal (-1)⟩
    evaluateStaticStringSlices source [first, second] =
      some [codePoint 0x42, codePoint 0x3bb] := by
  native_decide

end Maledictus
