import Maledictus.VC

namespace Maledictus

/-!
# Static Python slice normalization

This is the mathematical frontend-premise model for the closed-list and fixed-tuple slice
algorithm.  Bounds and steps are already parsed integer literals; the receiver length is known.
It intentionally does not claim that the current Rust AST recognizer or implementation refines
this model.  That requires a separate extraction/correspondence proof.
-/

inductive StaticSliceStep where
  | omitted
  | literal (value : Int)
  deriving DecidableEq, Repr

inductive StaticSlicePlan where
  | positive (start stop step : Nat)
  | negative (start stop : Int) (magnitude : Nat)
  deriving DecidableEq, Repr

def clampInt (lower upper value : Int) : Int :=
  max lower (min value upper)

def adjustNegativeBound (value length : Int) : Int :=
  if value < 0 then value + length else value

def normalizePositiveBound (value : Option Int) (fallback length : Nat) : Nat :=
  let raw := value.getD (Int.ofNat fallback)
  (clampInt 0 (Int.ofNat length) (adjustNegativeBound raw (Int.ofNat length))).toNat

def normalizeNegativeBound (value : Int) (length : Nat) : Int :=
  clampInt (-1) (Int.ofNat length - 1)
    (adjustNegativeBound value (Int.ofNat length))

def defaultNegativeStart (length : Nat) : Int :=
  Int.ofNat length - 1

def normalizeStaticSlice
    (lower upper : Option Int) (step : StaticSliceStep) (length : Nat) :
    Option StaticSlicePlan :=
  let rawStep := match step with
    | .omitted => 1
    | .literal value => value
  if rawStep = 0 then none
  else if 0 < rawStep then
    some (.positive
      (normalizePositiveBound lower 0 length)
      (normalizePositiveBound upper length length)
      rawStep.toNat)
  else
    some (.negative
      (lower.map (normalizeNegativeBound · length) |>.getD (defaultNegativeStart length))
      (upper.map (normalizeNegativeBound · length) |>.getD (-1))
      (-rawStep).toNat)

def indicesForPlan (length : Nat) : StaticSlicePlan -> List Nat
  | .positive start stop step =>
      (List.range length).filter fun index =>
        decide (start ≤ index ∧ index < stop ∧ (index - start) % step = 0)
  | .negative start stop magnitude =>
      (List.range length).reverse.filter fun index =>
        decide (stop < Int.ofNat index ∧ Int.ofNat index ≤ start ∧
          (start - Int.ofNat index).toNat % magnitude = 0)

def staticSliceIndices
    (lower upper : Option Int) (step : StaticSliceStep) (length : Nat) :
    Option (List Nat) :=
  (normalizeStaticSlice lower upper step length).map (indicesForPlan length)

theorem clamp_int_stays_between
    (lower upper value : Int) (ordered : lower ≤ upper) :
    lower ≤ clampInt lower upper value ∧ clampInt lower upper value ≤ upper := by
  simp only [clampInt]
  omega

theorem positive_slice_bounds_are_clipped
    (value : Int) (length : Nat) :
    0 ≤ clampInt 0 (Int.ofNat length) (adjustNegativeBound value (Int.ofNat length)) ∧
      clampInt 0 (Int.ofNat length) (adjustNegativeBound value (Int.ofNat length)) ≤
        Int.ofNat length := by
  exact clamp_int_stays_between 0 (Int.ofNat length)
    (adjustNegativeBound value (Int.ofNat length)) (by simp)

theorem negative_slice_bounds_are_clipped
    (value : Int) (length : Nat) :
    -1 ≤ normalizeNegativeBound value length ∧
      normalizeNegativeBound value length ≤ Int.ofNat length - 1 := by
  unfold normalizeNegativeBound
  have lengthNonnegative : 0 ≤ Int.ofNat length := Int.ofNat_zero_le length
  exact clamp_int_stays_between (-1) (Int.ofNat length - 1)
    (adjustNegativeBound value (Int.ofNat length)) (by omega)

theorem zero_step_refuses (lower upper : Option Int) (length : Nat) :
    normalizeStaticSlice lower upper (.literal 0) length = none := by
  simp [normalizeStaticSlice]

theorem positive_step_builds_positive_plan
    (lower upper : Option Int) (step : Int) (length : Nat)
    (positive : 0 < step) :
    normalizeStaticSlice lower upper (.literal step) length =
      some (.positive
        (normalizePositiveBound lower 0 length)
        (normalizePositiveBound upper length length)
        step.toNat) := by
  have nonzero : step ≠ 0 := by omega
  simp [normalizeStaticSlice, positive, nonzero]

theorem negative_step_builds_negative_plan
    (lower upper : Option Int) (step : Int) (length : Nat)
    (negative : step < 0) :
    normalizeStaticSlice lower upper (.literal step) length =
      some (.negative
        (lower.map (normalizeNegativeBound · length) |>.getD (defaultNegativeStart length))
        (upper.map (normalizeNegativeBound · length) |>.getD (-1))
        (-step).toNat) := by
  have nonzero : step ≠ 0 := by omega
  have notPositive : ¬ 0 < step := by omega
  simp [normalizeStaticSlice, nonzero, notPositive]

theorem every_static_slice_index_is_in_bounds
    (lower upper : Option Int) (step : StaticSliceStep) (length index : Nat)
    (member : ∃ indices,
      staticSliceIndices lower upper step length = some indices ∧ index ∈ indices) :
    index < length := by
  obtain ⟨indices, normalized, member⟩ := member
  cases normalizedPlan : normalizeStaticSlice lower upper step length with
  | none => simp [staticSliceIndices, normalizedPlan] at normalized
  | some plan =>
      simp [staticSliceIndices, normalizedPlan] at normalized
      subst indices
      cases plan with
      | positive start stop stride =>
          simp only [indicesForPlan, List.mem_filter] at member
          exact List.mem_range.mp member.1
      | negative start stop magnitude =>
          simp only [indicesForPlan, List.mem_filter, List.mem_reverse] at member
          exact List.mem_range.mp member.1

theorem omitted_negative_stop_differs_from_explicit_negative_one :
    staticSliceIndices none none (.literal (-1)) 5 = some [4, 3, 2, 1, 0] ∧
      staticSliceIndices none (some (-1)) (.literal (-1)) 5 = some [] := by
  native_decide

theorem extreme_bounds_clip_before_negative_stride :
    staticSliceIndices (some 100) (some (-100)) (.literal (-3)) 5 = some [4, 1] := by
  native_decide

theorem large_magnitude_steps_select_at_most_the_first_reachable_index :
    staticSliceIndices none none (.literal 100) 5 = some [0] ∧
      staticSliceIndices none none (.literal (-100)) 5 = some [4] := by
  native_decide

theorem empty_receiver_produces_empty_indices_for_nonzero_steps :
    staticSliceIndices none none (.literal 1) 0 = some [] ∧
      staticSliceIndices none none (.literal (-1)) 0 = some [] := by
  native_decide

end Maledictus
