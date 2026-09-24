import Maledictus.VC

namespace Maledictus

/-!
# Sound constant folding for a closed list index (v52)

The frontend may replace `values[index]` by an element only when `values` is an
already-validated finite `Term.list` and `index` is an `intLiteral`.  Elements need
not themselves be literals: a closed list has a known spine even when an element is
symbolic.  Dynamic receivers, dynamic indices, malformed lists, lengths outside the
signed-64 frontend, and out-of-range Python indices all produce `none`, leaving the
partial `listGet` for the caller to reject through the existing path obligations.

The negative-index calculation is performed in mathematical `Int`, so the minimum
signed-64 literal is never negated.  For every supported list length it is simply an
out-of-range Python index.
-/

/-- The sign bit determines the magnitude of the minimum signed 64-bit integer. -/
def executableI64Magnitude : Nat := 2 ^ 63

/-- Largest list length whose length is representable by the signed-64 frontend. -/
def executableI64MaximumListLength : Nat := executableI64Magnitude - 1

/-- Mathematical value of `i64::MIN`; normalization never machine-negates it. -/
def executableI64Minimum : Int := -Int.ofNat executableI64Magnitude

/-- Python's normalization step, represented in unbounded mathematical integers. -/
def pythonNormalizeListIndex (rawIndex : Int) (length : Nat) : Int :=
  if rawIndex < 0 then Int.ofNat length + rawIndex else rawIndex

/--
Return a machine-independent natural position exactly when Python's normalized
index lies in `[0, length)`.  The construction performs no unchecked conversion.
-/
def normalizedClosedListPosition (rawIndex : Int) (length : Nat) : Option Nat :=
  let normalized := pythonNormalizeListIndex rawIndex length
  if normalized < 0 then none
  else
    let position := normalized.toNat
    if position < length then some position else none

/-- Constant-fold a supported closed list and literal integer index. -/
def constantFoldClosedListIndex (receiver index : Term) : Option Term :=
  match receiver, index with
  | .list elementSort values, .intLiteral rawIndex =>
      if isListElementSort elementSort && allOfSort values elementSort then
        if values.length ≤ executableI64MaximumListLength then
          match normalizedClosedListPosition rawIndex values.length with
          | some position => values[position]?
          | none => none
        else none
      else none
  | _, _ => none

theorem python_normalize_nonnegative
    (rawIndex : Int) (length : Nat) (nonnegative : 0 ≤ rawIndex) :
    pythonNormalizeListIndex rawIndex length = rawIndex := by
  simp [pythonNormalizeListIndex, Int.not_lt.mpr nonnegative]

theorem python_normalize_negative
    (rawIndex : Int) (length : Nat) (negative : rawIndex < 0) :
    pythonNormalizeListIndex rawIndex length = Int.ofNat length + rawIndex := by
  simp [pythonNormalizeListIndex, negative]

theorem normalized_closed_list_position_is_in_bounds
    (rawIndex : Int) (length position : Nat)
    (normalized : normalizedClosedListPosition rawIndex length = some position) :
    position < length := by
  simp only [normalizedClosedListPosition] at normalized
  split at normalized
  next belowZero => contradiction
  next nonnegative =>
    split at normalized
    next inBounds =>
      injection normalized with positionEq
      subst position
      exact inBounds
    next outOfBounds => contradiction

theorem constant_fold_closed_list_success_is_exact
    (elementSort : ValueSort) (values : List Term) (rawIndex : Int) (value : Term)
    (folded :
      constantFoldClosedListIndex
        (.list elementSort values) (.intLiteral rawIndex) = some value) :
    inferSort (.list elementSort values) = some (.list elementSort) ∧
      values.length ≤ executableI64MaximumListLength ∧
      ∃ position,
        normalizedClosedListPosition rawIndex values.length = some position ∧
        values[position]? = some value ∧
        position < values.length := by
  simp only [constantFoldClosedListIndex] at folded
  split at folded
  next valid =>
    split at folded
    next bounded =>
      split at folded
      next position positionEq =>
        refine ⟨?_, bounded, position, positionEq, folded, ?_⟩
        . simp [inferSort, valid]
        . exact normalized_closed_list_position_is_in_bounds rawIndex values.length position positionEq
      next refused positionEq => contradiction
    next tooLong => contradiction
  next invalid => contradiction

theorem constant_fold_closed_list_refuses_nonliteral_index
    (elementSort : ValueSort) (values : List Term) (index : Term)
    (nonliteral : ∀ rawIndex, index ≠ .intLiteral rawIndex) :
    constantFoldClosedListIndex (.list elementSort values) index = none := by
  cases index <;> simp_all [constantFoldClosedListIndex]

theorem constant_fold_closed_list_refuses_unsafe_receiver
    (receiver index : Term)
    (notClosed : ∀ elementSort values, receiver ≠ .list elementSort values) :
    constantFoldClosedListIndex receiver index = none := by
  cases receiver <;> simp_all [constantFoldClosedListIndex]

theorem constant_fold_closed_list_refuses_malformed_list
    (elementSort : ValueSort) (values : List Term) (rawIndex : Int)
    (invalid : (isListElementSort elementSort && allOfSort values elementSort) = false) :
    constantFoldClosedListIndex
      (.list elementSort values) (.intLiteral rawIndex) = none := by
  simp [constantFoldClosedListIndex, invalid]

theorem constant_fold_closed_list_refuses_oversized_length
    (elementSort : ValueSort) (values : List Term) (rawIndex : Int)
    (tooLong : executableI64MaximumListLength < values.length) :
    constantFoldClosedListIndex
      (.list elementSort values) (.intLiteral rawIndex) = none := by
  simp [constantFoldClosedListIndex, Nat.not_le.mpr tooLong]

theorem constant_fold_closed_list_refuses_out_of_range
    (elementSort : ValueSort) (values : List Term) (rawIndex : Int)
    (outOfRange : normalizedClosedListPosition rawIndex values.length = none) :
    constantFoldClosedListIndex
      (.list elementSort values) (.intLiteral rawIndex) = none := by
  simp [constantFoldClosedListIndex, outOfRange]

theorem i64_minimum_is_out_of_range_for_supported_list
    (length : Nat) (bounded : length ≤ executableI64MaximumListLength) :
    normalizedClosedListPosition executableI64Minimum length = none := by
  have lengthLt : length < 2 ^ 63 := by
    simp [executableI64MaximumListLength, executableI64Magnitude] at bounded
    omega
  have castLt : (Int.ofNat length : Int) < Int.ofNat (2 ^ 63) :=
    Int.ofNat_lt.mpr lengthLt
  have minimumNegative : executableI64Minimum < 0 := by
    simp [executableI64Minimum, executableI64Magnitude]
  have belowZero : Int.ofNat length + executableI64Minimum < 0 := by
    simp only [executableI64Minimum, executableI64Magnitude]
    omega
  simp only [normalizedClosedListPosition]
  rw [python_normalize_negative executableI64Minimum length minimumNegative]
  simp only [if_pos belowZero]

theorem constant_fold_closed_list_refuses_i64_minimum
    (elementSort : ValueSort) (values : List Term) :
    constantFoldClosedListIndex
      (.list elementSort values) (.intLiteral executableI64Minimum) = none := by
  by_cases bounded : values.length ≤ executableI64MaximumListLength
  · exact constant_fold_closed_list_refuses_out_of_range elementSort values
      executableI64Minimum
      (i64_minimum_is_out_of_range_for_supported_list values.length bounded)
  · exact constant_fold_closed_list_refuses_oversized_length elementSort values
      executableI64Minimum (Nat.lt_of_not_ge bounded)

theorem constant_fold_closed_list_selects_positive_literal :
    constantFoldClosedListIndex
      (.list .int [.intLiteral 4, .variable "symbolic" .int, .intLiteral 9])
      (.intLiteral 1) = some (.variable "symbolic" .int) := by
  rfl

theorem constant_fold_closed_list_normalizes_negative_literal :
    constantFoldClosedListIndex
      (.list .int [.intLiteral 4, .variable "symbolic" .int, .intLiteral 9])
      (.intLiteral (-1)) = some (.intLiteral 9) := by
  rfl

end Maledictus
