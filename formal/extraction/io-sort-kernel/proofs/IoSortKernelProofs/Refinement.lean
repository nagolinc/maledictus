import IoSortKernel

open Aeneas Aeneas.Std Result

namespace IoSortKernel.Proofs

open python_io_contracts

def valueHasSortReference (value : Value) (expected : IoSort) : Bool :=
  match value, expected with
  | .Place _, .Place => true
  | .Int _, .Int => true
  | .SymbolicInt _, .Int => true
  | _, _ => false

def sameValueSortReference (left right : Value) : Bool :=
  match left, right with
  | .Place _, .Place _ => true
  | .Int _, .Int _ => true
  | .Int _, .SymbolicInt _ => true
  | .SymbolicInt _, .Int _ => true
  | .SymbolicInt _, .SymbolicInt _ => true
  | _, _ => false

theorem value_has_sort_matches_reference (value : Value) (expected : IoSort) :
    python_io_contracts.value_has_sort value expected =
      .ok (valueHasSortReference value expected) := by
  cases value <;> cases expected <;> rfl

theorem same_value_sort_matches_reference (left right : Value) :
    python_io_contracts.same_value_sort left right =
      .ok (sameValueSortReference left right) := by
  cases left <;> cases right <;> rfl

theorem value_has_sort_is_total (value : Value) (expected : IoSort) :
    ∃ result, python_io_contracts.value_has_sort value expected = .ok result := by
  exact ⟨valueHasSortReference value expected,
    value_has_sort_matches_reference value expected⟩

theorem same_value_sort_is_total (left right : Value) :
    ∃ result, python_io_contracts.same_value_sort left right = .ok result := by
  exact ⟨sameValueSortReference left right,
    same_value_sort_matches_reference left right⟩

end IoSortKernel.Proofs

