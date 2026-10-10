import SolverAdjacentOrderProofs.RawCorrespondence

open Aeneas Aeneas.Std Result

namespace SolverAdjacentOrder.Proofs

/-- Each source-node coverage claim names the actual extracted function,
    not merely the finite-runner normalization used to discharge its proof. -/
theorem raw_is_integer_literal_all_inputs_exact (term : vc.Term) (expected : Std.I64) :
    SolverAdjacentOrderRaw.solver.is_integer_literal term expected =
      .ok (integerLiteralSpec term expected) := by
  rw [raw_is_integer_literal_equals_normalized]
  exact is_integer_literal_all_inputs_exact term expected

theorem raw_is_bound_variable_all_inputs_exact (term : vc.Term) (binder : Str) :
    SolverAdjacentOrderRaw.solver.is_bound_variable term binder =
      boundVariableSpec term binder := by
  rw [raw_is_bound_variable_equals_normalized]
  exact is_bound_variable_all_inputs_exact term binder

theorem raw_is_bound_successor_all_inputs_exact (term : vc.Term) (binder : Str) :
    SolverAdjacentOrderRaw.solver.is_bound_successor term binder =
      boundSuccessorSpec term binder := by
  rw [raw_is_bound_successor_equals_normalized]
  exact is_bound_successor_all_inputs_exact term binder

theorem raw_unwrap_singleton_and_all_inputs_exact (term : vc.Term) :
    SolverAdjacentOrderRaw.solver.unwrap_singleton_and term =
      unwrapSingletonAndSpec term := by
  rw [raw_unwrap_singleton_and_equals_normalized]
  exact unwrap_singleton_and_all_inputs_exact term

theorem raw_is_python_index_of_all_inputs_exact
    (term : vc.Term) (binder : Str) (sorted : vc.Term) (successor : Bool) :
    SolverAdjacentOrderRaw.solver.is_python_index_of term binder sorted successor =
      pythonIndexSpec term binder sorted successor := by
  rw [raw_is_python_index_of_equals_normalized]
  exact is_python_index_of_all_inputs_exact term binder sorted successor

theorem raw_is_nonnegative_bound_all_inputs_exact
    (term : vc.Term) (binder : Str) (remaining : Slice vc.Term) :
    SolverAdjacentOrderRaw.solver.is_nonnegative_bound term binder remaining =
      nonnegativeBoundSpec term binder remaining.val := by
  rw [raw_is_nonnegative_bound_equals_normalized]
  exact is_nonnegative_bound_all_inputs_exact term binder remaining

theorem raw_is_adjacent_upper_bound_all_inputs_exact
    (term : vc.Term) (binder : Str) (sorted : vc.Term) (remaining : Slice vc.Term) :
    SolverAdjacentOrderRaw.solver.is_adjacent_upper_bound term binder sorted remaining =
      adjacentBoundSpec term binder sorted remaining.val := by
  rw [raw_is_adjacent_upper_bound_equals_normalized]
  exact is_adjacent_upper_bound_all_inputs_exact term binder sorted remaining

end SolverAdjacentOrder.Proofs
