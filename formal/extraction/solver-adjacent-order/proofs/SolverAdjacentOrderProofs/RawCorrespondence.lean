import SolverAdjacentOrder.Code.RawFuns
import SolverAdjacentOrderProofs.Top
import SolverAdjacentOrderProofs.LoopNormalization

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section

namespace SolverAdjacentOrder.Proofs

/-- Every continuation of the actual extracted unwrap loop selects the unique
    child of an And node. No bound on the depth of that input is assumed. -/
theorem unwrap_body_continuation_decreases (term next : vc.Term)
    (continuation : solver.unwrap_singleton_and_loop.body term = .ok (.cont next)) :
    sizeOf next < sizeOf term := by
  cases term <;>
    try { solve | simp [solver.unwrap_singleton_and_loop.body] at continuation }
  case And values =>
    cases values with
    | nil =>
        simp [solver.unwrap_singleton_and_loop.body, ModelVec.len,
          ModelVec.asVec] at continuation
    | cons first tail =>
        cases tail with
        | nil =>
            have maxPositive : Usize.max ≠ 0 := by scalar_tac
            simp [solver.unwrap_singleton_and_loop.body, ModelVec.len,
              ModelVec.index, ModelVec.asVec, alloc.vec.Vec.index_usize,
              maxPositive] at continuation
            subst next
            simp
            omega
        | cons second rest =>
            have maxAboveOne : 1 < Usize.max := by scalar_tac
            have lengthNotOne : min Usize.max (rest.length + 1 + 1) ≠ 1 := by
              omega
            simp [solver.unwrap_singleton_and_loop.body, ModelVec.len,
              ModelVec.asVec, lengthNotOne] at continuation

theorem raw_unwrap_body_equals_normalized (term : vc.Term) :
    SolverAdjacentOrderRaw.solver.unwrap_singleton_and_loop.body term =
      solver.unwrap_singleton_and_loop.body term := by
  rfl

/-- The raw partial loop and the finite runner agree for every source value,
    preserving failures and divergence of the loop body. Fuel follows from a
    structural decrease, not from an application-size cap. -/
theorem raw_unwrap_loop_equals_normalized (term : vc.Term) :
    SolverAdjacentOrderRaw.solver.unwrap_singleton_and_loop term =
      solver.unwrap_singleton_and_loop term := by
  change loop SolverAdjacentOrderRaw.solver.unwrap_singleton_and_loop.body term =
    runLoopFuel (sizeOf term + 1) solver.unwrap_singleton_and_loop.body term
  have bodyEqual : SolverAdjacentOrderRaw.solver.unwrap_singleton_and_loop.body =
      solver.unwrap_singleton_and_loop.body :=
    funext raw_unwrap_body_equals_normalized
  rw [bodyEqual]
  exact partial_loop_eq_fuel_of_decreases
    solver.unwrap_singleton_and_loop.body sizeOf unwrap_body_continuation_decreases term

theorem raw_unwrap_singleton_and_equals_normalized (term : vc.Term) :
    SolverAdjacentOrderRaw.solver.unwrap_singleton_and term =
      solver.unwrap_singleton_and term :=
  raw_unwrap_loop_equals_normalized term

theorem raw_is_integer_literal_equals_normalized (term : vc.Term) (expected : Std.I64) :
    SolverAdjacentOrderRaw.solver.is_integer_literal term expected =
      solver.is_integer_literal term expected := by
  rfl

theorem raw_is_bound_variable_equals_normalized (term : vc.Term) (binder : Str) :
    SolverAdjacentOrderRaw.solver.is_bound_variable term binder =
      solver.is_bound_variable term binder := by
  rfl

theorem raw_is_bound_successor_equals_normalized (term : vc.Term) (binder : Str) :
    SolverAdjacentOrderRaw.solver.is_bound_successor term binder =
      solver.is_bound_successor term binder := by
  rfl

theorem raw_is_nonnegative_bound_equals_normalized
    (term : vc.Term) (binder : Str) (remaining : Slice vc.Term) :
    SolverAdjacentOrderRaw.solver.is_nonnegative_bound term binder remaining =
      solver.is_nonnegative_bound term binder remaining := by
  rcases remaining with ⟨remaining, bounded⟩
  induction remaining generalizing term with
  | nil =>
      rw [SolverAdjacentOrderRaw.solver.is_nonnegative_bound.eq_def,
        solver.is_nonnegative_bound.eq_def]
      cases term <;> simp [core.slice.Slice.split_first,
        raw_is_integer_literal_equals_normalized, raw_is_bound_variable_equals_normalized]
  | cons next tail inductionHypothesis =>
      rw [SolverAdjacentOrderRaw.solver.is_nonnegative_bound.eq_def,
        solver.is_nonnegative_bound.eq_def]
      cases term <;> simp [core.slice.Slice.split_first,
        raw_is_integer_literal_equals_normalized, raw_is_bound_variable_equals_normalized,
        inductionHypothesis]

theorem raw_is_adjacent_upper_bound_equals_normalized
    (term : vc.Term) (binder : Str) (sorted : vc.Term) (remaining : Slice vc.Term) :
    SolverAdjacentOrderRaw.solver.is_adjacent_upper_bound term binder sorted remaining =
      solver.is_adjacent_upper_bound term binder sorted remaining := by
  rcases remaining with ⟨remaining, bounded⟩
  induction remaining generalizing term with
  | nil =>
      rw [SolverAdjacentOrderRaw.solver.is_adjacent_upper_bound.eq_def,
        solver.is_adjacent_upper_bound.eq_def]
      cases term <;> simp [core.slice.Slice.split_first,
        raw_is_bound_successor_equals_normalized]
      all_goals intros; rfl
  | cons next tail inductionHypothesis =>
      rw [SolverAdjacentOrderRaw.solver.is_adjacent_upper_bound.eq_def,
        solver.is_adjacent_upper_bound.eq_def]
      cases term <;> simp [core.slice.Slice.split_first,
        raw_is_bound_successor_equals_normalized, inductionHypothesis]
      all_goals
        intros
        rfl

theorem raw_is_python_index_of_equals_normalized
    (term : vc.Term) (binder : Str) (sorted : vc.Term) (successor : Bool) :
    SolverAdjacentOrderRaw.solver.is_python_index_of term binder sorted successor =
      solver.is_python_index_of term binder sorted successor := by
  unfold SolverAdjacentOrderRaw.solver.is_python_index_of solver.is_python_index_of
  simp only [raw_is_bound_successor_equals_normalized,
    raw_is_bound_variable_equals_normalized, raw_unwrap_singleton_and_equals_normalized,
    raw_is_integer_literal_equals_normalized,
    SolverAdjacentOrderRaw.vc.Term.Insts.CoreCmpPartialEqTerm,
    SolverAdjacentOrder.vc.Term.Insts.CoreCmpPartialEqTerm]
  rfl

theorem raw_is_exact_sorted_adjacent_order_equals_normalized (term : vc.Term) :
    SolverAdjacentOrderRaw.solver.is_exact_sorted_adjacent_order_theorem term =
      solver.is_exact_sorted_adjacent_order_theorem term := by
  unfold SolverAdjacentOrderRaw.solver.is_exact_sorted_adjacent_order_theorem
    solver.is_exact_sorted_adjacent_order_theorem
  simp only [raw_unwrap_singleton_and_equals_normalized,
    raw_is_python_index_of_equals_normalized,
    raw_is_nonnegative_bound_equals_normalized,
    raw_is_adjacent_upper_bound_equals_normalized,
    SolverAdjacentOrderRaw.vc.Term.Insts.CoreCmpPartialEqTerm,
    SolverAdjacentOrder.vc.Term.Insts.CoreCmpPartialEqTerm]
  rfl

/-- Transport the checked specification through the raw extraction, rather
    than certifying only the manually normalized finite runner. -/
theorem raw_is_exact_sorted_adjacent_order_all_inputs_exact (term : vc.Term) :
    SolverAdjacentOrderRaw.solver.is_exact_sorted_adjacent_order_theorem term =
      exactSortedAdjacentOrderSpec term := by
  rw [raw_is_exact_sorted_adjacent_order_equals_normalized]
  exact is_exact_sorted_adjacent_order_theorem_all_inputs_exact term

end SolverAdjacentOrder.Proofs
