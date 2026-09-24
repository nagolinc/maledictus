import VcTermSort.Code.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace VcTermSort.Proofs

theorem entrypoint_is_term_sort (term : VcTermSort.Term) :
    VcTermSort.term_sort_extraction_entrypoint term = VcTermSort.Term.sort_typed term := by
  rfl

/-- The final all-input implementation relation can be proved against the
    generated method body: the transparent extraction wrapper adds no separate
    semantic obligation. This theorem deliberately does not assume or assert
    that the production Rust result already equals either side. -/
theorem entrypoint_correspondence_iff
    (production : VcTermSort.Term →
      Result (core.result.Result VcTermSort.Sort VcTermSort.SortError)) :
    (∀ term, production term = VcTermSort.term_sort_extraction_entrypoint term) ↔
      (∀ term, production term = VcTermSort.Term.sort_typed term) := by
  constructor <;> intro correspondence term
  · rw [← entrypoint_is_term_sort]
    exact correspondence term
  · rw [entrypoint_is_term_sort]
    exact correspondence term

theorem sort_clone_exact (sort : VcTermSort.Sort) :
    VcTermSort.Sort.Insts.CoreCloneClone.clone sort = .ok sort := by
  rfl

theorem model_vec_with_capacity_exact {T : Type} (capacity : Usize) :
    VcTermSort.ModelVec.with_capacity T capacity = [] := by
  rfl

theorem model_vec_is_empty_exact {T : Type} (values : VcTermSort.ModelVec T) :
    VcTermSort.ModelVec.is_empty T values = .ok values.isEmpty := by
  rfl

mutual

theorem sort_model_eq_internal_true_iff : ∀ left right : VcTermSort.Sort,
    sortModelEq left right = true ↔ left = right
  | .Bool, right
  | .Int, right
  | .Float, right
  | .String, right
  | .Unit, right
  | .Reference, right
  | .Class, right
  | .Bytes, right
  | .Range, right => by cases right <;> simp [sortModelEq]
  | .Tuple left, right => by
      cases right <;> simp [sortModelEq, sort_model_list_eq_internal_true_iff left]
  | .List left, right => by
      cases right <;> simp [sortModelEq, sort_model_eq_internal_true_iff left]
  | .VariadicTuple left, right => by
      cases right <;> simp [sortModelEq, sort_model_eq_internal_true_iff left]
  | .Set left, right => by
      cases right <;> simp [sortModelEq, sort_model_eq_internal_true_iff left]
  | .Dict leftKey leftValue, right => by
      cases right <;>
        simp [sortModelEq, sort_model_eq_internal_true_iff leftKey,
          sort_model_eq_internal_true_iff leftValue]
  | .FiniteDict leftKey leftValue, right => by
      cases right <;>
        simp [sortModelEq, sort_model_eq_internal_true_iff leftKey,
          sort_model_eq_internal_true_iff leftValue]
  | .DictKeys left, right => by
      cases right <;> simp [sortModelEq, sort_model_eq_internal_true_iff left]

theorem sort_model_list_eq_internal_true_iff : ∀ left right : List VcTermSort.Sort,
    sortModelListEq left right = true ↔ left = right
  | [], right => by cases right <;> simp [sortModelListEq]
  | leftHead :: leftTail, right => by
      cases right with
      | nil => simp [sortModelListEq]
      | cons rightHead rightTail =>
          simp [sortModelListEq, sort_model_eq_internal_true_iff leftHead,
            sort_model_list_eq_internal_true_iff leftTail]

end

theorem sort_model_eq_true_iff (left right : VcTermSort.Sort) :
    VcTermSort.sortModelEqPublic left right = true ↔ left = right := by
  exact sort_model_eq_internal_true_iff left right

theorem sort_model_list_eq_true_iff (left right : List VcTermSort.Sort) :
    VcTermSort.sortModelListEqPublic left right = true ↔ left = right := by
  exact sort_model_list_eq_internal_true_iff left right

theorem sort_partial_eq_exact (left right : VcTermSort.Sort) :
    VcTermSort.Sort.Insts.CoreCmpPartialEqSort.eq left right = .ok true ↔
      left = right := by
  constructor
  · intro observed
    have modeled :
        Result.ok (VcTermSort.sortModelEqPublic left right) = Result.ok true :=
      Eq.trans (VcTermSort.sortPartialEqModel left right).symm observed
    have structural : VcTermSort.sortModelEqPublic left right = true := by
      exact Result.ok.inj modeled
    exact (sort_model_eq_true_iff left right).mp structural
  · intro equal
    have structural : VcTermSort.sortModelEqPublic left right = true :=
      (sort_model_eq_true_iff left right).mpr equal
    exact Eq.trans (VcTermSort.sortPartialEqModel left right)
      (congrArg Result.ok structural)

/-- A finite execution certificate for the constructive loop runner. The trace
    records every continuation and retains success, failure, and divergence as
    distinct terminal outcomes. -/
inductive FiniteLoopTrace {State Output : Type}
    (body : State → Result (ControlFlow State Output)) :
    Nat → State → Result Output → Prop where
  | done {state output}
      (step : body state = .ok (.done output)) :
      FiniteLoopTrace body 1 state (.ok output)
  | fail {state error}
      (step : body state = .fail error) :
      FiniteLoopTrace body 1 state (.fail error)
  | div {state}
      (step : body state = .div) :
      FiniteLoopTrace body 1 state .div
  | cont {steps state next result}
      (step : body state = .ok (.cont next))
      (tail : FiniteLoopTrace body steps next result) :
      FiniteLoopTrace body (steps + 1) state result

theorem run_loop_fuel_of_trace {State Output : Type}
    {body : State → Result (ControlFlow State Output)}
    {steps : Nat} {state : State} {result : Result Output}
    (trace : FiniteLoopTrace body steps state result) :
    VcTermSort.runLoopFuel steps body state = result := by
  induction trace with
  | done step => simp [VcTermSort.runLoopFuel, step]
  | fail step => simp [VcTermSort.runLoopFuel, step]
  | div step => simp [VcTermSort.runLoopFuel, step]
  | cont step tail induction =>
      simp [VcTermSort.runLoopFuel, step, induction]

theorem run_loop_fuel_with_headroom_of_trace {State Output : Type}
    {body : State → Result (ControlFlow State Output)}
    {steps : Nat} {state : State} {result : Result Output}
    (trace : FiniteLoopTrace body steps state result) (headroom : Nat) :
    VcTermSort.runLoopFuel (steps + headroom) body state = result := by
  induction trace generalizing headroom with
  | done step =>
      rw [Nat.add_comm]
      simp [VcTermSort.runLoopFuel, step]
  | fail step =>
      rw [Nat.add_comm]
      simp [VcTermSort.runLoopFuel, step]
  | div step =>
      rw [Nat.add_comm]
      simp [VcTermSort.runLoopFuel, step]
  | cont step tail induction =>
      rw [Nat.add_right_comm]
      simp [VcTermSort.runLoopFuel, step, induction headroom]

/-- Any loop body whose continuation states strictly decrease a natural
    measure has a finite trace bounded by the initial measure plus the final
    terminal check. This is the reusable termination argument for all eleven
    normalized slice loops. -/
theorem finite_loop_trace_exists_of_decreases {State Output : Type}
    (body : State → Result (ControlFlow State Output)) (measure : State → Nat)
    (decreases : ∀ state next,
      body state = .ok (.cont next) → measure next < measure state)
    (state : State) :
    ∃ steps result,
      steps ≤ measure state + 1 ∧ FiniteLoopTrace body steps state result := by
  cases observed : body state with
  | fail error =>
      exact ⟨1, .fail error, by omega, .fail observed⟩
  | div =>
      exact ⟨1, .div, by omega, .div observed⟩
  | ok flow =>
      cases flow with
      | done output =>
          exact ⟨1, .ok output, by omega, .done observed⟩
      | cont next =>
          have smaller := decreases state next observed
          obtain ⟨steps, result, bounded, trace⟩ :=
            finite_loop_trace_exists_of_decreases body measure decreases next
          exact ⟨steps + 1, result, by omega, .cont observed trace⟩
termination_by measure state
decreasing_by exact smaller

def sliceIteratorRemaining {T : Type} (iter : core.slice.iter.Iter T) : Nat :=
  iter.slice.val.length - iter.i

theorem slice_iterator_next_some_decreases {T : Type}
    (iter next : core.slice.iter.Iter T) (value : T)
    (observed : core.slice.iter.IteratorSliceIter.next iter =
      .ok (some value, next)) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  unfold core.slice.iter.IteratorSliceIter.next at observed
  split at observed
  · simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at observed
    have within : iter.i < iter.slice.val.length := by
      simpa using ‹iter.i < iter.slice.len›
    obtain ⟨_, rfl⟩ := observed
    change iter.slice.val.length - (iter.i + 1) <
      iter.slice.val.length - iter.i
    omega
  · simp at observed

end VcTermSort.Proofs
