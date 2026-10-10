import SolverSortPredicates.Code.FunsExternal

open Aeneas Aeneas.Std Result ControlFlow Error

section
open Lean.Order

private theorem SolverSortPredicates.result_order_cases {T : Type}
    {left right : Result T} (ordered : left ⊑ right) :
    left = .div ∨ left = right := by
  change FlatOrder.rel left right at ordered
  cases ordered with
  | bot => exact Or.inl rfl
  | refl => exact Or.inr rfl

/-- The Aeneas partial loop is monotone in a monotone loop body.  Upstream
Aeneas does not currently register this higher-order rule, which prevents its
own raw mutually recursive extraction from elaborating when a loop body calls
another member of the mutual group.  This constructive fixpoint-induction
proof lets us retain and compile the actual raw program for the normalization
correspondence theorem. -/
private theorem SolverSortPredicates.loop_body_monotone_function
    {State Output : Type} {Φ : Sort _} [Lean.Order.PartialOrder Φ]
    (body : Φ → State → Result (ControlFlow State Output))
    (bodyMonotone : Lean.Order.monotone body) :
    Lean.Order.monotone (fun parameter state => loop (body parameter) state) := by
  intro left right leftLeRight
  have bodyOrdered : ∀ state, body left state ⊑ body right state :=
    fun state => monotone_apply state body bodyMonotone left right leftLeRight
  apply loop.fixpoint_induct (body left)
    (motive := fun recur => ∀ state,
      recur state ⊑ loop (body right) state)
  · apply Lean.Order.admissible_pi
    intro state
    exact Lean.Order.admissible_apply
      (fun _ value => value ⊑ loop (body right) state) state
      (Lean.Order.admissible_flatOrder _ FlatOrder.rel.bot)
  · intro recur induction state
    simp only
    have stepOrdered := bodyOrdered state
    rcases SolverSortPredicates.result_order_cases stepOrdered with leftDiverges | same
    · rw [leftDiverges]
      exact FlatOrder.rel.bot
    · rw [same]
      unfold loop
      cases observed : body right state with
      | fail error =>
          simp [observed]
          exact Lean.Order.PartialOrder.rel_refl
      | div =>
          simp [observed]
          exact Lean.Order.PartialOrder.rel_refl
      | ok flow =>
          cases flow with
          | done output =>
              simp [observed]
              exact Lean.Order.PartialOrder.rel_refl
          | cont next => simp [observed, induction next]

@[partial_fixpoint_monotone]
theorem SolverSortPredicates.loop_body_monotone
    {State Output : Type} {Φ : Sort _} [Lean.Order.PartialOrder Φ]
    (body : Φ → State → Result (ControlFlow State Output))
    (bodyMonotone : Lean.Order.monotone body) (state : State) :
    Lean.Order.monotone (fun parameter => loop (body parameter) state) :=
  monotone_apply state _
    (SolverSortPredicates.loop_body_monotone_function body bodyMonotone)


end
