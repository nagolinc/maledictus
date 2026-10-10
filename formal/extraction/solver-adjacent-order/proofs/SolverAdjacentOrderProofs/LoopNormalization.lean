import SolverAdjacentOrder.Code.FunsExternal

open Aeneas Aeneas.Std Result ControlFlow Error

namespace SolverAdjacentOrder.Proofs

/-- Any strictly decreasing continuation has exactly the same result under
    the extracted partial loop and a sufficiently fuelled finite runner.
    Failure and divergence of the loop body are preserved, not assumed away. -/
theorem partial_loop_eq_fuel_of_bound {State Output : Type}
    (body : State → Result (ControlFlow State Output))
    (measure : State → Nat)
    (decreases : ∀ state next,
      body state = .ok (.cont next) → measure next < measure state)
    (fuel : Nat) (state : State) (sufficient : measure state < fuel) :
    loop body state = runLoopFuel fuel body state := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel inductionHypothesis =>
      rw [runLoopFuel]
      unfold loop
      cases observed : body state with
      | fail error => simp [observed]
      | div => simp [observed]
      | ok flow =>
          cases flow with
          | done output => simp [observed]
          | cont next =>
              have smaller := decreases state next observed
              have enough : measure next < fuel := by omega
              simpa [observed] using inductionHypothesis next enough

theorem partial_loop_eq_fuel_of_decreases {State Output : Type}
    (body : State → Result (ControlFlow State Output))
    (measure : State → Nat)
    (decreases : ∀ state next,
      body state = .ok (.cont next) → measure next < measure state)
    (state : State) :
    loop body state = runLoopFuel (measure state + 1) body state :=
  partial_loop_eq_fuel_of_bound body measure decreases _ state (by omega)

end SolverAdjacentOrder.Proofs
