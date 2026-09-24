import VcTermSort.Helpers.Funs

open Aeneas Aeneas.Std Result

namespace VcTermSort.Proofs

def obligationSatisfied
    (expectation : VcTermSort.ObligationExpectation)
    (status : VcTermSort.ObligationStatus) : Bool :=
  match expectation, status with
  | .Prove, .Proved => true
  | .Refute, .Refuted => true
  | _, _ => false

theorem obligation_result_satisfied_exact (result : VcTermSort.ObligationResult) :
    VcTermSort.ObligationResult.satisfied result =
      .ok (obligationSatisfied result.expectation result.status) := by
  rcases result with ⟨id, expectation, status, counterexample, path, byteOffset, line, column⟩
  cases expectation <;> cases status <;> rfl

end VcTermSort.Proofs
