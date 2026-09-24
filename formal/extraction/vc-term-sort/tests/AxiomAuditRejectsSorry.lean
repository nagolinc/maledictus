import VcTermSortProofs.AxiomAudit

open Lean Lean.Elab Lean.Elab.Command

namespace VcTermSort.AxiomAudit.Regression

theorem proofWithPlaceholder : True := by
  sorry

run_cmd VcTermSort.AxiomAudit.assertExactAxioms ``VcTermSort.AxiomAudit.Regression.proofWithPlaceholder #[]

end VcTermSort.AxiomAudit.Regression
