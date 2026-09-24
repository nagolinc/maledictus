import BindCallFullProofs.AxiomAudit

open Lean Lean.Elab Lean.Elab.Command

namespace BindCallFull.AxiomAudit.Regression

theorem proofWithPlaceholder : True := by
  sorry

run_cmd do
  BindCallFull.AxiomAudit.assertExactAxioms
    ``BindCallFull.AxiomAudit.Regression.proofWithPlaceholder
    #[]

end BindCallFull.AxiomAudit.Regression
