import VcTermSortProofs.AxiomAudit

open Lean Lean.Elab Lean.Elab.Command

namespace VcTermSort.AxiomAudit.Regression

axiom untrustedAssumption : True

theorem proofWithProjectAxiom : True :=
  untrustedAssumption

run_cmd VcTermSort.AxiomAudit.assertExactAxioms ``VcTermSort.AxiomAudit.Regression.proofWithProjectAxiom #[]

end VcTermSort.AxiomAudit.Regression
