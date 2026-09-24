import BindCallFullProofs.AxiomAudit

open Lean Lean.Elab Lean.Elab.Command

namespace BindCallFull.AxiomAudit.Regression

axiom untrustedAssumption : True

theorem proofWithProjectAxiom : True :=
  untrustedAssumption

run_cmd do
  BindCallFull.AxiomAudit.assertExactAxioms
    ``BindCallFull.AxiomAudit.Regression.proofWithProjectAxiom
    #[]

end BindCallFull.AxiomAudit.Regression
