import SolverAdjacentOrderProofs.AxiomAudit

namespace SolverAdjacentOrder.AxiomAudit.Regression

axiom untrustedAssumption : True

theorem proofWithProjectAxiom : True :=
  untrustedAssumption

run_cmd SolverAdjacentOrder.AxiomAudit.assertExactAxioms SolverAdjacentOrder.AxiomAudit.permittedAxioms ``proofWithProjectAxiom

end SolverAdjacentOrder.AxiomAudit.Regression
