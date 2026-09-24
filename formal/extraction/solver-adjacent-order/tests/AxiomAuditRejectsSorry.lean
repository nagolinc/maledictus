import SolverAdjacentOrderProofs.AxiomAudit

namespace SolverAdjacentOrder.AxiomAudit.Regression

theorem proofWithPlaceholder : True := by
  sorry

run_cmd SolverAdjacentOrder.AxiomAudit.assertExactAxioms SolverAdjacentOrder.AxiomAudit.permittedAxioms ``proofWithPlaceholder

end SolverAdjacentOrder.AxiomAudit.Regression
