import SolverSortPredicatesProofs.AxiomAudit

namespace SolverSortPredicates.AxiomAudit.Regression

theorem proofWithPlaceholder : True := by
  sorry

run_cmd SolverSortPredicates.AxiomAudit.assertExactAxioms SolverSortPredicates.AxiomAudit.permittedAxioms ``proofWithPlaceholder

end SolverSortPredicates.AxiomAudit.Regression
