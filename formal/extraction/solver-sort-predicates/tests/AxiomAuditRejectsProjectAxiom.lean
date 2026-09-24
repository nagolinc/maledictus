import SolverSortPredicatesProofs.AxiomAudit

namespace SolverSortPredicates.AxiomAudit.Regression

axiom untrustedAssumption : True

theorem proofWithProjectAxiom : True :=
  untrustedAssumption

run_cmd SolverSortPredicates.AxiomAudit.assertExactAxioms SolverSortPredicates.AxiomAudit.permittedAxioms ``proofWithProjectAxiom

end SolverSortPredicates.AxiomAudit.Regression
