import IoSortKernelProofs.AxiomAudit

namespace IoSortKernel.AxiomAudit.Regression

axiom untrustedAssumption : True

theorem proofWithProjectAxiom : True :=
  untrustedAssumption

run_cmd IoSortKernel.AxiomAudit.assertOnlyPropext ``IoSortKernel.AxiomAudit.Regression.proofWithProjectAxiom

end IoSortKernel.AxiomAudit.Regression
