import ObligationKernelProofs.AxiomAudit

namespace ObligationKernel.AxiomAudit.Regression

theorem proofWithPlaceholder : True := by
  sorry

run_cmd ObligationKernel.AxiomAudit.assertExactAxioms ObligationKernel.AxiomAudit.permittedAxioms ``ObligationKernel.AxiomAudit.Regression.proofWithPlaceholder

end ObligationKernel.AxiomAudit.Regression
