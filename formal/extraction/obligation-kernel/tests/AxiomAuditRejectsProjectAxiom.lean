import ObligationKernelProofs.AxiomAudit

namespace ObligationKernel.AxiomAudit.Regression

axiom untrustedAssumption : True

theorem proofWithProjectAxiom : True := untrustedAssumption

run_cmd ObligationKernel.AxiomAudit.assertExactAxioms ObligationKernel.AxiomAudit.permittedAxioms ``ObligationKernel.AxiomAudit.Regression.proofWithProjectAxiom

end ObligationKernel.AxiomAudit.Regression
