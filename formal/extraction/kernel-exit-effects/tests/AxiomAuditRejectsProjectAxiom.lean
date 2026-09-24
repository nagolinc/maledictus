import KernelExitEffectsProofs.AxiomAudit

namespace KernelExitEffects.AxiomAudit.Regression

axiom untrustedAssumption : True

theorem proofWithProjectAxiom : True :=
  untrustedAssumption

run_cmd KernelExitEffects.AxiomAudit.assertExactAxioms KernelExitEffects.AxiomAudit.permittedAxioms ``KernelExitEffects.AxiomAudit.Regression.proofWithProjectAxiom

end KernelExitEffects.AxiomAudit.Regression
