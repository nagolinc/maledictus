import KernelExitEffectsProofs.AxiomAudit

namespace KernelExitEffects.AxiomAudit.Regression

theorem proofWithPlaceholder : True := by
  sorry

run_cmd KernelExitEffects.AxiomAudit.assertExactAxioms KernelExitEffects.AxiomAudit.permittedAxioms ``KernelExitEffects.AxiomAudit.Regression.proofWithPlaceholder

end KernelExitEffects.AxiomAudit.Regression
