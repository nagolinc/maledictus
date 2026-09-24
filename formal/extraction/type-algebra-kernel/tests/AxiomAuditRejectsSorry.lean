import TypeAlgebraKernelProofs.AxiomAudit

namespace TypeAlgebraKernel.AxiomAudit.Regression

theorem proofWithPlaceholder : True := by
  sorry

run_cmd TypeAlgebraKernel.AxiomAudit.assertExactAxioms ``TypeAlgebraKernel.AxiomAudit.Regression.proofWithPlaceholder TypeAlgebraKernel.AxiomAudit.nominalAxioms

end TypeAlgebraKernel.AxiomAudit.Regression
