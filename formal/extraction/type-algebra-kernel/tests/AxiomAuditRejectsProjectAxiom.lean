import TypeAlgebraKernelProofs.AxiomAudit

namespace TypeAlgebraKernel.AxiomAudit.Regression

axiom untrustedAssumption : True

theorem proofWithProjectAxiom : True :=
  untrustedAssumption

run_cmd TypeAlgebraKernel.AxiomAudit.assertExactAxioms ``TypeAlgebraKernel.AxiomAudit.Regression.proofWithProjectAxiom TypeAlgebraKernel.AxiomAudit.nominalAxioms

end TypeAlgebraKernel.AxiomAudit.Regression
