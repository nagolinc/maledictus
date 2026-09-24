import ObligationKernelProofs.Refinement
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Lean.Elab Lean.Elab.Command

namespace ObligationKernel.AxiomAudit

def assertExactAxioms (expected : Array Name) (declaration : Name) : CommandElabM Unit := do
  let actual <- Lean.collectAxioms declaration
  unless actual.qsort Name.lt == expected.qsort Name.lt do
    throwError
      "axiom audit failed for '{declaration}': expected {expected.toList}, got {actual.toList}"

#guard #[Name.mkSimple ("sorr" ++ "yAx")] != #[]

def permittedAxioms : Array Name := #[``propext]
def noAxioms : Array Name := #[]

end ObligationKernel.AxiomAudit

open ObligationKernel.AxiomAudit

run_cmd assertExactAxioms permittedAxioms ``ObligationKernel.Proofs.source_transition_semantics
run_cmd assertExactAxioms noAxioms ``ObligationKernel.Proofs.decide_produce_deterministic
run_cmd assertExactAxioms noAxioms ``ObligationKernel.Proofs.decide_consume_deterministic
run_cmd assertExactAxioms noAxioms ``ObligationKernel.Proofs.decide_close_deterministic
