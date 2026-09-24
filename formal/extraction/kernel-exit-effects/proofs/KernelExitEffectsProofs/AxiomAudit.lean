import KernelExitEffectsProofs.Refinement
import Lean.Util.CollectAxioms

open Lean Lean.Elab Lean.Elab.Command

namespace KernelExitEffects.AxiomAudit

def assertExactAxioms (expected : Array Name) (declaration : Name) : CommandElabM Unit := do
  let actual ← Lean.collectAxioms declaration
  unless actual.qsort Name.lt == expected.qsort Name.lt do
    throwError
      "axiom audit failed for '{declaration}': expected {expected.toList}, got {actual.toList}"

#guard #[Name.mkSimple ("sorr" ++ "yAx")] != #[``propext]

def permittedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

end KernelExitEffects.AxiomAudit

open KernelExitEffects.AxiomAudit

run_cmd assertExactAxioms permittedAxioms ``KernelExitEffects.Proofs.check_exit_effects_all_inputs_exact
