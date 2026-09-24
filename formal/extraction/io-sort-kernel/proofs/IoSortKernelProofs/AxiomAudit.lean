import IoSortKernelProofs.Refinement
import Lean.Util.CollectAxioms

open Lean Lean.Elab Lean.Elab.Command

namespace IoSortKernel.AxiomAudit

def assertOnlyPropext (declaration : Name) : CommandElabM Unit := do
  let actual ← Lean.collectAxioms declaration
  unless actual.qsort Name.lt == #[``propext] do
    throwError
      "axiom audit failed for '{declaration}': expected only propext, got {actual.toList}"

#guard #[Name.mkSimple ("sorr" ++ "yAx")] != #[``propext]

end IoSortKernel.AxiomAudit

open IoSortKernel.AxiomAudit

run_cmd assertOnlyPropext ``IoSortKernel.Proofs.value_has_sort_matches_reference
run_cmd assertOnlyPropext ``IoSortKernel.Proofs.same_value_sort_matches_reference
run_cmd assertOnlyPropext ``IoSortKernel.Proofs.value_has_sort_is_total
run_cmd assertOnlyPropext ``IoSortKernel.Proofs.same_value_sort_is_total
