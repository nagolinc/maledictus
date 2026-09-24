import VcTermSortProofs.StructuredRefinement
import VcTermSortProofs.Helpers
import Lean.Util.CollectAxioms

open Aeneas Aeneas.Std Result ControlFlow Error
open Lean Lean.Elab Lean.Elab.Command

namespace VcTermSort.AxiomAudit

def exactAxiomSet (actual expected : Array Name) : Bool :=
  actual.qsort Name.lt == expected.qsort Name.lt

def assertExactAxioms (declaration : Name) (expected : Array Name) : CommandElabM Unit := do
  let actual ← Lean.collectAxioms declaration
  if !exactAxiomSet actual expected then
    throwError
      "axiom audit failed for '{declaration}': expected exactly {expected.qsort Name.lt |>.toList}, got {actual.qsort Name.lt |>.toList}"

def standardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

#guard !exactAxiomSet #[Name.mkSimple ("sorr" ++ "yAx")] standardAxioms
#guard !exactAxiomSet #[``propext, ``Classical.choice, ``Quot.sound, `Maledictus.unexpectedAxiom] standardAxioms

end VcTermSort.AxiomAudit

open VcTermSort.AxiomAudit

namespace VcTermSort.Proofs

run_cmd assertExactAxioms ``VcTermSort.Proofs.term_sort_terminates standardAxioms
run_cmd assertExactAxioms ``VcTermSort.Proofs.term_sort_extraction_entrypoint_terminates standardAxioms
run_cmd assertExactAxioms ``VcTermSort.Proofs.term_sort_extraction_entrypoint_structured_refinement standardAxioms
run_cmd assertExactAxioms ``VcTermSort.RawProofs.term_sort_terminates standardAxioms
run_cmd assertExactAxioms ``VcTermSort.RawProofs.term_sort_extraction_entrypoint_terminates standardAxioms
run_cmd assertExactAxioms ``VcTermSort.Proofs.raw_term_sort_typed_eq_normalized standardAxioms
run_cmd assertExactAxioms ``VcTermSort.Proofs.raw_term_sort_extraction_entrypoint_eq_normalized standardAxioms
run_cmd assertExactAxioms ``VcTermSort.Proofs.raw_term_sort_extraction_entrypoint_structured_refinement standardAxioms
run_cmd assertExactAxioms ``VcTermSort.Proofs.obligation_result_satisfied_exact #[``propext]

end VcTermSort.Proofs
