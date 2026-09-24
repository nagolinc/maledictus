import PersistentCollectionsProofs.Refinement
import Lean.Util.CollectAxioms

open Lean Lean.Elab Lean.Elab.Command

namespace PersistentCollections.AxiomAudit

def exactAxiomSet (actual expected : Array Name) : Bool :=
  actual.qsort Name.lt == expected.qsort Name.lt

def assertExactAxioms (declaration : Name) (expected : Array Name) :
    CommandElabM Unit := do
  let actual ← Lean.collectAxioms declaration
  if !exactAxiomSet actual expected then
    throwError
      "axiom audit failed for '{declaration}': expected exactly {expected.qsort Name.lt |>.toList}, got {actual.qsort Name.lt |>.toList}"

def requireAxioms : Array Name := #[``propext]
def concatenationAxioms : Array Name := #[``propext, ``Quot.sound]
def uniqueAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

#guard !exactAxiomSet #[Name.mkSimple ("sorr" ++ "yAx")] requireAxioms
#guard !exactAxiomSet
  #[``propext, ``Quot.sound, `Maledictus.unexpectedAxiom]
  concatenationAxioms
#guard !exactAxiomSet
  #[``propext, ``Classical.choice, ``Quot.sound,
    Name.mkSimple ("sorr" ++ "yAx")]
  uniqueAxioms
#guard !exactAxiomSet
  #[``propext, ``Classical.choice, ``Quot.sound,
    `Maledictus.unexpectedAxiom]
  uniqueAxioms

end PersistentCollections.AxiomAudit

open PersistentCollections.AxiomAudit

run_cmd assertExactAxioms ``PersistentCollections.Proofs.require_compatible_kinds_all_inputs requireAxioms
run_cmd assertExactAxioms ``PersistentCollections.Proofs.concatenate_success_all_values concatenationAxioms
run_cmd assertExactAxioms ``PersistentCollections.Proofs.concatenate_kind_error_all_values concatenationAxioms
run_cmd assertExactAxioms ``PersistentCollections.Proofs.concatenate_capacity_failure_all_values concatenationAxioms
run_cmd assertExactAxioms ``PersistentCollections.Proofs.concatenate_never_diverges concatenationAxioms
run_cmd assertExactAxioms ``PersistentCollections.Proofs.concatenate_all_inputs_exact concatenationAxioms
run_cmd assertExactAxioms ``PersistentCollections.Proofs.unique_loop_exact uniqueAxioms
run_cmd assertExactAxioms ``PersistentCollections.Proofs.unique_all_inputs_exact uniqueAxioms
