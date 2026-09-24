import BindCallFullProofs.Composition
import Lean.Util.CollectAxioms

open Aeneas Aeneas.Std Result
open Lean Lean.Elab Lean.Elab.Command

namespace BindCallFull.AxiomAudit

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

end BindCallFull.AxiomAudit

open BindCallFull.AxiomAudit

namespace BindCallFull.Proofs

run_cmd assertExactAxioms ``BindCallFull.Proofs.bind_call_with_allocator_matches_exact_reference standardAxioms
run_cmd assertExactAxioms ``BindCallFull.Proofs.canonical_environment_matches_reference standardAxioms
run_cmd assertExactAxioms ``BindCallFull.Proofs.expand_actual_items_with_allocator_matches_reference standardAxioms
run_cmd assertExactAxioms ``BindCallFull.Proofs.validate_signature_matches_reference standardAxioms
run_cmd assertExactAxioms ``BindCallFull.Proofs.bindingResultView_injective #[``propext]
run_cmd assertExactAxioms ``BindCallFull.Proofs.call_signature_default_exact #[``propext]
run_cmd assertExactAxioms ``BindCallFull.Proofs.exact_type_compatibility_accepts_exact #[]
run_cmd assertExactAxioms ``BindCallFull.Proofs.callback_type_compatibility_accepts_exact #[]
run_cmd assertExactAxioms ``BindCallFull.Proofs.type_compatibility_accepts_implementations_exact #[]

end BindCallFull.Proofs
