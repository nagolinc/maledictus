import SolverSortPredicatesProofs.Refinement
import SolverSortPredicatesProofs.RawCorrespondence
import Lean.Util.CollectAxioms

open Lean Lean.Elab Lean.Elab.Command

namespace SolverSortPredicates.AxiomAudit

def assertExactAxioms (expected : Array Name) (declaration : Name) : CommandElabM Unit := do
  let actual ← Lean.collectAxioms declaration
  unless actual.qsort Name.lt == expected.qsort Name.lt do
    throwError
      "axiom audit failed for '{declaration}': expected {expected.toList}, got {actual.toList}"

#guard #[Name.mkSimple ("sorr" ++ "yAx")] != #[``propext]

def permittedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

end SolverSortPredicates.AxiomAudit

open SolverSortPredicates.AxiomAudit

run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.Proofs.collection_key_sort_all_inputs_exact
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.Proofs.collection_value_sort_all_inputs_exact
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.Proofs.nested_equality_sort_all_inputs_exact
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.Proofs.float_collection_value_is_admitted
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.Proofs.nested_float_collection_value_is_admitted
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.Proofs.float_collection_key_is_rejected
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.Proofs.float_nested_equality_is_still_rejected
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.RawProofs.collection_key_sort_all_inputs_exact
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.RawProofs.collection_value_sort_all_inputs_exact
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.RawProofs.nested_equality_sort_all_inputs_exact
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.RawProofs.collection_key_raw_eq_normalized
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.RawProofs.collection_value_raw_eq_normalized
run_cmd assertExactAxioms permittedAxioms ``SolverSortPredicates.RawProofs.nested_equality_raw_eq_normalized
