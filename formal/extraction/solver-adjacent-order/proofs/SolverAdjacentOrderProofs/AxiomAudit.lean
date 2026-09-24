import SolverAdjacentOrderProofs.Top
import Lean.Util.CollectAxioms

open Lean Lean.Elab Lean.Elab.Command

namespace SolverAdjacentOrder.AxiomAudit

def assertExactAxioms (expected : Array Name) (declaration : Name) : CommandElabM Unit := do
  let actual ← Lean.collectAxioms declaration
  unless actual.qsort Name.lt == expected.qsort Name.lt do
    throwError
      "axiom audit failed for '{declaration}': expected {expected.toList}, got {actual.toList}"

#guard #[Name.mkSimple ("sorr" ++ "yAx")] != #[``propext]

def structuralAxioms : Array Name := #[``propext, ``Quot.sound]

def recursiveAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def permittedAxioms : Array Name := recursiveAxioms

end SolverAdjacentOrder.AxiomAudit

open SolverAdjacentOrder.AxiomAudit

run_cmd assertExactAxioms structuralAxioms ``SolverAdjacentOrder.Proofs.is_integer_literal_all_inputs_exact
run_cmd assertExactAxioms structuralAxioms ``SolverAdjacentOrder.Proofs.is_bound_variable_all_inputs_exact
run_cmd assertExactAxioms recursiveAxioms ``SolverAdjacentOrder.Proofs.is_bound_successor_all_inputs_exact
run_cmd assertExactAxioms recursiveAxioms ``SolverAdjacentOrder.Proofs.unwrap_singleton_and_all_inputs_exact
run_cmd assertExactAxioms recursiveAxioms ``SolverAdjacentOrder.Proofs.is_python_index_of_all_inputs_exact
run_cmd assertExactAxioms recursiveAxioms ``SolverAdjacentOrder.Proofs.is_nonnegative_bound_all_inputs_exact
run_cmd assertExactAxioms recursiveAxioms ``SolverAdjacentOrder.Proofs.is_adjacent_upper_bound_all_inputs_exact
run_cmd assertExactAxioms recursiveAxioms ``SolverAdjacentOrder.Proofs.is_exact_sorted_adjacent_order_theorem_all_inputs_exact
