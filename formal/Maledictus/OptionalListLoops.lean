import Maledictus.Kernel

namespace Maledictus

/-!
# Optional-reference and symbolic List-loop algebra

This file is a constructive model of the bounded Optional and symbolic List-loop rules. An
Optional reference has an explicit null case, and a non-null guard exposes the nominal value only
on that branch. A symbolic loop always retains an exhaustion/fallthrough exit independently of an
arbitrary-element early-return exit. Iteration additionally requires an explicit list-predicate
permission token.

These theorems prove only the algebra below. The Rust AST frontend is not extracted into, or proved
to refine, this model, so this file contributes no Rust/frontend correspondence coverage.
-/

inductive OptionalReference (α : Type) where
  | null
  | value (reference : α)
  deriving DecidableEq

def narrowNonNull : OptionalReference α → Option α
  | .null => none
  | .value reference => some reference

theorem null_does_not_narrow :
    narrowNonNull (OptionalReference.null : OptionalReference α) = none := by
  rfl

theorem value_narrows_to_same_reference (reference : α) :
    narrowNonNull (.value reference) = some reference := by
  rfl

inductive SymbolicLoopExit (α : Type) where
  | exhausted
  | returned (value : α)
  deriving DecidableEq

def symbolicListLoopExits (candidate : Option α) : List (SymbolicLoopExit α) :=
  [.exhausted] ++ (candidate.map SymbolicLoopExit.returned).toList

theorem symbolic_loop_always_retains_exhaustion (candidate : Option α) :
    SymbolicLoopExit.exhausted ∈ symbolicListLoopExits candidate := by
  simp [symbolicListLoopExits]

theorem symbolic_loop_retains_arbitrary_element_return (value : α) :
    SymbolicLoopExit.returned value ∈ symbolicListLoopExits (some value) := by
  simp [symbolicListLoopExits]

structure ListPredicatePermission where
  available : Bool
  deriving DecidableEq

def symbolicIterationAllowed (permission : ListPredicatePermission) : Bool :=
  permission.available

theorem iteration_requires_list_predicate_permission :
    symbolicIterationAllowed ⟨false⟩ = false := by
  rfl

theorem explicit_list_predicate_permission_allows_iteration :
    symbolicIterationAllowed ⟨true⟩ = true := by
  rfl

end Maledictus
