namespace Maledictus

/-!
Constructive model-only algebra for bounded abstract-predicate fold resolution.

This file is not extracted Rust and is not a frontend-refinement proof. Production derives
predicate kind, exact receiver provenance, and effective inherited method declarations from the
real Python AST and source-ordered binding catalog.
-/

inductive PredicateKind where
  | concrete
  | abstract
  deriving DecidableEq, Repr

inductive PredicateResolution where
  | unknown
  | known (kind : PredicateKind)
  deriving DecidableEq, Repr

def foldAllowed : PredicateResolution → Bool
  | .known .concrete => true
  | .known .abstract => false
  | .unknown => false

def resolveExactReceiver
    (receiverClass : Option String)
    (methodCatalog : String → String → Option PredicateKind)
    (methodName : String) : PredicateResolution :=
  match receiverClass with
  | none => .unknown
  | some className =>
      match methodCatalog className methodName with
      | none => .unknown
      | some kind => .known kind

theorem concrete_predicate_can_be_folded :
    foldAllowed (.known .concrete) = true := by
  rfl

theorem abstract_predicate_cannot_be_folded :
    foldAllowed (.known .abstract) = false := by
  rfl

theorem unknown_receiver_cannot_manufacture_fold_permission
    (catalog : String → String → Option PredicateKind)
    (methodName : String) :
    foldAllowed (resolveExactReceiver none catalog methodName) = false := by
  rfl

theorem exact_abstract_method_is_rejected
    (catalog : String → String → Option PredicateKind)
    (className methodName : String)
    (resolved : catalog className methodName = some .abstract) :
    foldAllowed (resolveExactReceiver (some className) catalog methodName) = false := by
  simp [resolveExactReceiver, resolved, foldAllowed]

theorem exact_concrete_method_is_accepted
    (catalog : String → String → Option PredicateKind)
    (className methodName : String)
    (resolved : catalog className methodName = some .concrete) :
    foldAllowed (resolveExactReceiver (some className) catalog methodName) = true := by
  simp [resolveExactReceiver, resolved, foldAllowed]

end Maledictus
