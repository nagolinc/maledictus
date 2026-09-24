namespace Maledictus

/-!
Model-only algebra for the bounded Python object-identity fragment.

This file is constructive documentation of the source-level rules. It is not an extraction or a
Rust-to-Lean refinement proof. The production frontend keeps these identities beside value terms:
equal values do not thereby become identical objects.
-/

inductive PythonObjectIdentity where
  | emptyTuple
  | internedString (value : String)
  | fresh (allocation : Nat)
  | uncertain (allocation : Nat)
  deriving DecidableEq, Repr

/-- `some true/false` is a proved identity result; `none` preserves implementation uncertainty. -/
def pythonIdentityRelation
    (left right : PythonObjectIdentity) : Option Bool :=
  if left = right then
    some true
  else
    match left, right with
    | .uncertain _, _ => none
    | _, .uncertain _ => none
    | _, _ => some false

theorem python_identity_is_reflexive (identity : PythonObjectIdentity) :
    pythonIdentityRelation identity identity = some true := by
  simp [pythonIdentityRelation]

theorem distinct_fresh_allocations_are_not_identical
    (left right : Nat) (different : left ≠ right) :
    pythonIdentityRelation (.fresh left) (.fresh right) = some false := by
  simp [pythonIdentityRelation, different]

theorem aliases_preserve_uncertain_identity (allocation : Nat) :
    pythonIdentityRelation (.uncertain allocation) (.uncertain allocation) = some true := by
  simp [pythonIdentityRelation]

theorem uncertain_and_distinct_identity_stays_unknown
    (allocation : Nat) (other : PythonObjectIdentity)
    (different : PythonObjectIdentity.uncertain allocation ≠ other) :
    pythonIdentityRelation (.uncertain allocation) other = none := by
  simp [pythonIdentityRelation, different]

theorem equal_interned_values_are_identical (value : String) :
    pythonIdentityRelation (.internedString value) (.internedString value) = some true := by
  simp [pythonIdentityRelation]

end Maledictus
