namespace Maledictus

/-!
Constructive model-only algebra for the bounded behavioral-override declaration check.

This file is not extracted Rust and is not a frontend-refinement proof. Production obtains method
kind, keyword-callable parameter order, declared exceptional outcomes, and nominal subclass edges
from the source AST and its source-ordered binding catalog.
-/

inductive OverrideMethodKind where
  | ordinary
  | pure
  deriving DecidableEq, Repr

structure OverrideBoundary where
  kind : OverrideMethodKind
  keywordParameters : List String
  deriving DecidableEq, Repr

def overrideBoundaryCompatible
    (inherited derived : OverrideBoundary)
    (derivedExceptionsNarrowed : Bool) : Bool :=
  inherited.kind == .ordinary
    && derived.kind == .ordinary
    && inherited.keywordParameters == derived.keywordParameters
    && derivedExceptionsNarrowed

theorem identical_ordinary_narrowed_boundary_is_compatible (parameters : List String) :
    overrideBoundaryCompatible
      { kind := .ordinary, keywordParameters := parameters }
      { kind := .ordinary, keywordParameters := parameters }
      true = true := by
  simp [overrideBoundaryCompatible]

theorem pure_inherited_boundary_is_incompatible
    (inheritedParameters derivedParameters : List String)
    (exceptionsNarrowed : Bool) :
    overrideBoundaryCompatible
      { kind := .pure, keywordParameters := inheritedParameters }
      { kind := .ordinary, keywordParameters := derivedParameters }
      exceptionsNarrowed = false := by
  simp [overrideBoundaryCompatible]

theorem pure_derived_boundary_is_incompatible
    (inheritedParameters derivedParameters : List String)
    (exceptionsNarrowed : Bool) :
    overrideBoundaryCompatible
      { kind := .ordinary, keywordParameters := inheritedParameters }
      { kind := .pure, keywordParameters := derivedParameters }
      exceptionsNarrowed = false := by
  simp [overrideBoundaryCompatible]

theorem widened_exception_channel_is_incompatible
    (parameters : List String) :
    overrideBoundaryCompatible
      { kind := .ordinary, keywordParameters := parameters }
      { kind := .ordinary, keywordParameters := parameters }
      false = false := by
  simp [overrideBoundaryCompatible]

end Maledictus
