import Maledictus.Kernel

namespace Maledictus

/-!
# Constructive undeclared exceptional-exit classification (v53)

This finite IR classifies the exceptional exits already represented by `ExitEffect`.
An uncaught raised type is covered exactly when the callable declares it.  Otherwise a
non-application exit is reported at the callable boundary, while an operation failure
whose proof obligation is an application precondition is reported at that operation.

The batch classifier is structurally bounded by its input list.  An `ExitEffect.unknown`
does not disappear as though it were safe: it produces `none`, forcing the caller to
refuse a purported complete classification.
-/

inductive ExceptionalExitOrigin where
  | nonApplication
  | applicationPrecondition
  deriving DecidableEq

structure ExceptionalExitTrace where
  effect : ExitEffect
  origin : ExceptionalExitOrigin
  caught : Bool
  callableBoundary : String
  operationSite : String
  deriving DecidableEq

inductive UndeclaredExitDiagnosticCode where
  | exhaleFailed
  | applicationPrecondition
  deriving DecidableEq

inductive UndeclaredExitBlame where
  | callableBoundary (site : String)
  | operationSite (site : String)
  deriving DecidableEq

structure UndeclaredExitDiagnostic where
  exceptionType : String
  code : UndeclaredExitDiagnosticCode
  blame : UndeclaredExitBlame
  deriving DecidableEq

inductive ExceptionalExitClassification where
  | noUndeclaredDiagnostic
  | diagnostic (value : UndeclaredExitDiagnostic)
  | unmodeled
  deriving DecidableEq

def undeclaredExitDiagnostic
    (trace : ExceptionalExitTrace) (exceptionType : String) :
    UndeclaredExitDiagnostic :=
  match trace.origin with
  | .nonApplication => {
      exceptionType
      code := .exhaleFailed
      blame := .callableBoundary trace.callableBoundary
    }
  | .applicationPrecondition => {
      exceptionType
      code := .applicationPrecondition
      blame := .operationSite trace.operationSite
    }

def classifyExceptionalExit
    (declaredExceptionTypes : List String)
    (trace : ExceptionalExitTrace) : ExceptionalExitClassification :=
  match trace.effect with
  | .returned _ => .noUndeclaredDiagnostic
  | .unknown _ => .unmodeled
  | .raised exceptionType =>
      if trace.caught || effectAllowed declaredExceptionTypes trace.effect then
        .noUndeclaredDiagnostic
      else
        .diagnostic (undeclaredExitDiagnostic trace exceptionType)

/--
Classify a finite exit set, preserving source order.  `none` means at least one exit
was unknown, so the supplied exit set was not a constructive completeness witness.
-/
def classifyExceptionalExits
    (declaredExceptionTypes : List String) :
    List ExceptionalExitTrace → Option (List UndeclaredExitDiagnostic)
  | [] => some []
  | trace :: rest =>
      match classifyExceptionalExit declaredExceptionTypes trace,
          classifyExceptionalExits declaredExceptionTypes rest with
      | .unmodeled, _ => none
      | _, none => none
      | .noUndeclaredDiagnostic, some diagnostics => some diagnostics
      | .diagnostic diagnostic, some diagnostics => some (diagnostic :: diagnostics)

theorem returned_exit_produces_no_undeclared_diagnostic
    (declaredExceptionTypes : List String) (trace : ExceptionalExitTrace)
    (result : String) (returned : trace.effect = .returned result) :
    classifyExceptionalExit declaredExceptionTypes trace = .noUndeclaredDiagnostic := by
  simp [classifyExceptionalExit, returned]

theorem caught_exit_produces_no_undeclared_diagnostic
    (declaredExceptionTypes : List String) (trace : ExceptionalExitTrace)
    (exceptionType : String) (raised : trace.effect = .raised exceptionType)
    (caught : trace.caught = true) :
    classifyExceptionalExit declaredExceptionTypes trace = .noUndeclaredDiagnostic := by
  simp [classifyExceptionalExit, raised, caught]

theorem declared_exit_produces_no_undeclared_diagnostic
    (declaredExceptionTypes : List String) (trace : ExceptionalExitTrace)
    (exceptionType : String) (raised : trace.effect = .raised exceptionType)
    (declared : exceptionType ∈ declaredExceptionTypes) :
    classifyExceptionalExit declaredExceptionTypes trace = .noUndeclaredDiagnostic := by
  simp [classifyExceptionalExit, raised, effectAllowed, declared]

theorem unknown_exit_is_explicitly_unmodeled
    (declaredExceptionTypes : List String) (trace : ExceptionalExitTrace)
    (description : String) (unknown : trace.effect = .unknown description) :
    classifyExceptionalExit declaredExceptionTypes trace = .unmodeled := by
  simp [classifyExceptionalExit, unknown]

theorem uncaught_undeclared_nonapplication_exit_blames_callable_boundary
    (declaredExceptionTypes : List String) (trace : ExceptionalExitTrace)
    (exceptionType : String) (raised : trace.effect = .raised exceptionType)
    (uncaught : trace.caught = false)
    (undeclared : exceptionType ∉ declaredExceptionTypes)
    (ordinary : trace.origin = .nonApplication) :
    classifyExceptionalExit declaredExceptionTypes trace = .diagnostic {
      exceptionType
      code := .exhaleFailed
      blame := .callableBoundary trace.callableBoundary
    } := by
  simp [classifyExceptionalExit, raised, uncaught, effectAllowed, undeclared,
    undeclaredExitDiagnostic, ordinary]

theorem uncaught_undeclared_application_failure_blames_operation_site
    (declaredExceptionTypes : List String) (trace : ExceptionalExitTrace)
    (exceptionType : String) (raised : trace.effect = .raised exceptionType)
    (uncaught : trace.caught = false)
    (undeclared : exceptionType ∉ declaredExceptionTypes)
    (application : trace.origin = .applicationPrecondition) :
    classifyExceptionalExit declaredExceptionTypes trace = .diagnostic {
      exceptionType
      code := .applicationPrecondition
      blame := .operationSite trace.operationSite
    } := by
  simp [classifyExceptionalExit, raised, uncaught, effectAllowed, undeclared,
    undeclaredExitDiagnostic, application]

theorem emitted_undeclared_diagnostic_is_uncaught_and_undeclared
    (declaredExceptionTypes : List String) (trace : ExceptionalExitTrace)
    (diagnostic : UndeclaredExitDiagnostic)
    (classified : classifyExceptionalExit declaredExceptionTypes trace =
      .diagnostic diagnostic) :
    ∃ exceptionType,
      trace.effect = .raised exceptionType ∧
      trace.caught = false ∧
      exceptionType ∉ declaredExceptionTypes ∧
      diagnostic = undeclaredExitDiagnostic trace exceptionType := by
  cases effect : trace.effect with
  | returned result => simp [classifyExceptionalExit, effect] at classified
  | unknown description => simp [classifyExceptionalExit, effect] at classified
  | raised exceptionType =>
      by_cases caught : trace.caught = true
      · simp [classifyExceptionalExit, effect, caught] at classified
      · have uncaught : trace.caught = false := by
          cases found : trace.caught <;> simp_all
        by_cases declared : exceptionType ∈ declaredExceptionTypes
        · simp [classifyExceptionalExit, effect, uncaught, effectAllowed, declared] at classified
        · refine ⟨exceptionType, rfl, uncaught, declared, ?_⟩
          simpa [classifyExceptionalExit, effect, uncaught, effectAllowed, declared] using
            classified.symm

theorem emitted_diagnostic_blame_matches_origin
    (declaredExceptionTypes : List String) (trace : ExceptionalExitTrace)
    (diagnostic : UndeclaredExitDiagnostic)
    (classified : classifyExceptionalExit declaredExceptionTypes trace =
      .diagnostic diagnostic) :
    (trace.origin = .nonApplication →
        diagnostic.code = .exhaleFailed ∧
        diagnostic.blame = .callableBoundary trace.callableBoundary) ∧
      (trace.origin = .applicationPrecondition →
        diagnostic.code = .applicationPrecondition ∧
        diagnostic.blame = .operationSite trace.operationSite) := by
  obtain ⟨exceptionType, _, _, _, exactDiagnostic⟩ :=
    emitted_undeclared_diagnostic_is_uncaught_and_undeclared
      declaredExceptionTypes trace diagnostic classified
  subst diagnostic
  cases origin : trace.origin <;> simp [undeclaredExitDiagnostic, origin]

theorem classification_output_is_bounded_by_exit_count
    (declaredExceptionTypes : List String) (traces : List ExceptionalExitTrace)
    (diagnostics : List UndeclaredExitDiagnostic)
    (classified : classifyExceptionalExits declaredExceptionTypes traces = some diagnostics) :
    diagnostics.length ≤ traces.length := by
  induction traces generalizing diagnostics with
  | nil => simp [classifyExceptionalExits] at classified; simp [classified]
  | cons trace rest inductionHypothesis =>
      simp only [classifyExceptionalExits] at classified
      cases single : classifyExceptionalExit declaredExceptionTypes trace with
      | unmodeled => simp [single] at classified
      | noUndeclaredDiagnostic =>
        cases tail : classifyExceptionalExits declaredExceptionTypes rest with
        | none => simp [single, tail] at classified
        | some tailDiagnostics =>
            simp [single, tail] at classified
            subst diagnostics
            exact Nat.le_trans
              (inductionHypothesis tailDiagnostics tail) (Nat.le_succ _)
      | diagnostic diagnostic =>
        cases tail : classifyExceptionalExits declaredExceptionTypes rest with
        | none => simp [single, tail] at classified
        | some tailDiagnostics =>
            simp [single, tail] at classified
            subst diagnostics
            exact Nat.succ_le_succ
              (inductionHypothesis tailDiagnostics tail)

theorem unknown_exit_makes_batch_classification_fail_closed
    (declaredExceptionTypes : List String) (trace : ExceptionalExitTrace)
    (rest : List ExceptionalExitTrace) (description : String)
    (unknown : trace.effect = .unknown description) :
    classifyExceptionalExits declaredExceptionTypes (trace :: rest) = none := by
  simp [classifyExceptionalExits, classifyExceptionalExit, unknown]

end Maledictus
