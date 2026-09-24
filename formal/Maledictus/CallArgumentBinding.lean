import Maledictus.Kernel

namespace Maledictus

/-!
# Finite Python call-argument binding

This module is a closed mathematical model of the v59 call-binding boundary.  A signature has
finite positional parameters, finite keyword-only parameters, and optional `*args` and `**kwargs`
parameters.  Actual arguments are expanded left-to-right; a fixed star contributes its elements
at exactly its location in the positional stream.  Method receiver injection is represented by a
distinguished positional origin rather than by comparing runtime values.

The model deliberately does not claim that a Python AST or the Rust frontend corresponds to these
definitions.  It also does not model arbitrary iterable star expansion, evaluation effects,
positional-only parameters, or dynamic `**mapping` expansion.  Those remain frontend proof
obligations.  The values below are abstract typed atoms; `payload` exists only to distinguish
values having the same type tag.
-/

structure CallValue where
  typeTag : String
  payload : Int
  deriving DecidableEq, Repr

structure FormalParameter where
  name : String
  expectedType : String
  defaultValue : Option CallValue := none
  deriving DecidableEq, Repr

structure CallSignature where
  positional : List FormalParameter
  keywordOnly : List FormalParameter
  varArgs : Option FormalParameter := none
  keywordArgs : Option FormalParameter := none
  deriving DecidableEq, Repr

inductive FormalKind where
  | positional
  | keywordOnly
  | varArgs
  | keywordArgs
  deriving DecidableEq, Repr

structure FormalSlot where
  parameter : FormalParameter
  kind : FormalKind
  deriving DecidableEq, Repr

def CallSignature.orderedSlots (signature : CallSignature) : List FormalSlot :=
  signature.positional.map (fun parameter => { parameter, kind := .positional }) ++
  signature.keywordOnly.map (fun parameter => { parameter, kind := .keywordOnly }) ++
  signature.varArgs.toList.map (fun parameter => { parameter, kind := .varArgs }) ++
  signature.keywordArgs.toList.map (fun parameter => { parameter, kind := .keywordArgs })

def CallSignature.formalNames (signature : CallSignature) : List String :=
  signature.orderedSlots.map (fun slot => slot.parameter.name)

def defaultHasExpectedType (parameter : FormalParameter) : Prop :=
  ∀ value, parameter.defaultValue = some value → value.typeTag = parameter.expectedType

def CallSignature.WellFormed (signature : CallSignature) : Prop :=
  signature.formalNames.Nodup ∧
  (∀ parameter ∈ signature.positional, defaultHasExpectedType parameter) ∧
  (∀ parameter ∈ signature.keywordOnly, defaultHasExpectedType parameter) ∧
  (∀ parameter ∈ signature.varArgs, parameter.defaultValue = none) ∧
  (∀ parameter ∈ signature.keywordArgs, parameter.defaultValue = none)

inductive ActualItem where
  | positional (value : CallValue)
  | named (name : String) (value : CallValue)
  | fixedStar (values : List CallValue)
  deriving DecidableEq, Repr

inductive PositionalOrigin where
  | explicit
  | fixedStar
  | receiver
  deriving DecidableEq, Repr

structure PositionalActual where
  value : CallValue
  origin : PositionalOrigin
  deriving DecidableEq, Repr

structure NamedActual where
  name : String
  value : CallValue
  deriving DecidableEq, Repr

structure ExpandedCall where
  positional : List PositionalActual
  named : List NamedActual
  deriving DecidableEq, Repr

def expandActualItems : List ActualItem → ExpandedCall
  | [] => { positional := [], named := [] }
  | item :: rest =>
      let expandedRest := expandActualItems rest
      match item with
      | .positional value =>
          { expandedRest with positional := { value, origin := .explicit } :: expandedRest.positional }
      | .named name value =>
          { expandedRest with named := { name, value } :: expandedRest.named }
      | .fixedStar values =>
          { expandedRest with
            positional := values.map (fun value => { value, origin := .fixedStar }) ++
              expandedRest.positional }

def injectReceiver (receiver : CallValue) (items : List ActualItem) : ExpandedCall :=
  let expanded := expandActualItems items
  { expanded with positional := { value := receiver, origin := .receiver } :: expanded.positional }

theorem fixed_star_preserves_exact_order (values : List CallValue) (rest : List ActualItem) :
    (expandActualItems (.fixedStar values :: rest)).positional =
      values.map (fun value => { value, origin := PositionalOrigin.fixedStar }) ++
        (expandActualItems rest).positional := by
  rfl

theorem named_item_does_not_change_positional_order
    (name : String) (value : CallValue) (rest : List ActualItem) :
    (expandActualItems (.named name value :: rest)).positional =
      (expandActualItems rest).positional := by
  rfl

theorem receiver_is_injected_first (receiver : CallValue) (items : List ActualItem) :
    (injectReceiver receiver items).positional.head? =
      some { value := receiver, origin := PositionalOrigin.receiver } := by
  rfl

def receiverOriginCount : List PositionalActual → Nat
  | [] => 0
  | actual :: rest =>
      (if actual.origin = .receiver then 1 else 0) + receiverOriginCount rest

theorem fixed_star_values_have_no_receiver_origin (values : List CallValue) :
    receiverOriginCount
      (values.map (fun value => { value, origin := PositionalOrigin.fixedStar })) = 0 := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp [receiverOriginCount, inductionHypothesis]

theorem receiver_origin_count_append (first second : List PositionalActual) :
    receiverOriginCount (first ++ second) =
      receiverOriginCount first + receiverOriginCount second := by
  induction first with
  | nil => simp [receiverOriginCount]
  | cons actual rest inductionHypothesis =>
      simp [receiverOriginCount, inductionHypothesis, Nat.add_assoc]

theorem expanded_source_has_no_receiver_origin (items : List ActualItem) :
    receiverOriginCount (expandActualItems items).positional = 0 := by
  induction items with
  | nil => rfl
  | cons item rest inductionHypothesis =>
      cases item with
      | positional value => simp [expandActualItems, receiverOriginCount, inductionHypothesis]
      | named name value => simpa [expandActualItems] using inductionHypothesis
      | fixedStar values =>
          rw [show (expandActualItems (ActualItem.fixedStar values :: rest)).positional =
            values.map (fun value => { value, origin := PositionalOrigin.fixedStar }) ++
              (expandActualItems rest).positional from rfl]
          rw [receiver_origin_count_append, fixed_star_values_have_no_receiver_origin,
            inductionHypothesis]

theorem receiver_injection_has_one_receiver_origin (receiver : CallValue) (items : List ActualItem) :
    receiverOriginCount (injectReceiver receiver items).positional = 1 := by
  simp [injectReceiver, receiverOriginCount, expanded_source_has_no_receiver_origin]

def namedValue (actuals : List NamedActual) (name : String) : Option CallValue :=
  (actuals.find? (fun actual => actual.name == name)).map (fun actual => actual.value)

def positionalFormalNames (signature : CallSignature) : List String :=
  signature.positional.map (fun parameter => parameter.name)

def ordinaryFormalNames (signature : CallSignature) : List String :=
  positionalFormalNames signature ++ signature.keywordOnly.map (fun parameter => parameter.name)

def residualKeywordActuals (signature : CallSignature) (call : ExpandedCall) : List NamedActual :=
  call.named.filter (fun actual => actual.name ∉ ordinaryFormalNames signature)

inductive BoundArgument where
  | suppliedPositional (actual : PositionalActual)
  | suppliedNamed (actual : CallValue)
  | defaulted (value : CallValue)
  | residualPositionals (values : List PositionalActual)
  | residualKeywords (values : List NamedActual)
  deriving DecidableEq, Repr

structure BindingCell where
  slot : FormalSlot
  assignment : Option BoundArgument
  deriving DecidableEq, Repr

abbrev ProofEnvironment := List BindingCell

def ordinaryAssignment
    (positional : Option PositionalActual)
    (named : Option CallValue)
    (defaultValue : Option CallValue) : Option BoundArgument :=
  match positional, named with
  | some _, some _ => none
  | some actual, none => some (.suppliedPositional actual)
  | none, some actual => some (.suppliedNamed actual)
  | none, none => defaultValue.map .defaulted

theorem default_assignment_requires_no_supplied_argument
    (positional : Option PositionalActual) (named defaultValue : Option CallValue)
    (value : CallValue)
    (assigned : ordinaryAssignment positional named defaultValue =
      some (.defaulted value)) :
    positional = none ∧ named = none ∧ defaultValue = some value := by
  cases positional with
  | none =>
      cases named with
      | none =>
          simp [ordinaryAssignment] at assigned
          exact ⟨rfl, rfl, assigned⟩
      | some supplied => simp [ordinaryAssignment] at assigned
  | some supplied =>
      cases named <;> simp [ordinaryAssignment] at assigned

def bindPositionalCells :
    List FormalParameter → List PositionalActual → List NamedActual → List BindingCell
  | [], _, _ => []
  | parameter :: rest, positional, named =>
      let position := positional.head?
      let assignment := ordinaryAssignment position (namedValue named parameter.name)
        parameter.defaultValue
      { slot := { parameter, kind := .positional }, assignment } ::
        bindPositionalCells rest positional.tail named

def bindKeywordOnlyCells
    (parameters : List FormalParameter) (named : List NamedActual) : List BindingCell :=
  parameters.map (fun parameter =>
    { slot := { parameter, kind := .keywordOnly }
      assignment := ordinaryAssignment none (namedValue named parameter.name)
        parameter.defaultValue })

def bindVarArgsCell
    (signature : CallSignature) (call : ExpandedCall) : List BindingCell :=
  signature.varArgs.toList.map (fun parameter =>
    { slot := { parameter, kind := .varArgs }
      assignment := some (.residualPositionals (call.positional.drop signature.positional.length)) })

def bindKeywordArgsCell
    (signature : CallSignature) (call : ExpandedCall) : List BindingCell :=
  signature.keywordArgs.toList.map (fun parameter =>
    { slot := { parameter, kind := .keywordArgs }
      assignment := some (.residualKeywords (residualKeywordActuals signature call)) })

def canonicalEnvironment (signature : CallSignature) (call : ExpandedCall) : ProofEnvironment :=
  bindPositionalCells signature.positional call.positional call.named ++
  bindKeywordOnlyCells signature.keywordOnly call.named ++
  bindVarArgsCell signature call ++
  bindKeywordArgsCell signature call

def environmentNames (environment : ProofEnvironment) : List String :=
  environment.map (fun cell => cell.slot.parameter.name)

theorem bind_positional_cell_names
    (parameters : List FormalParameter) (positional : List PositionalActual)
    (named : List NamedActual) :
    environmentNames (bindPositionalCells parameters positional named) =
      parameters.map (fun parameter => parameter.name) := by
  induction parameters generalizing positional with
  | nil => rfl
  | cons parameter rest inductionHypothesis =>
      change parameter.name ::
          environmentNames (bindPositionalCells rest positional.tail named) =
        parameter.name :: rest.map (fun parameter => parameter.name)
      rw [inductionHypothesis]

theorem canonical_environment_names_are_formal_names
    (signature : CallSignature) (call : ExpandedCall) :
    environmentNames (canonicalEnvironment signature call) = signature.formalNames := by
  have positionalNames :
      (bindPositionalCells signature.positional call.positional call.named).map
          (fun cell => cell.slot.parameter.name) =
        signature.positional.map (fun parameter => parameter.name) := by
    simpa [environmentNames] using
      bind_positional_cell_names signature.positional call.positional call.named
  simp only [canonicalEnvironment, environmentNames, List.map_append]
  rw [positionalNames]
  simp [CallSignature.formalNames, CallSignature.orderedSlots, bindKeywordOnlyCells,
    bindVarArgsCell, bindKeywordArgsCell, Function.comp_def]

def positionallyBoundNames : List FormalParameter → List PositionalActual → List String
  | parameter :: parameters, _ :: actuals =>
      parameter.name :: positionallyBoundNames parameters actuals
  | _, _ => []

def namedActualNames (call : ExpandedCall) : List String :=
  call.named.map (fun actual => actual.name)

def noDuplicateBinding (signature : CallSignature) (call : ExpandedCall) : Prop :=
  ∀ name ∈ positionallyBoundNames signature.positional call.positional,
    name ∉ namedActualNames call

def excessPositionalsAccepted (signature : CallSignature) (call : ExpandedCall) : Prop :=
  call.positional.length ≤ signature.positional.length ∨ signature.varArgs.isSome

def unexpectedKeywordsAccepted (signature : CallSignature) (call : ExpandedCall) : Prop :=
  residualKeywordActuals signature call = [] ∨ signature.keywordArgs.isSome

def allCellsAssigned (environment : ProofEnvironment) : Prop :=
  ∀ cell ∈ environment, ∃ assignment, cell.assignment = some assignment

def argumentHasExpectedType (expected : String) : BoundArgument → Prop
  | .suppliedPositional actual => actual.value.typeTag = expected
  | .suppliedNamed value => value.typeTag = expected
  | .defaulted value => value.typeTag = expected
  | .residualPositionals actuals => ∀ actual ∈ actuals, actual.value.typeTag = expected
  | .residualKeywords actuals => ∀ actual ∈ actuals, actual.value.typeTag = expected

def environmentWellTyped (environment : ProofEnvironment) : Prop :=
  ∀ cell ∈ environment, ∀ assignment,
    cell.assignment = some assignment →
      argumentHasExpectedType cell.slot.parameter.expectedType assignment

structure CallConditions (signature : CallSignature) (call : ExpandedCall) : Prop where
  signatureWellFormed : signature.WellFormed
  namedActualsUnique : (namedActualNames call).Nodup
  noDuplicateBinding : noDuplicateBinding signature call
  excessPositionalsAccepted : excessPositionalsAccepted signature call
  unexpectedKeywordsAccepted : unexpectedKeywordsAccepted signature call
  everyFormalAssigned : allCellsAssigned (canonicalEnvironment signature call)
  assignmentsWellTyped : environmentWellTyped (canonicalEnvironment signature call)

def ValidProofEnvironment
    (signature : CallSignature) (call : ExpandedCall) (environment : ProofEnvironment) : Prop :=
  environment = canonicalEnvironment signature call ∧ CallConditions signature call

inductive BindingError where
  | malformedSignature
  | duplicateNamedArgument
  | duplicateBinding
  | tooManyPositionals
  | unexpectedKeyword
  | missingRequiredArgument
  | typeMismatch
  deriving DecidableEq, Repr

inductive BindingResult (signature : CallSignature) (call : ExpandedCall) where
  | success (environment : ProofEnvironment)
      (proof : ValidProofEnvironment signature call environment)
  | error (reason : BindingError)

noncomputable def diagnoseBindingFailure
    (signature : CallSignature) (call : ExpandedCall) : BindingError := by
  classical
  exact
    if ¬signature.WellFormed then .malformedSignature
    else if ¬(namedActualNames call).Nodup then .duplicateNamedArgument
    else if ¬noDuplicateBinding signature call then .duplicateBinding
    else if ¬excessPositionalsAccepted signature call then .tooManyPositionals
    else if ¬unexpectedKeywordsAccepted signature call then .unexpectedKeyword
    else if ¬allCellsAssigned (canonicalEnvironment signature call) then .missingRequiredArgument
    else .typeMismatch

noncomputable def bindCall
    (signature : CallSignature) (call : ExpandedCall) : BindingResult signature call := by
  classical
  exact
    if conditions : CallConditions signature call then
      .success (canonicalEnvironment signature call) ⟨rfl, conditions⟩
    else
      .error (diagnoseBindingFailure signature call)

theorem valid_binding_environment_is_unique
    (first second : ProofEnvironment)
    (firstValid : ValidProofEnvironment signature call first)
    (secondValid : ValidProofEnvironment signature call second) :
    first = second := by
  rw [firstValid.1, secondValid.1]

theorem successful_binding_is_canonical
    (environment : ProofEnvironment) (proof : ValidProofEnvironment signature call environment) :
    environment = canonicalEnvironment signature call :=
  proof.1

theorem successful_binding_has_no_duplicate_formal_bindings
    (environment : ProofEnvironment) (proof : ValidProofEnvironment signature call environment) :
    (environmentNames environment).Nodup := by
  rw [proof.1, canonical_environment_names_are_formal_names]
  exact proof.2.signatureWellFormed.1

theorem required_formals_are_all_bound_exactly_once
    (environment : ProofEnvironment) (proof : ValidProofEnvironment signature call environment) :
    environmentNames environment = signature.formalNames ∧
      (environmentNames environment).Nodup ∧
      ∀ cell ∈ environment,
        cell.slot.kind = .positional ∨ cell.slot.kind = .keywordOnly →
        cell.slot.parameter.defaultValue = none →
        ∃ assignment, cell.assignment = some assignment := by
  constructor
  · rw [proof.1, canonical_environment_names_are_formal_names]
  · constructor
    · exact successful_binding_has_no_duplicate_formal_bindings environment proof
    · intro cell member _ _
      rw [proof.1] at member
      exact proof.2.everyFormalAssigned cell member

theorem successful_binding_preserves_declared_types
    (environment : ProofEnvironment) (proof : ValidProofEnvironment signature call environment) :
    environmentWellTyped environment := by
  rw [proof.1]
  exact proof.2.assignmentsWellTyped

theorem varargs_are_exact_residual_positionals
    (signature : CallSignature) (call : ExpandedCall) (parameter : FormalParameter)
    (present : signature.varArgs = some parameter) :
    bindVarArgsCell signature call =
      [{ slot := { parameter, kind := .varArgs },
         assignment := some (.residualPositionals
           (call.positional.drop signature.positional.length)) }] := by
  simp [bindVarArgsCell, present]

theorem kwargs_are_exact_residual_keywords
    (signature : CallSignature) (call : ExpandedCall) (parameter : FormalParameter)
    (present : signature.keywordArgs = some parameter) :
    bindKeywordArgsCell signature call =
      [{ slot := { parameter, kind := .keywordArgs },
         assignment := some (.residualKeywords (residualKeywordActuals signature call)) }] := by
  simp [bindKeywordArgsCell, present]

theorem variadic_parameters_are_not_default_eligible
    (signature : CallSignature) (wellFormed : signature.WellFormed) :
    (∀ parameter ∈ signature.varArgs, parameter.defaultValue = none) ∧
      (∀ parameter ∈ signature.keywordArgs, parameter.defaultValue = none) := by
  exact ⟨wellFormed.2.2.2.1, wellFormed.2.2.2.2⟩

theorem receiver_cannot_be_rebound_by_name
    (receiver : CallValue) (items : List ActualItem)
    (first : FormalParameter) (rest : List FormalParameter)
    (signature : CallSignature)
    (positionals : signature.positional = first :: rest)
    (namedAgain : first.name ∈ namedActualNames (injectReceiver receiver items)) :
    ¬noDuplicateBinding signature (injectReceiver receiver items) := by
  intro accepted
  apply accepted first.name
  · simp [positionallyBoundNames, injectReceiver, positionals]
  · exact namedAgain

theorem bind_call_errors_exactly_when_conditions_fail
    (signature : CallSignature) (call : ExpandedCall) :
    (∃ reason, bindCall signature call = BindingResult.error reason) ↔
      ¬CallConditions signature call := by
  classical
  by_cases conditions : CallConditions signature call
  · constructor
    · rintro ⟨reason, failed⟩
      simp [bindCall, conditions] at failed
    · intro contradicted
      exact False.elim (contradicted conditions)
  · constructor
    · intro _
      exact conditions
    · intro _
      exact ⟨diagnoseBindingFailure signature call, by simp [bindCall, conditions]⟩

theorem binding_error_has_no_proof_environment
    (reason : BindingError)
    (failed : bindCall signature call = BindingResult.error reason) :
    ¬∃ environment, ValidProofEnvironment signature call environment := by
  intro alleged
  rcases alleged with ⟨environment, valid⟩
  have conditions : CallConditions signature call := valid.2
  classical
  simp [bindCall, conditions] at failed

theorem successful_binding_cannot_be_an_error
    (environment : ProofEnvironment) (proof : ValidProofEnvironment signature call environment)
    (reason : BindingError) :
    BindingResult.success environment proof ≠ BindingResult.error reason := by
  intro impossible
  cases impossible

end Maledictus
