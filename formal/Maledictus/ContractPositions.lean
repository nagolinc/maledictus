import Maledictus.Kernel

namespace Maledictus

/-!
# Contract-position context and order algebra

This is a constructive model of the finite context/order gate used for Nagini contract
primitives. It proves only the algebra below. It does not claim extraction of the Rust AST or
binding resolver and therefore contributes no Rust/frontend implementation-refinement coverage.
-/

inductive ContractPrimitive where
  | requires
  | ensures
  | exsures
  | invariant
  | assertion
  | decreases
  | permission
  | unfolding
  deriving DecidableEq

inductive ContractContext where
  | moduleScope
  | runtime
  | precondition
  | postcondition
  | loopPrefix
  | unfoldingValue
  deriving DecidableEq

def contractPrimitiveAllowed
    (primitive : ContractPrimitive) (context : ContractContext) : Bool :=
  match primitive, context with
  | .requires, .precondition => true
  | .ensures, .postcondition => true
  | .exsures, .postcondition => true
  | .invariant, .loopPrefix => true
  | .assertion, .runtime => true
  | .decreases, .precondition => true
  | .permission, .precondition => true
  | .permission, .postcondition => true
  | .permission, .loopPrefix => true
  | .unfolding, .precondition => true
  | .unfolding, .postcondition => true
  | .unfolding, .runtime => true
  | _, _ => false

inductive ContractPrefixState where
  | preconditions
  | postconditions
  | executableBody
  deriving DecidableEq

def advanceContractPrefix
    (state : ContractPrefixState) (primitive : ContractPrimitive) :
    Option ContractPrefixState :=
  match state, primitive with
  | .preconditions, .requires => some .preconditions
  | .preconditions, .ensures => some .postconditions
  | .preconditions, .exsures => some .postconditions
  | .preconditions, .decreases => some .preconditions
  | .postconditions, .ensures => some .postconditions
  | .postconditions, .exsures => some .postconditions
  | _, _ => none

def startExecutableBody (_ : ContractPrefixState) : ContractPrefixState :=
  .executableBody

theorem module_level_contracts_are_rejected (primitive : ContractPrimitive) :
    contractPrimitiveAllowed primitive .moduleScope = false := by
  cases primitive <;> rfl

theorem runtime_permissions_are_rejected :
    contractPrimitiveAllowed .permission .runtime = false := by
  rfl

theorem unfolding_values_cannot_contain_permissions :
    contractPrimitiveAllowed .permission .unfoldingValue = false := by
  rfl

theorem invariant_requires_loop_prefix :
    contractPrimitiveAllowed .invariant .loopPrefix = true /\
      contractPrimitiveAllowed .invariant .runtime = false := by
  constructor <;> rfl

theorem requires_after_postcondition_is_rejected :
    advanceContractPrefix .postconditions .requires = none := by
  rfl

theorem requires_after_executable_body_is_rejected :
    advanceContractPrefix .executableBody .requires = none := by
  rfl

theorem ordered_requires_then_ensures_is_accepted :
    advanceContractPrefix .preconditions .requires = some .preconditions /\
      advanceContractPrefix .preconditions .ensures = some .postconditions := by
  constructor <;> rfl

theorem nested_assertion_has_no_specification_context :
    contractPrimitiveAllowed .assertion .precondition = false /\
      contractPrimitiveAllowed .assertion .postcondition = false := by
  constructor <;> rfl

inductive DeclaredResultType where
  | none
  | bool
  | int
  | string
  | nominal (name : String)
  deriving DecidableEq

inductive ResultContractForm where
  | noResult
  | result
  | typedResult (declared : DeclaredResultType)
  | resultT (declared : DeclaredResultType)
  deriving DecidableEq

inductive ContractWellformednessFailure where
  | invalidResult
  | invalidResultType
  | incorrectDeclaredType
  | invalidPredicate
  deriving DecidableEq

def validateResultContract
    (functionResult : DeclaredResultType) (contract : ResultContractForm) :
    Option ContractWellformednessFailure :=
  match functionResult, contract with
  | .none, .result => some .invalidResult
  | .none, .typedResult _ => some .invalidResult
  | expected, .typedResult actual =>
      if expected = actual then none else some .invalidResultType
  | expected, .resultT actual =>
      if expected = actual then none else some .incorrectDeclaredType
  | _, _ => none

structure PredicateDeclaration where
  returnsBool : Bool
  hasSingleReturnExpression : Bool
  callsKnownImpureFunction : Bool
  deriving DecidableEq

def validatePredicateDeclaration
    (declaration : PredicateDeclaration) : Option ContractWellformednessFailure :=
  if declaration.returnsBool && declaration.hasSingleReturnExpression &&
      !declaration.callsKnownImpureFunction then
    none
  else
    some .invalidPredicate

theorem none_return_cannot_expose_result :
    validateResultContract .none .result = some .invalidResult := by
  rfl

theorem none_return_cannot_expose_typed_result (declared : DeclaredResultType) :
    validateResultContract .none (.typedResult declared) = some .invalidResult := by
  rfl

theorem matching_typed_result_is_wellformed
    (declared : DeclaredResultType) (nonvoid : declared ≠ .none) :
    validateResultContract declared (.typedResult declared) = none := by
  cases declared <;> simp_all [validateResultContract]

theorem mismatching_typed_result_is_rejected
    (expected actual : DeclaredResultType) (nonvoid : expected ≠ .none)
    (different : expected ≠ actual) :
    validateResultContract expected (.typedResult actual) = some .invalidResultType := by
  cases expected <;> cases actual <;> simp_all [validateResultContract]

theorem mismatching_resultT_is_rejected
    (expected actual : DeclaredResultType) (different : expected ≠ actual) :
    validateResultContract expected (.resultT actual) = some .incorrectDeclaredType := by
  simp [validateResultContract, different]

theorem valid_predicate_declaration_is_accepted :
    validatePredicateDeclaration ⟨true, true, false⟩ = none := by
  rfl

theorem non_boolean_predicate_is_rejected
    (singleReturn callsImpure : Bool) :
    validatePredicateDeclaration ⟨false, singleReturn, callsImpure⟩ =
      some .invalidPredicate := by
  cases singleReturn <;> cases callsImpure <;> rfl

theorem multi_statement_predicate_is_rejected
    (returnsBool callsImpure : Bool) :
    validatePredicateDeclaration ⟨returnsBool, false, callsImpure⟩ =
      some .invalidPredicate := by
  cases returnsBool <;> cases callsImpure <;> rfl

theorem predicate_calling_known_impure_function_is_rejected
    (returnsBool singleReturn : Bool) :
    validatePredicateDeclaration ⟨returnsBool, singleReturn, true⟩ =
      some .invalidPredicate := by
  cases returnsBool <;> cases singleReturn <;> rfl

inductive DeclarationBoundaryFailure where
  | decoratorsIncompatible
  | overridingInlineMethod
  | contractInInlineMethod
  | inlineConstructorUnsupported
  deriving DecidableEq

structure FunctionDeclarationBoundary where
  isInline : Bool
  isPure : Bool
  isPredicate : Bool
  isOpaque : Bool
  isConstructor : Bool
  doesOverrideMethod : Bool
  isInheritedMethodInline : Bool
  containsModularContract : Bool
  deriving DecidableEq

def validateFunctionDeclarationBoundary
    (declaration : FunctionDeclarationBoundary) : Option DeclarationBoundaryFailure :=
  if declaration.isInline && (declaration.isPure || declaration.isPredicate) then
    some .decoratorsIncompatible
  else if declaration.isOpaque && !declaration.isPure then
    some .decoratorsIncompatible
  else if declaration.isInline && declaration.isConstructor then
    some .inlineConstructorUnsupported
  else if declaration.doesOverrideMethod &&
      (declaration.isInline || declaration.isInheritedMethodInline) then
    some .overridingInlineMethod
  else if declaration.isInline && declaration.containsModularContract then
    some .contractInInlineMethod
  else
    none

theorem inline_pure_is_incompatible
    (predicateValue opaqueValue constructorValue overrides inherited contract : Bool) :
    validateFunctionDeclarationBoundary
      ⟨true, true, predicateValue, opaqueValue, constructorValue, overrides, inherited, contract⟩ =
      some .decoratorsIncompatible := by
  rfl

theorem opaque_requires_pure
    (inlineValue predicateValue constructorValue overrides inherited contract : Bool) :
    validateFunctionDeclarationBoundary
      ⟨inlineValue, false, predicateValue, true, constructorValue, overrides, inherited, contract⟩ =
      some .decoratorsIncompatible := by
  cases inlineValue <;> cases predicateValue <;> rfl

theorem inline_constructor_is_rejected
    (overrides inherited contract : Bool) :
    validateFunctionDeclarationBoundary
      ⟨true, false, false, false, true, overrides, inherited, contract⟩ =
      some .inlineConstructorUnsupported := by
  rfl

theorem overriding_an_inline_boundary_is_rejected
    (currentInline inheritedInline : Bool)
    (boundary : currentInline = true ∨ inheritedInline = true) :
    validateFunctionDeclarationBoundary
      ⟨currentInline, false, false, false, false, true, inheritedInline, false⟩ =
      some .overridingInlineMethod := by
  cases currentInline <;> cases inheritedInline <;> simp_all [validateFunctionDeclarationBoundary]

theorem inline_contract_is_rejected :
    validateFunctionDeclarationBoundary
      ⟨true, false, false, false, false, false, false, true⟩ =
      some .contractInInlineMethod := by
  rfl

theorem plain_inline_and_pure_opaque_are_wellformed :
    validateFunctionDeclarationBoundary
        ⟨true, false, false, false, false, false, false, false⟩ = none /\
      validateFunctionDeclarationBoundary
        ⟨false, true, false, true, false, false, false, true⟩ = none := by
  constructor <;> rfl

inductive DeclarationScope where
  | moduleScope
  | classScope
  | functionScope
  deriving DecidableEq

inductive SourceDeclarationKind where
  | importDeclaration
  | canonicalTypeAlias
  | ordinaryAssignment
  deriving DecidableEq

inductive LocalDeclarationFailure where
  | localImport
  | localTypeAlias
  deriving DecidableEq

def validateDeclarationScope
    (scope : DeclarationScope) (kind : SourceDeclarationKind) :
    Option LocalDeclarationFailure :=
  match scope, kind with
  | .moduleScope, _ => none
  | .classScope, .importDeclaration => some .localImport
  | .functionScope, .importDeclaration => some .localImport
  | .classScope, .canonicalTypeAlias => some .localTypeAlias
  | .functionScope, .canonicalTypeAlias => some .localTypeAlias
  | _, .ordinaryAssignment => none

theorem imports_are_module_only (scope : DeclarationScope)
    (notModule : scope ≠ .moduleScope) :
    validateDeclarationScope scope .importDeclaration = some .localImport := by
  cases scope <;> simp_all [validateDeclarationScope]

theorem canonical_type_aliases_are_module_only (scope : DeclarationScope)
    (notModule : scope ≠ .moduleScope) :
    validateDeclarationScope scope .canonicalTypeAlias = some .localTypeAlias := by
  cases scope <;> simp_all [validateDeclarationScope]

theorem module_declarations_and_ordinary_assignments_remain_valid
    (kind : SourceDeclarationKind) (scope : DeclarationScope) :
    validateDeclarationScope .moduleScope kind = none /\
      validateDeclarationScope scope .ordinaryAssignment = none := by
  cases kind <;> cases scope <;> constructor <;> rfl

inductive PureDeclarationFailure where
  | resultTypeNone
  | throwsException
  | returnMissing
  | deadCode
  deriving DecidableEq

structure PureFunctionShape where
  resultTypeIsNone : Bool
  declaresOrRaisesException : Bool
  hasValueReturn : Bool
  containsDeadCode : Bool
  deriving DecidableEq

def validatePureFunctionShape
    (shape : PureFunctionShape) : Option PureDeclarationFailure :=
  if shape.resultTypeIsNone then
    some .resultTypeNone
  else if shape.declaresOrRaisesException then
    some .throwsException
  else if !shape.hasValueReturn then
    some .returnMissing
  else if shape.containsDeadCode then
    some .deadCode
  else
    none

theorem pure_none_result_is_rejected (throws hasReturn deadCode : Bool) :
    validatePureFunctionShape ⟨true, throws, hasReturn, deadCode⟩ =
      some .resultTypeNone := by
  rfl

theorem pure_exception_channel_is_rejected (hasReturn deadCode : Bool) :
    validatePureFunctionShape ⟨false, true, hasReturn, deadCode⟩ =
      some .throwsException := by
  rfl

theorem pure_value_return_is_required (deadCode : Bool) :
    validatePureFunctionShape ⟨false, false, false, deadCode⟩ =
      some .returnMissing := by
  rfl

theorem pure_dead_code_is_rejected :
    validatePureFunctionShape ⟨false, false, true, true⟩ = some .deadCode := by
  rfl

theorem total_reachable_pure_shape_is_wellformed :
    validatePureFunctionShape ⟨false, false, true, false⟩ = none := by
  rfl

end Maledictus
