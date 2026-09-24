import Maledictus.HeapCallable

namespace Maledictus

/-!
# Executable guarded heap control flow

This file is the executable IR semantics for the v42-v51 statement and conditional subset.  Unlike the older
premise-level trace records in `HeapCallable`, these definitions construct branch entries, execute
both branch blocks recursively, preserve returned and halted paths without re-executing them,
apply typed source effects to the current state, retain every constructed path, and instantiate
one bound postcondition list on every actual normal return.

Python-AST-to-IR lowering and source-summary correctness remain frontend proof obligations.  Once
an `ExecutableHeapFunction` and its typed effects have been supplied, however, no Boolean field can
vouch for branch execution, input/output matching, continuation consumption, or postcondition
completeness.  Those properties follow from the recursive functions below.
-/

inductive ExecutableHeapPathStatus where
  | normal
  | returned (value : Term)
  | halted (failedObligation : Term)

structure ExecutableHeapPath where
  guard : Term
  state : HeapFunctionState
  status : ExecutableHeapPathStatus

def executableBindLocal
    (environment : HeapStatementEnvironment) (binding : HeapStatementLocal) :
    HeapStatementEnvironment :=
  binding :: environment.filter (fun prior => prior.name != binding.name)

def executableTermsAreBoolean (terms : List Term) : Bool :=
  terms.all (fun term => inferSort term == some .bool)

def executableReferenceLocals (environment : HeapStatementEnvironment) : List Term :=
  environment.filterMap (fun binding =>
    if heapStatementLocalTypeSort binding.valueType == .reference
    then some binding.value else none)

/-!
## Source-ordered builtin type-object aliases (v51)

Python evaluates `Alias = int` as an ordinary immutable module binding to the canonical builtin
type object.  The executable prefix below keeps all names already bound by source execution,
including imports and declarations that do not have a scalar value in `bindings`.  Consequently a
shadowing prefix can never be mistaken for the builtin merely because the shadowing value is
outside this IR fragment.
-/

inductive ExecutableBuiltinTypeObject where
  | boolType
  | intType
  | objectType
  deriving DecidableEq

def executableBuiltinTypeSourceName : ExecutableBuiltinTypeObject -> String
  | .boolType => "bool"
  | .intType => "int"
  | .objectType => "object"

def executableBuiltinTypeTerm : ExecutableBuiltinTypeObject -> Term
  | .boolType => .classLiteral "builtins::bool"
  | .intType => .classLiteral "builtins::int"
  | .objectType => .classLiteral "builtins::object"

structure ExecutableModulePrefix where
  bindings : ModuleEnvironment
  boundNames : List String

def executableModulePrefixValid (moduleState : ExecutableModulePrefix) : Bool :=
  moduleState.boundNames.eraseDups.length == moduleState.boundNames.length &&
    moduleState.bindings.all (fun binding => moduleState.boundNames.contains binding.1)

structure ExecutableBuiltinTypeAliasRequest where
  targetName : String
  builtinType : ExecutableBuiltinTypeObject

def executeExecutableBuiltinTypeAlias
    (request : ExecutableBuiltinTypeAliasRequest) (moduleState : ExecutableModulePrefix) :
    Option ExecutableModulePrefix :=
  let sourceName := executableBuiltinTypeSourceName request.builtinType
  let value := executableBuiltinTypeTerm request.builtinType
  if !executableModulePrefixValid moduleState || request.targetName.isEmpty ||
      moduleState.boundNames.contains request.targetName || moduleState.boundNames.contains sourceName then
    none
  else some {
    bindings := (request.targetName, value) :: moduleState.bindings
    boundNames := request.targetName :: moduleState.boundNames
  }

theorem executable_builtin_type_term_has_class_sort
    (builtinType : ExecutableBuiltinTypeObject) :
    inferSort (executableBuiltinTypeTerm builtinType) = some .class := by
  cases builtinType <;> rfl

theorem executable_builtin_type_alias_binds_exact_class_literal
    (request : ExecutableBuiltinTypeAliasRequest)
    (moduleState result : ExecutableModulePrefix)
    (executed : executeExecutableBuiltinTypeAlias request moduleState = some result) :
    moduleLookup result.bindings request.targetName =
      some (executableBuiltinTypeTerm request.builtinType) := by
  simp only [executeExecutableBuiltinTypeAlias] at executed
  split at executed <;> try contradiction
  next inserted =>
    injection executed with resultEq
    subst result
    exact inserted_module_binding_is_visible moduleState.bindings request.targetName
      (executableBuiltinTypeTerm request.builtinType)

theorem executable_builtin_type_alias_preserves_prior_binding
    (request : ExecutableBuiltinTypeAliasRequest)
    (moduleState result : ExecutableModulePrefix)
    (other : String)
    (different : other ≠ request.targetName)
    (executed : executeExecutableBuiltinTypeAlias request moduleState = some result) :
    moduleLookup result.bindings other = moduleLookup moduleState.bindings other := by
  simp only [executeExecutableBuiltinTypeAlias] at executed
  split at executed <;> try contradiction
  next inserted =>
    injection executed with resultEq
    subst result
    exact inserted_module_binding_preserves_other_names moduleState.bindings request.targetName other
      (executableBuiltinTypeTerm request.builtinType) different

theorem executable_builtin_type_alias_records_target_name
    (request : ExecutableBuiltinTypeAliasRequest)
    (moduleState result : ExecutableModulePrefix)
    (executed : executeExecutableBuiltinTypeAlias request moduleState = some result) :
    request.targetName ∈ result.boundNames := by
  simp only [executeExecutableBuiltinTypeAlias] at executed
  split at executed <;> try contradiction
  next inserted =>
    injection executed with resultEq
    subst result
    simp

theorem executable_builtin_type_alias_refuses_shadowed_source
    (request : ExecutableBuiltinTypeAliasRequest)
    (moduleState : ExecutableModulePrefix)
    (shadowed : executableBuiltinTypeSourceName request.builtinType ∈ moduleState.boundNames) :
    executeExecutableBuiltinTypeAlias request moduleState = none := by
  simp [executeExecutableBuiltinTypeAlias, shadowed]

structure ExecutableSourceNominalType where
  canonicalClass : String
  optional : Bool

def executableSourceNominalTypeValid (type : ExecutableSourceNominalType) : Bool :=
  !type.canonicalClass.isEmpty

def executableSourceLocalType (type : ExecutableSourceNominalType) : HeapStatementLocalType :=
  .nominal {
    canonicalClass := type.canonicalClass
    optional := type.optional
    sourceOwned := true
    checkedExternalContractHash := ""
  }

def executableOpaqueObjectParameter
    (name : String) (value : Term) : Option HeapStatementLocal :=
  if name.isEmpty || inferSort value != some .reference then none
  else some {
    name
    value
    valueType := .opaqueObject
    exactRuntimeClassProved := false
    sourceConstructedProved := false
  }

def executableSourceReceiverTypeValid : HeapStatementLocalType → Bool
  | .nominal nominal =>
      nominal.sourceOwned && heapStatementNominalTypeValidated nominal && !nominal.optional
  | _ => false

def executableLookupLocal
    (environment : HeapStatementEnvironment) (name : String) : Option HeapStatementLocal :=
  match environment with
  | [] => none
  | binding :: rest =>
      if binding.name == name then some binding else executableLookupLocal rest name

structure ExecutableSourceFieldRecord where
  name : String
  type : HeapStatementLocalType

inductive ExecutablePureScalarExpr where
  | boolLiteral (value : Bool)
  | intLiteral (value : Int)
  | receiverField (fieldName : String)
  | methodResult
  | not (value : ExecutablePureScalarExpr)
  | equal (left right : ExecutablePureScalarExpr)
  | less (left right : ExecutablePureScalarExpr)
  | add (left right : ExecutablePureScalarExpr)
  deriving DecidableEq

inductive ExecutablePureMethodResultRule where
  /-- The frontend selected this verified implementation and extracted its single return. -/
  | selectedBody (body : ExecutablePureScalarExpr)
  /-- The selected verified implementation is represented modularly by its result contract. -/
  | contractResult (sort : ValueSort)

structure ExecutablePureMethodRecord where
  /-- Records are source-extracted only after the frontend has selected and verified the
  effective implementation (locally or from a completed provider). -/
  name : String
  resultRule : ExecutablePureMethodResultRule
  preconditions : List ExecutablePureScalarExpr
  postconditions : List ExecutablePureScalarExpr

structure ExecutableSourceClassRecord where
  /-- A record exists only for a frontend-proved complete source class with the default metaclass,
  no `__instancecheck__`, and ordinary attribute storage. -/
  name : String
  directBase : Option String
  fields : List ExecutableSourceFieldRecord
  pureMethods : List ExecutablePureMethodRecord

structure ExecutableCompleteSourceClassCatalog where
  classes : List ExecutableSourceClassRecord

def executableCatalogLookupClass
    (catalog : ExecutableCompleteSourceClassCatalog) (className : String) :
    Option ExecutableSourceClassRecord :=
  catalog.classes.find? (fun candidate => candidate.name == className)

def executableCatalogFieldTypeValid : HeapStatementLocalType → Bool
  | .scalar sort => isHeapFieldSort sort
  | .nominal nominal => heapStatementNominalTypeValidated nominal
  | .nullOnly | .opaqueObject => false

def executablePureScalarExprContainsResult : ExecutablePureScalarExpr → Bool
  | .methodResult => true
  | .not value => executablePureScalarExprContainsResult value
  | .equal left right | .less left right | .add left right =>
      executablePureScalarExprContainsResult left ||
        executablePureScalarExprContainsResult right
  | _ => false

def executablePureMethodResultRuleValid : ExecutablePureMethodResultRule → Bool
  | .selectedBody body => !executablePureScalarExprContainsResult body
  | .contractResult sort => heapIfExpScalarSortSupported sort

def executablePureMethodRecordLocallyValid (method : ExecutablePureMethodRecord) : Bool :=
  !method.name.isEmpty && executablePureMethodResultRuleValid method.resultRule &&
    method.preconditions.all (fun expression =>
      !executablePureScalarExprContainsResult expression)

def executableSourceClassRecordLocallyValid (record : ExecutableSourceClassRecord) : Bool :=
  !record.name.isEmpty && record.name != "object" &&
    record.fields.all (fun field =>
      !field.name.isEmpty && executableCatalogFieldTypeValid field.type) &&
    (record.fields.map (fun field => field.name)).eraseDups.length == record.fields.length &&
    record.pureMethods.all executablePureMethodRecordLocallyValid &&
    (record.pureMethods.map (fun method => method.name)).eraseDups.length ==
      record.pureMethods.length

def executableCatalogClassChain
    (catalog : ExecutableCompleteSourceClassCatalog) (className : String) :
    Nat → List String → Option (List String)
  | 0, _ => none
  | fuel + 1, visited =>
      if className == "object" then some ["object"]
      else if visited.any (fun prior => prior == className) then none
      else
        match executableCatalogLookupClass catalog className with
        | none => none
        | some record =>
            match record.directBase with
            | none => some [className, "object"]
            | some base =>
                match executableCatalogClassChain catalog base fuel (className :: visited) with
                | none => none
                | some rest => some (className :: rest)

def executableSourceClassCatalogValid
    (catalog : ExecutableCompleteSourceClassCatalog) : Bool :=
  let names := catalog.classes.map (fun record => record.name)
  names.eraseDups.length == names.length &&
    catalog.classes.all executableSourceClassRecordLocallyValid &&
    catalog.classes.all (fun record =>
      (executableCatalogClassChain catalog record.name
        (catalog.classes.length + 1) []).isSome)

def executableCatalogHasSourceSafeClass
    (catalog : ExecutableCompleteSourceClassCatalog) (className : String) : Bool :=
  executableSourceClassCatalogValid catalog &&
    (executableCatalogLookupClass catalog className).isSome

def executableCatalogProvesSubtype
    (catalog : ExecutableCompleteSourceClassCatalog) (actual expected : String) : Bool :=
  if !executableSourceClassCatalogValid catalog then false
  else
    match executableCatalogClassChain catalog actual (catalog.classes.length + 1) [] with
    | none => false
    | some chain => chain.any (fun className => className == expected)

def executableCatalogLookupFieldUnchecked
    (catalog : ExecutableCompleteSourceClassCatalog) (className fieldName : String) :
    Nat → Option ExecutableSourceFieldRecord
  | 0 => none
  | fuel + 1 =>
      match executableCatalogLookupClass catalog className with
      | none => none
      | some record =>
          match record.fields.find? (fun field => field.name == fieldName) with
          | some field => some field
          | none =>
              match record.directBase with
              | none => none
              | some base => executableCatalogLookupFieldUnchecked catalog base fieldName fuel

def executableCatalogLookupField
    (catalog : ExecutableCompleteSourceClassCatalog) (className fieldName : String) :
    Option ExecutableSourceFieldRecord :=
  if !executableSourceClassCatalogValid catalog then none
  else executableCatalogLookupFieldUnchecked catalog className fieldName
    (catalog.classes.length + 1)

def executableCatalogLookupPureMethodUnchecked
    (catalog : ExecutableCompleteSourceClassCatalog) (className methodName : String) :
    Nat → Option ExecutablePureMethodRecord
  | 0 => none
  | fuel + 1 =>
      match executableCatalogLookupClass catalog className with
      | none => none
      | some record =>
          match record.pureMethods.find? (fun method => method.name == methodName) with
          | some method => some method
          | none =>
              match record.directBase with
              | none => none
              | some base =>
                  executableCatalogLookupPureMethodUnchecked catalog base methodName fuel

def executableCatalogLookupPureMethod
    (catalog : ExecutableCompleteSourceClassCatalog) (className methodName : String) :
    Option ExecutablePureMethodRecord :=
  if !executableSourceClassCatalogValid catalog then none
  else executableCatalogLookupPureMethodUnchecked catalog className methodName
    (catalog.classes.length + 1)

structure ExecutableResolvedPureMethod where
  receiverClass : String
  method : ExecutablePureMethodRecord

def executableBindingExactSourceClass (binding : HeapStatementLocal) : Option String :=
  match binding.valueType with
  | .nominal nominal =>
      if (binding.exactRuntimeClassProved || binding.sourceConstructedProved) &&
          nominal.sourceOwned && heapStatementNominalTypeValidated nominal then
        some nominal.canonicalClass
      else none
  | _ => none

def executableResolvePureMethodDispatch
    (catalog : ExecutableCompleteSourceClassCatalog)
    (binding : HeapStatementLocal) (methodName : String) :
    Option ExecutableResolvedPureMethod :=
  if methodName.isEmpty || !executableSourceReceiverTypeValid binding.valueType then none
  else
    match executableBindingExactSourceClass binding with
    | some exactClass =>
        match executableCatalogLookupPureMethod catalog exactClass methodName with
        | some method => some { receiverClass := exactClass, method }
        | none => none
    | none => none

def executableInstanceOfDynamicPredicate (value : Term) (targetClass : String) : Term :=
  .and [
    .not (.equal value .nullReference),
    .classSubtype (.runtimeClass value) (.classLiteral targetClass)
  ]

def executableInstanceOfCondition
    (catalog : ExecutableCompleteSourceClassCatalog)
    (binding : HeapStatementLocal) (targetClass : String) : Term :=
  match executableBindingExactSourceClass binding with
  | some actualClass => .boolLiteral
      (executableCatalogProvesSubtype catalog actualClass targetClass)
  | none => executableInstanceOfDynamicPredicate binding.value targetClass

def executableInstanceOfTrueBinding
    (catalog : ExecutableCompleteSourceClassCatalog)
    (binding : HeapStatementLocal) (targetClass : String) : HeapStatementLocal :=
  match binding.valueType with
  | .nominal nominal =>
      if nominal.sourceOwned && heapStatementNominalTypeValidated nominal &&
          executableCatalogProvesSubtype catalog nominal.canonicalClass targetClass then
        { binding with valueType := .nominal { nominal with optional := false } }
      else { binding with
          valueType := executableSourceLocalType { canonicalClass := targetClass, optional := false }
          exactRuntimeClassProved := false
          sourceConstructedProved := false
        }
  | _ => { binding with
      valueType := executableSourceLocalType { canonicalClass := targetClass, optional := false }
      exactRuntimeClassProved := false
      sourceConstructedProved := false
    }

structure ExecutableInstanceOfRequest where
  subjectName : String
  targetClass : String
  catalog : ExecutableCompleteSourceClassCatalog

structure ExecutableInstanceOfSplit where
  condition : Term
  thenPath : ExecutableHeapPath
  elsePath : ExecutableHeapPath

def executableSplitInstanceOf
    (request : ExecutableInstanceOfRequest) (path : ExecutableHeapPath) :
    Option ExecutableInstanceOfSplit :=
  match path.status with
  | .returned _ | .halted _ => none
  | .normal =>
      if !executableCatalogHasSourceSafeClass request.catalog request.targetClass then none
      else
        match executableLookupLocal path.state.environment request.subjectName with
        | none => none
        | some binding =>
            if inferSort binding.value != some .reference then none
            else
              let condition := executableInstanceOfCondition
                request.catalog binding request.targetClass
              let narrowed := executableInstanceOfTrueBinding
                request.catalog binding request.targetClass
              some {
                condition
                thenPath := {
                  path with
                    guard := .and [path.guard, condition]
                    state := {
                      path.state with
                        environment := executableBindLocal path.state.environment narrowed
                        assumptions := path.state.assumptions ++ [condition]
                    }
                }
                elsePath := {
                  path with
                    guard := .and [path.guard, .not condition]
                    state := {
                      path.state with assumptions := path.state.assumptions ++ [.not condition]
                    }
                }
              }

def executableJoinInstanceOfPurePass
    (request : ExecutableInstanceOfRequest) (path : ExecutableHeapPath) :
    Option HeapStatementEnvironment :=
  match executableSplitInstanceOf request path with
  | none => none
  | some _ => some path.state.environment

inductive ExecutableProofDisposition where
  | proved
  | refuted (failedObligation : Term)
  | unresolved

inductive ExecutableObligationDisposition (obligations : List Term) where
  | proved
  | refuted (failedObligation : Term) (isGenerated : failedObligation ∈ obligations)
  | unresolved

abbrev ExecutableProofKernel :=
  (obligations : List Term) → ExecutableObligationDisposition obligations

def executableAllProvedKernel : ExecutableProofKernel :=
  fun _ => .proved

def executableRefuteFirstKernel : ExecutableProofKernel
  | [] => .unresolved
  | first :: rest => .refuted first (by simp)

structure ExecutablePureScalarResult where
  value : Term
  obligations : List Term

def executablePureScalarPair
    (constructor : Term → Term → Term)
    (left right : ExecutablePureScalarResult) : ExecutablePureScalarResult := {
  value := constructor left.value right.value
  obligations := left.obligations ++ right.obligations
}

def executableInstantiatePureScalarExpr
    (catalog : ExecutableCompleteSourceClassCatalog)
    (receiverClass : String) (receiver : Term) (path : ExecutableHeapPath)
    (methodResult : Option Term) :
    ExecutablePureScalarExpr → Option ExecutablePureScalarResult
  | .boolLiteral value => some { value := .boolLiteral value, obligations := [] }
  | .intLiteral value => some { value := .intLiteral value, obligations := [] }
  | .methodResult => methodResult.map (fun value => { value, obligations := [] })
  | .receiverField fieldName =>
      match executableCatalogLookupField catalog receiverClass fieldName with
      | none => none
      | some field =>
          match field.type with
          | .scalar .bool | .scalar .int =>
              some {
                value := .fieldRead path.state.heap receiver field.name
                  (heapStatementLocalTypeSort field.type)
                obligations := [
                  .permissionAtLeast path.state.mask receiver field.name 1 1
                ]
              }
          | _ => none
  | .not value =>
      match executableInstantiatePureScalarExpr
          catalog receiverClass receiver path methodResult value with
      | some result =>
          if inferSort result.value == some .bool then
            some { result with value := .not result.value }
          else none
      | none => none
  | .equal left right =>
      match executableInstantiatePureScalarExpr catalog receiverClass receiver path methodResult left,
          executableInstantiatePureScalarExpr catalog receiverClass receiver path methodResult right with
      | some leftResult, some rightResult =>
          let result := executablePureScalarPair Term.equal leftResult rightResult
          if inferSort result.value == some .bool then some result else none
      | _, _ => none
  | .less left right =>
      match executableInstantiatePureScalarExpr catalog receiverClass receiver path methodResult left,
          executableInstantiatePureScalarExpr catalog receiverClass receiver path methodResult right with
      | some leftResult, some rightResult =>
          let result := executablePureScalarPair Term.less leftResult rightResult
          if inferSort result.value == some .bool then some result else none
      | _, _ => none
  | .add left right =>
      match executableInstantiatePureScalarExpr catalog receiverClass receiver path methodResult left,
          executableInstantiatePureScalarExpr catalog receiverClass receiver path methodResult right with
      | some leftResult, some rightResult =>
          let result := executablePureScalarPair Term.add leftResult rightResult
          if inferSort result.value == some .int then some result else none
      | _, _ => none

def executableInstantiatePurePreconditions
    (catalog : ExecutableCompleteSourceClassCatalog)
    (receiverClass : String) (receiver : Term) (path : ExecutableHeapPath) :
    List ExecutablePureScalarExpr → Option (List Term)
  | [] => some []
  | precondition :: rest =>
      match executableInstantiatePureScalarExpr
          catalog receiverClass receiver path none precondition,
          executableInstantiatePurePreconditions catalog receiverClass receiver path rest with
      | some result, some remaining =>
          if inferSort result.value == some .bool then
            some (result.obligations ++ [result.value] ++ remaining)
          else none
      | _, _ => none

structure ExecutablePureMethodInvocation where
  result : Term
  obligations : List Term
  assumptions : List Term

structure ExecutableInstantiatedPurePostconditions where
  obligations : List Term
  assumptions : List Term

def executablePureContractResultName
    (runtimeClass methodName : String) (binding : HeapStatementLocal)
    (path : ExecutableHeapPath) : String :=
  "condition-result:" ++ binding.name ++ ":" ++ runtimeClass ++ "." ++ methodName ++
    ":h" ++ toString path.state.heap ++ ":m" ++ toString path.state.mask

def executableInstantiatePurePostconditions
    (catalog : ExecutableCompleteSourceClassCatalog)
    (receiverClass : String) (receiver result : Term) (path : ExecutableHeapPath) :
    List ExecutablePureScalarExpr → Option ExecutableInstantiatedPurePostconditions
  | [] => some { obligations := [], assumptions := [] }
  | postcondition :: rest =>
      match executableInstantiatePureScalarExpr catalog receiverClass receiver path
          (some result) postcondition,
          executableInstantiatePurePostconditions
            catalog receiverClass receiver result path rest with
      | some instantiated, some remaining =>
          if inferSort instantiated.value == some .bool then some {
            obligations := instantiated.obligations ++ remaining.obligations
            assumptions := [instantiated.value] ++ remaining.assumptions
          } else none
      | _, _ => none

def executableInvokePureMethodAtRuntimeClass
    (catalog : ExecutableCompleteSourceClassCatalog)
    (runtimeClass : String) (binding : HeapStatementLocal) (methodName : String)
    (path : ExecutableHeapPath) : Option ExecutablePureMethodInvocation :=
  match executableCatalogLookupPureMethod catalog runtimeClass methodName with
  | none => none
  | some method =>
      let resultAndBodyObligations : Option (Term × List Term) :=
        match method.resultRule with
        | .selectedBody body =>
            match executableInstantiatePureScalarExpr
                catalog runtimeClass binding.value path none body with
            | some instantiated =>
                match inferSort instantiated.value with
                | some sort =>
                    if heapIfExpScalarSortSupported sort then
                      some (instantiated.value, instantiated.obligations)
                    else none
                | none => none
            | none => none
        | .contractResult sort =>
            if heapIfExpScalarSortSupported sort then
              some (.variable
                (executablePureContractResultName
                  runtimeClass methodName binding path) sort, [])
            else none
      match executableInstantiatePurePreconditions catalog runtimeClass binding.value
          path method.preconditions, resultAndBodyObligations with
      | some preconditions, some (result, bodyObligations) =>
          match executableInstantiatePurePostconditions catalog runtimeClass binding.value
              result path method.postconditions with
          | some postconditions => some {
              result
              obligations := [.not (.equal binding.value .nullReference)] ++
                preconditions ++ bodyObligations ++ postconditions.obligations
              assumptions := postconditions.assumptions
            }
          | none => none
      | _, _ => none

def executableInvokePureMethod
    (catalog : ExecutableCompleteSourceClassCatalog)
    (binding : HeapStatementLocal) (methodName : String) (path : ExecutableHeapPath) :
    Option ExecutablePureMethodInvocation :=
  match binding.valueType with
  | .nominal _ =>
      match executableResolvePureMethodDispatch catalog binding methodName with
      | some resolved => executableInvokePureMethodAtRuntimeClass
          catalog resolved.receiverClass binding methodName path
      | none => none
  | _ => none

inductive ExecutableVersionTransition where
  | preserves
  | advances
  deriving DecidableEq

def executableNextVersion (version : Nat) : ExecutableVersionTransition → Nat
  | .preserves => version
  | .advances => version + 1

structure ExecutableHeapFieldLayout where
  field : String
  sort : ValueSort

def executableFieldFrameFacts
    (preHeap postHeap : Nat) (receiver : Term)
    (fields : List ExecutableHeapFieldLayout) : List Term :=
  fields.map (fun field => .equal
    (.fieldRead postHeap receiver field.field field.sort)
    (.fieldRead preHeap receiver field.field field.sort))

def executableConstructorFreshFacts
    (result : Term) (className : String) (environment : HeapStatementEnvironment) : List Term :=
  [.not (.equal result .nullReference),
    .equal (.runtimeClass result) (.classLiteral className)] ++
    (executableReferenceLocals environment).map (fun prior => .not (.equal result prior))

structure ExecutableSourceConstructorEffect where
  localName : String
  result : Term
  resultType : ExecutableSourceNominalType
  preconditionObligations : List Term
  postconditionFacts : List Term
  disposition : ExecutableProofDisposition

structure ExecutableSourceMethodEffect where
  receiver : Term
  receiverType : HeapStatementLocalType
  resultBinding : Option (String × HeapStatementLocalType)
  result : Term
  heapTransition : ExecutableVersionTransition
  maskTransition : ExecutableVersionTransition
  preconditionObligations : List Term
  postconditionFacts : List Term
  frameFacts : List Term
  disposition : ExecutableProofDisposition

structure ExecutableSourceFieldWriteEffect where
  receiver : Term
  receiverType : HeapStatementLocalType
  field : String
  fieldType : HeapStatementLocalType
  value : Term
  valueType : HeapStatementLocalType
  nominalEvidence : GuardedFieldWriteNominalEvidence
  framedFields : List ExecutableHeapFieldLayout
  permissionDisposition : ExecutableProofDisposition

inductive ExecutableHeapEffect where
  | constructorLocal (effect : ExecutableSourceConstructorEffect)
  | sourceMethod (effect : ExecutableSourceMethodEffect)
  | sourceFieldWrite (effect : ExecutableSourceFieldWriteEffect)

def executableHaltPath
    (path : ExecutableHeapPath) (obligations : List Term) (failed : Term) :
    ExecutableHeapPath := {
  path with
    state := { path.state with obligations := path.state.obligations ++ obligations }
    status := .halted failed
}

def executableSourceMethodObligations (effect : ExecutableSourceMethodEffect) : List Term :=
  [.not (.equal effect.receiver .nullReference)] ++ effect.preconditionObligations

def executableMethodResultLocal
    (effect : ExecutableSourceMethodEffect) : Option HeapStatementLocal :=
  match effect.resultBinding with
  | none => none
  | some (name, type) => some {
      name
      value := effect.result
      valueType := type
      exactRuntimeClassProved := false
      sourceConstructedProved := false
    }

def executableMethodResultWellTyped (effect : ExecutableSourceMethodEffect) : Bool :=
  match effect.resultBinding with
  | none => inferSort effect.result == some .unit
  | some (_, type) => inferSort effect.result == some (heapStatementLocalTypeSort type)

def executeExecutableHeapEffect
    (effect : ExecutableHeapEffect) (path : ExecutableHeapPath) :
    Option ExecutableHeapPath :=
  match path.status with
  | .returned _ | .halted _ => some path
  | .normal =>
      match effect with
      | .constructorLocal constructor =>
          if inferSort constructor.result != some .reference ||
              !executableSourceNominalTypeValid constructor.resultType ||
              constructor.resultType.optional ||
              !executableTermsAreBoolean constructor.preconditionObligations ||
              !executableTermsAreBoolean constructor.postconditionFacts then none
          else
            match constructor.disposition with
            | .unresolved => none
            | .refuted failed => some (executableHaltPath path
                constructor.preconditionObligations failed)
            | .proved =>
                let binding : HeapStatementLocal := {
                  name := constructor.localName
                  value := constructor.result
                  valueType := executableSourceLocalType constructor.resultType
                  exactRuntimeClassProved := true
                  sourceConstructedProved := true
                }
                some { path with state := {
                  path.state with
                    environment := executableBindLocal path.state.environment binding
                    assumptions := path.state.assumptions ++
                      executableConstructorFreshFacts constructor.result
                        constructor.resultType.canonicalClass path.state.environment ++
                      constructor.postconditionFacts
                    obligations := path.state.obligations ++ constructor.preconditionObligations
                }}
      | .sourceMethod method =>
          let obligations := executableSourceMethodObligations method
          if inferSort method.receiver != some .reference ||
              !executableSourceReceiverTypeValid method.receiverType ||
              !executableMethodResultWellTyped method ||
              !executableTermsAreBoolean obligations ||
              !executableTermsAreBoolean method.postconditionFacts ||
              !executableTermsAreBoolean method.frameFacts then none
          else
            match method.disposition with
            | .unresolved => none
            | .refuted failed => some (executableHaltPath path obligations failed)
            | .proved =>
                let environment := match executableMethodResultLocal method with
                  | none => path.state.environment
                  | some binding => executableBindLocal path.state.environment binding
                some { path with state := {
                  environment
                  heap := executableNextVersion path.state.heap method.heapTransition
                  mask := executableNextVersion path.state.mask method.maskTransition
                  assumptions := path.state.assumptions ++ method.frameFacts ++
                    method.postconditionFacts
                  obligations := path.state.obligations ++ obligations
                }}
      | .sourceFieldWrite write =>
          if inferSort write.receiver != some .reference ||
              !executableSourceReceiverTypeValid write.receiverType || write.field.isEmpty ||
              inferSort write.value != some (heapStatementLocalTypeSort write.valueType) ||
              !guardedFieldWriteTypesCompatible write.fieldType write.valueType
                write.nominalEvidence then none
          else
            let permission : Term := .permissionAtLeast
              path.state.mask write.receiver write.field 1 1
            match write.permissionDisposition with
            | .unresolved => none
            | .refuted failed => some (executableHaltPath path [permission] failed)
            | .proved =>
                let postHeap := path.state.heap + 1
                let writeFact : Term := .equal
                  (.fieldRead postHeap write.receiver write.field
                    (heapStatementLocalTypeSort write.fieldType))
                  write.value
                some { path with state := {
                  path.state with
                    heap := postHeap
                    assumptions := path.state.assumptions ++ [writeFact] ++
                      executableFieldFrameFacts path.state.heap postHeap write.receiver
                        write.framedFields
                    obligations := path.state.obligations ++ [permission]
                }}

mutual

  def executableReadFreeScalarTerm : Term → Bool
    | .boolLiteral _ | .intLiteral _ => true
    | .variable _ .bool | .variable _ .int => true
    | .not value | .negate value => executableReadFreeScalarTerm value
    | .and values | .or values => executableReadFreeScalarTerms values
    | .implies left right | .equal left right | .less left right | .lessEqual left right |
        .greater left right | .greaterEqual left right | .add left right | .subtract left right |
        .multiply left right =>
        executableReadFreeScalarTerm left && executableReadFreeScalarTerm right
    | .floorDivideByPositive value _ => executableReadFreeScalarTerm value
    | .ite condition thenValue elseValue =>
        executableReadFreeScalarTerm condition &&
          executableReadFreeScalarTerm thenValue && executableReadFreeScalarTerm elseValue
    | _ => false

  def executableReadFreeScalarTerms : List Term → Bool
    | [] => true
    | value :: rest =>
        executableReadFreeScalarTerm value && executableReadFreeScalarTerms rest

end

def executableScalarIfExpBranchAtSort (value : Term) (joinedSort : ValueSort) : Term :=
  if joinedSort == .int && inferSort value == some .bool then
    promoteHeapConditionalBoolToInt value
  else value

structure ExecutableScalarIfExpResult where
  value : Term
  sort : ValueSort

def executeScalarIfExp
    (condition thenValue elseValue : Term) : Option ExecutableScalarIfExpResult :=
  if inferSort condition != some .bool ||
      !executableReadFreeScalarTerm condition ||
      !executableReadFreeScalarTerm thenValue ||
      !executableReadFreeScalarTerm elseValue then none
  else
    match inferSort thenValue, inferSort elseValue with
    | some thenSort, some elseSort =>
        let joinedSort :=
          if thenSort == .int || elseSort == .int then .int else .bool
        if !heapIfExpScalarSortSupported thenSort ||
            !heapIfExpScalarSortSupported elseSort then none
        else some {
          value := .ite condition
            (executableScalarIfExpBranchAtSort thenValue joinedSort)
            (executableScalarIfExpBranchAtSort elseValue joinedSort)
          sort := joinedSort
        }
    | _, _ => none

def executableReadableSourceFieldType : HeapStatementLocalType → Bool
  | .scalar sort => isHeapFieldSort sort
  | .nominal nominal => heapStatementNominalTypeValidated nominal
  | .nullOnly | .opaqueObject => false

structure ExecutableRawFieldRead where
  receiverName : String
  fieldName : String
  catalog : ExecutableCompleteSourceClassCatalog
  permissionDisposition : ExecutableProofDisposition

structure ExecutableResolvedRawFieldRead where
  receiver : Term
  field : ExecutableSourceFieldRecord

def executableResolveRawFieldRead
    (read : ExecutableRawFieldRead) (path : ExecutableHeapPath) :
    Option ExecutableResolvedRawFieldRead :=
  match executableLookupLocal path.state.environment read.receiverName with
  | none => none
  | some binding =>
      if inferSort binding.value != some .reference ||
          !executableSourceReceiverTypeValid binding.valueType || read.fieldName.isEmpty then none
      else
        match binding.valueType with
        | .nominal nominal =>
            match executableCatalogLookupField read.catalog nominal.canonicalClass read.fieldName with
            | none => none
            | some field => some { receiver := binding.value, field }
        | _ => none

def executableRawFieldReadTerm
    (read : ExecutableResolvedRawFieldRead) (path : ExecutableHeapPath) : Term :=
  .fieldRead path.state.heap read.receiver read.field.name
    (heapStatementLocalTypeSort read.field.type)

def executableRawFieldReadObligations
    (read : ExecutableResolvedRawFieldRead) (path : ExecutableHeapPath) : List Term :=
  [.not (.equal read.receiver .nullReference),
    .permissionAtLeast path.state.mask read.receiver read.field.name 1 1]

def executeExecutableRawFieldReturn
    (request : ExecutableRawFieldRead) (path : ExecutableHeapPath) : Option ExecutableHeapPath :=
  match path.status with
  | .returned _ | .halted _ => some path
  | .normal =>
      match executableResolveRawFieldRead request path with
      | none => none
      | some read =>
          let value := executableRawFieldReadTerm read path
          let obligations := executableRawFieldReadObligations read path
          if !executableReadableSourceFieldType read.field.type ||
              inferSort value != some (heapStatementLocalTypeSort read.field.type) ||
              !executableTermsAreBoolean obligations then none
          else
            match request.permissionDisposition with
            | .unresolved => none
            | .refuted failed => some (executableHaltPath path obligations failed)
            | .proved => some { path with
                state := { path.state with
                  obligations := path.state.obligations ++ obligations
                }
                status := .returned value
              }

inductive ExecutableScalarComparisonOperator where
  | equal
  | notEqual
  | less
  | lessEqual
  | greater
  | greaterEqual

inductive ExecutablePureMethodAtom where
  | boolean (receiverName methodName : String)
  | compareCallLeft (receiverName methodName : String)
      (operator : ExecutableScalarComparisonOperator) (peer : Term)
  | compareCallRight (peer : Term) (operator : ExecutableScalarComparisonOperator)
      (receiverName methodName : String)

def executablePureMethodAtomReceiver : ExecutablePureMethodAtom → String
  | .boolean receiverName _ | .compareCallLeft receiverName _ _ _ |
      .compareCallRight _ _ receiverName _ => receiverName

def executablePureMethodAtomMethod : ExecutablePureMethodAtom → String
  | .boolean _ methodName | .compareCallLeft _ methodName _ _ |
      .compareCallRight _ _ _ methodName => methodName

inductive ExecutableHeapCondition where
  | instanceOf (request : ExecutableInstanceOfRequest)
  | pureMethod (atom : ExecutablePureMethodAtom)
  | not (condition : ExecutableHeapCondition)
  | and (left right : ExecutableHeapCondition)
  | or (left right : ExecutableHeapCondition)

structure ExecutableConditionFlow where
  truePaths : List ExecutableHeapPath
  falsePaths : List ExecutableHeapPath
  haltedPaths : List ExecutableHeapPath
  unmodeledPaths : List ExecutableHeapPath

def executablePathAssumptionTerm (path : ExecutableHeapPath) : Term :=
  .and (path.state.assumptions ++ [path.guard])

def executablePathInfeasibilityObligation (path : ExecutableHeapPath) : Term :=
  .implies (executablePathAssumptionTerm path) (.boolLiteral false)

inductive ExecutablePathFeasibility where
  | feasible
  | infeasible
  | unmodeled
  deriving DecidableEq

def executableClassifyPathFeasibility
    (proofKernel : ExecutableProofKernel) (path : ExecutableHeapPath) :
    ExecutablePathFeasibility :=
  let obligation := executablePathInfeasibilityObligation path
  match proofKernel [obligation] with
  | .proved => .infeasible
  | .refuted _ _ => .feasible
  | .unresolved => .unmodeled

def executableClassifyConditionPaths
    (proofKernel : ExecutableProofKernel) :
    List ExecutableHeapPath → List ExecutableHeapPath × List ExecutableHeapPath
  | [] => ([], [])
  | path :: rest =>
      let (feasible, unmodeled) := executableClassifyConditionPaths proofKernel rest
      match executableClassifyPathFeasibility proofKernel path with
      | .feasible => (path :: feasible, unmodeled)
      | .infeasible => (feasible, unmodeled)
      | .unmodeled => (feasible, path :: unmodeled)

def executableConditionFlowFromSplit
    (proofKernel : ExecutableProofKernel)
    (thenPath elsePath : ExecutableHeapPath) : ExecutableConditionFlow :=
  let (truePaths, trueUnmodeled) :=
    executableClassifyConditionPaths proofKernel [thenPath]
  let (falsePaths, falseUnmodeled) :=
    executableClassifyConditionPaths proofKernel [elsePath]
  {
    truePaths
    falsePaths
    haltedPaths := []
    unmodeledPaths := trueUnmodeled ++ falseUnmodeled
  }

def executableUnmodeledConditionFlow
    (path : ExecutableHeapPath) : ExecutableConditionFlow := {
  truePaths := []
  falsePaths := []
  haltedPaths := []
  unmodeledPaths := [path]
}

def executableEmptyConditionFlow : ExecutableConditionFlow := {
  truePaths := []
  falsePaths := []
  haltedPaths := []
  unmodeledPaths := []
}

/- Unary `not` is a structural operation on the already-evaluated partition.  It does not
re-run an atom, reclassify feasibility, or invent a truth witness.  Failures and paths whose
semantics remain open keep exactly the same disposition. -/
def executableNegateConditionFlow
    (flow : ExecutableConditionFlow) : ExecutableConditionFlow := {
  truePaths := flow.falsePaths
  falsePaths := flow.truePaths
  haltedPaths := flow.haltedPaths
  unmodeledPaths := flow.unmodeledPaths
}

def executableSplitPath
    (condition : Term) (path : ExecutableHeapPath) :
    Option (ExecutableHeapPath × ExecutableHeapPath) :=
  if inferSort condition != some .bool then none
  else some (
    { path with
      guard := .and [path.guard, condition]
      state := heapStatementThenEntry path.state condition },
    { path with
      guard := .and [path.guard, .not condition]
      state := heapStatementElseEntry path.state condition })

def executableConditionFlowCount (flow : ExecutableConditionFlow) : Nat :=
  flow.truePaths.length + flow.falsePaths.length + flow.haltedPaths.length +
    flow.unmodeledPaths.length

inductive ExecutableConditionDisposition where
  | modeled
  | refuted
  | unmodeled
  deriving DecidableEq

def executableConditionDisposition (flow : ExecutableConditionFlow) :
    ExecutableConditionDisposition :=
  if !flow.haltedPaths.isEmpty then .refuted
  else if !flow.unmodeledPaths.isEmpty then .unmodeled
  else .modeled

def executableUnionConditionFlows (flows : List ExecutableConditionFlow) : ExecutableConditionFlow :=
  flows.foldl (fun combined flow => {
    truePaths := combined.truePaths ++ flow.truePaths
    falsePaths := combined.falsePaths ++ flow.falsePaths
    haltedPaths := combined.haltedPaths ++ flow.haltedPaths
    unmodeledPaths := combined.unmodeledPaths ++ flow.unmodeledPaths
  }) { truePaths := [], falsePaths := [], haltedPaths := [], unmodeledPaths := [] }

def executableScalarComparisonTerm
    (operator : ExecutableScalarComparisonOperator)
    (left right : Term) : Option Term :=
  let leftSort := inferSort left
  let rightSort := inferSort right
  let (coercedLeft, coercedRight, comparisonSort) :=
    match leftSort, rightSort with
    | some .bool, some .int =>
        (promoteHeapConditionalBoolToInt left, right, some ValueSort.int)
    | some .int, some .bool =>
        (left, promoteHeapConditionalBoolToInt right, some ValueSort.int)
    | some leftSort, some rightSort =>
        (left, right, if leftSort == rightSort then some leftSort else none)
    | _, _ => (left, right, none)
  match comparisonSort with
  | some .bool =>
      match operator with
      | .equal => some (.equal coercedLeft coercedRight)
      | .notEqual => some (.not (.equal coercedLeft coercedRight))
      | _ => none
  | some .int =>
      match operator with
      | .equal => some (.equal coercedLeft coercedRight)
      | .notEqual => some (.not (.equal coercedLeft coercedRight))
      | .less => some (.less coercedLeft coercedRight)
      | .lessEqual => some (.lessEqual coercedLeft coercedRight)
      | .greater => some (.greater coercedLeft coercedRight)
      | .greaterEqual => some (.greaterEqual coercedLeft coercedRight)
  | _ => none

def executablePureMethodAtomCondition
    (invocation : ExecutablePureMethodInvocation)
    (atom : ExecutablePureMethodAtom) : Option Term :=
  match atom with
  | .boolean _ _ =>
      if inferSort invocation.result == some .bool then some invocation.result else none
  | .compareCallLeft _ _ operator peer =>
      if !executableReadFreeScalarTerm peer then none
      else executableScalarComparisonTerm operator invocation.result peer
  | .compareCallRight peer operator _ _ =>
      if !executableReadFreeScalarTerm peer then none
      else executableScalarComparisonTerm operator peer invocation.result

def executeExecutableHeapCondition
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog) :
    ExecutableHeapCondition → ExecutableHeapPath → Option ExecutableConditionFlow
  | .instanceOf request, path =>
      match executableSplitInstanceOf request path with
      | none => some (executableUnmodeledConditionFlow path)
      | some split => some
          (executableConditionFlowFromSplit proofKernel split.thenPath split.elsePath)
  | .pureMethod atom, path =>
      let receiverName := executablePureMethodAtomReceiver atom
      let methodName := executablePureMethodAtomMethod atom
      match path.status with
      | .returned _ | .halted _ => some (executableUnmodeledConditionFlow path)
      | .normal =>
          match executableLookupLocal path.state.environment receiverName with
          | none => some (executableUnmodeledConditionFlow path)
          | some binding =>
              match executableInvokePureMethod catalog binding methodName path with
              | none => some (executableUnmodeledConditionFlow path)
              | some invocation =>
                  match executablePureMethodAtomCondition invocation atom with
                  | none => some (executableUnmodeledConditionFlow path)
                  | some condition =>
                      match proofKernel invocation.obligations with
                      | .unresolved => some (executableUnmodeledConditionFlow path)
                      | .refuted failed _ => some {
                          truePaths := []
                          falsePaths := []
                          haltedPaths := [executableHaltPath path invocation.obligations failed]
                          unmodeledPaths := []
                        }
                      | .proved =>
                          let checkedState : HeapFunctionState := {
                            path.state with
                            assumptions := path.state.assumptions ++ invocation.assumptions
                            obligations := path.state.obligations ++ invocation.obligations
                          }
                          let checkedPath := { path with state := checkedState }
                          match executableSplitPath condition checkedPath with
                          | none => some (executableUnmodeledConditionFlow path)
                          | some (thenPath, elsePath) => some
                              (executableConditionFlowFromSplit
                                proofKernel thenPath elsePath)
  | .not condition, path =>
      match executeExecutableHeapCondition proofKernel catalog condition path with
      | none => none
      | some flow => some (executableNegateConditionFlow flow)
  | .and left right, path =>
      match executeExecutableHeapCondition proofKernel catalog left path with
      | none => none
      | some leftFlow =>
          match leftFlow.truePaths.mapM
              (executeExecutableHeapCondition proofKernel catalog right) with
          | none => none
          | some rightFlows =>
              let rightFlow := executableUnionConditionFlows rightFlows
              let combined : ExecutableConditionFlow := {
                truePaths := rightFlow.truePaths
                falsePaths := leftFlow.falsePaths ++ rightFlow.falsePaths
                haltedPaths := leftFlow.haltedPaths ++ rightFlow.haltedPaths
                unmodeledPaths := leftFlow.unmodeledPaths ++ rightFlow.unmodeledPaths
              }
              some combined
  | .or left right, path =>
      match executeExecutableHeapCondition proofKernel catalog left path with
      | none => none
      | some leftFlow =>
          match leftFlow.falsePaths.mapM
              (executeExecutableHeapCondition proofKernel catalog right) with
          | none => none
          | some rightFlows =>
              let rightFlow := executableUnionConditionFlows rightFlows
              let combined : ExecutableConditionFlow := {
                truePaths := leftFlow.truePaths ++ rightFlow.truePaths
                falsePaths := rightFlow.falsePaths
                haltedPaths := leftFlow.haltedPaths ++ rightFlow.haltedPaths
                unmodeledPaths := leftFlow.unmodeledPaths ++ rightFlow.unmodeledPaths
              }
              some combined


inductive ExecutableHeapStmt where
  | pass
  | assertion (condition : Term)
  | assignLocal (name : String) (value : Term) (type : HeapStatementLocalType)
  | effect (effect : ExecutableHeapEffect)
  | ifThenElse (condition : Term)
      (thenBody elseBody : List ExecutableHeapStmt)
  | ifInstanceOf (request : ExecutableInstanceOfRequest)
      (thenBody elseBody : List ExecutableHeapStmt)
  | returnValue (value : Term)
  | returnFieldRead (read : ExecutableRawFieldRead)

mutual

  def executeExecutableHeapStmt
      (declaredSort : ValueSort) (statement : ExecutableHeapStmt)
      (path : ExecutableHeapPath) : Option (List ExecutableHeapPath) :=
    match path.status with
    | .returned _ | .halted _ => some [path]
    | .normal =>
        match statement with
        | .pass => some [path]
        | .assertion condition =>
            if inferSort condition != some .bool then none
            else some [{ path with state := {
              path.state with obligations := path.state.obligations ++ [condition]
            }}]
        | .assignLocal name value type =>
            if inferSort value != some (heapStatementLocalTypeSort type) then none
            else
              let binding : HeapStatementLocal := {
                name
                value
                valueType := type
                exactRuntimeClassProved := false
                sourceConstructedProved := false
              }
              some [{ path with state := {
                path.state with environment := executableBindLocal path.state.environment binding
              }}]
        | .effect effect => (executeExecutableHeapEffect effect path).map (fun result => [result])
        | .returnValue value =>
            let returned := coerceV43ReturnValue declaredSort value
            if !heapV43ReturnSortSupported declaredSort ||
                inferSort returned != some declaredSort then none
            else some [{ path with status := .returned returned }]
        | .returnFieldRead read =>
            (executeExecutableRawFieldReturn read path).map (fun result => [result])
        | .ifThenElse condition thenBody elseBody =>
            match executableSplitPath condition path with
            | none => none
            | some (thenPath, elsePath) =>
                match executeExecutableHeapBlock declaredSort thenBody [thenPath],
                    executeExecutableHeapBlock declaredSort elseBody [elsePath] with
                | some thenPaths, some elsePaths =>
                    some (thenPaths ++ elsePaths)
                | _, _ => none
        | .ifInstanceOf request thenBody elseBody =>
            match executableSplitInstanceOf request path with
            | none => none
            | some split =>
                match executeExecutableHeapBlock declaredSort thenBody [split.thenPath],
                    executeExecutableHeapBlock declaredSort elseBody [split.elsePath] with
                | some thenPaths, some elsePaths =>
                    some (thenPaths ++ elsePaths)
                | _, _ => none

  def executeExecutableHeapBlock
      (declaredSort : ValueSort) (statements : List ExecutableHeapStmt)
      (paths : List ExecutableHeapPath) : Option (List ExecutableHeapPath) :=
    match statements with
    | [] => some paths
    | statement :: rest =>
        match paths.mapM (executeExecutableHeapStmt declaredSort statement) with
        | none => none
        | some nestedPaths =>
            executeExecutableHeapBlock declaredSort rest nestedPaths.flatten

end

structure ExecutableHeapConditionalBlockResult where
  modeledExits : List ExecutableHeapPath
  unmodeledPaths : List ExecutableHeapPath

/- A v46 compound conditional is not represented by a caller-supplied exit trace.  The
condition evaluator constructs its guarded path partition, and these actual paths are then
fed to the same recursive block executor as ordinary heap statements. -/
def executeExecutableHeapConditionalBlock
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (declaredSort : ValueSort) (condition : ExecutableHeapCondition)
    (thenBody elseBody : List ExecutableHeapStmt) (path : ExecutableHeapPath) :
    Option ExecutableHeapConditionalBlockResult :=
  match path.status with
  | .returned _ | .halted _ => some { modeledExits := [path], unmodeledPaths := [] }
  | .normal =>
      match executeExecutableHeapCondition proofKernel catalog condition path with
      | none => none
      | some flow =>
          match executeExecutableHeapBlock declaredSort thenBody flow.truePaths,
              executeExecutableHeapBlock declaredSort elseBody flow.falsePaths with
          | some trueExits, some falseExits =>
              let exits := trueExits ++ falseExits ++ flow.haltedPaths
              some { modeledExits := exits, unmodeledPaths := flow.unmodeledPaths }
          | _, _ => none

abbrev ExecutableHeapPostcondition := Term → Nat → Nat → Term

structure ExecutableHeapFunction where
  declaredSort : ValueSort
  body : List ExecutableHeapStmt
  postconditions : List ExecutableHeapPostcondition
  sourceLine : Nat

structure ExecutableHeapReturnExit where
  guard : Term
  value : Term
  state : HeapFunctionState
  postconditionObligations : List Term
  sourceLine : Nat

inductive ExecutableHeapFinalPath where
  | returned (exit : ExecutableHeapReturnExit)
  | implicitNoneMismatch (exit : ExecutableHeapReturnExit)
  | halted (path : ExecutableHeapPath)

def executableInstantiatePostconditions
    (postconditions : List ExecutableHeapPostcondition)
    (guard value : Term) (state : HeapFunctionState) : List Term :=
  postconditions.map (fun postcondition =>
    .implies guard (postcondition value state.heap state.mask))

def executableGuardedImplicitNoneMismatch (guard : Term) : Term :=
  .implies guard (.boolLiteral false)

def finalizeExecutableHeapPath
    (function : ExecutableHeapFunction) (path : ExecutableHeapPath) :
    Option ExecutableHeapFinalPath :=
  match path.status with
  | .halted failed => some (.halted { path with status := .halted failed })
  | .returned value =>
      let obligations := executableInstantiatePostconditions
        function.postconditions path.guard value path.state
      if !executableTermsAreBoolean obligations then none
      else some (.returned {
        guard := path.guard
        value
        state := { path.state with obligations := path.state.obligations ++ obligations }
        postconditionObligations := obligations
        sourceLine := function.sourceLine
      })
  | .normal =>
      let value := Term.unitLiteral
      if function.declaredSort != .unit then
        let obligations := [executableGuardedImplicitNoneMismatch path.guard]
        some (.implicitNoneMismatch {
          guard := path.guard
          value
          state := { path.state with obligations := path.state.obligations ++ obligations }
          postconditionObligations := obligations
          sourceLine := function.sourceLine
        })
      else
        let obligations := executableInstantiatePostconditions
          function.postconditions path.guard value path.state
        if !executableTermsAreBoolean obligations then none
        else some (.returned {
          guard := path.guard
          value
          state := { path.state with obligations := path.state.obligations ++ obligations }
          postconditionObligations := obligations
          sourceLine := function.sourceLine
        })

def executeExecutableHeapFunction
    (function : ExecutableHeapFunction) (entry : ExecutableHeapPath) :
    Option (List ExecutableHeapFinalPath) :=
  if !heapV43ReturnSortSupported function.declaredSort ||
      inferSort entry.guard != some .bool then none
  else
    match entry.status with
    | .returned _ | .halted _ => none
    | .normal =>
        match executeExecutableHeapBlock function.declaredSort function.body [entry] with
        | none => none
        | some paths => paths.mapM (finalizeExecutableHeapPath function)

def executableFinalPathObligations : ExecutableHeapFinalPath → List Term
  | .returned exit | .implicitNoneMismatch exit => exit.state.obligations
  | .halted path => path.state.obligations

def executableModeledExitObligations
    (paths : List ExecutableHeapFinalPath) : List Term :=
  paths.flatMap executableFinalPathObligations

def finalizeExecutableHeapConditionalBlock
    (function : ExecutableHeapFunction)
    (result : ExecutableHeapConditionalBlockResult) :
    Option (List ExecutableHeapFinalPath × List ExecutableHeapPath) :=
  match result.modeledExits.mapM (finalizeExecutableHeapPath function) with
  | none => none
  | some finalPaths => some (finalPaths, result.unmodeledPaths)

inductive ExecutableFinalDisposition where
  | proved
  | refuted (failedObligation : Term)
  | unmodeled

def executableFinalDisposition
    (proofKernel : ExecutableProofKernel)
    (modeledExits : List ExecutableHeapFinalPath)
    (unmodeledPaths : List ExecutableHeapPath) : ExecutableFinalDisposition :=
  let obligations := executableModeledExitObligations modeledExits
  match proofKernel obligations with
  | .refuted failed _ => .refuted failed
  | .unresolved => .unmodeled
  | .proved => if unmodeledPaths.isEmpty then .proved else .unmodeled

/-! Theorems connecting the executable core to the v42-v50 properties. -/

theorem executable_if_constructs_distinct_opposite_guarded_entries
    (condition : Term) (path : ExecutableHeapPath)
    (typed : inferSort condition = some .bool) :
    executableSplitPath condition path = some (
      { path with
        guard := .and [path.guard, condition]
        state := heapStatementThenEntry path.state condition },
      { path with
        guard := .and [path.guard, .not condition]
        state := heapStatementElseEntry path.state condition }) := by
  have notDifferent : (some ValueSort.bool != some ValueSort.bool) = false := by rfl
  simp [executableSplitPath, typed, notDifferent]

theorem executable_absent_else_is_negated_guard_fallthrough
    (declaredSort : ValueSort) (condition : Term) (path : ExecutableHeapPath)
    :
    executeExecutableHeapBlock declaredSort [] [{ path with
      guard := .and [path.guard, .not condition]
      state := heapStatementElseEntry path.state condition }] =
      some [{ path with
        guard := .and [path.guard, .not condition]
        state := heapStatementElseEntry path.state condition }] := by
  simp [executeExecutableHeapBlock]

theorem executable_returned_path_absorbs_every_later_statement
    (declaredSort : ValueSort) (statement : ExecutableHeapStmt)
    (path : ExecutableHeapPath) (value : Term)
    (returned : path.status = .returned value) :
    executeExecutableHeapStmt declaredSort statement path = some [path] := by
  cases statement <;>
    simp_all [executeExecutableHeapStmt.eq_1, executeExecutableHeapStmt.eq_2,
      executeExecutableHeapStmt.eq_3, executeExecutableHeapStmt.eq_4,
      executeExecutableHeapStmt.eq_5, executeExecutableHeapStmt.eq_6,
      executeExecutableHeapStmt.eq_7, executeExecutableHeapStmt.eq_8]

theorem executable_halted_path_absorbs_every_later_statement
    (declaredSort : ValueSort) (statement : ExecutableHeapStmt)
    (path : ExecutableHeapPath) (failed : Term)
    (halted : path.status = .halted failed) :
    executeExecutableHeapStmt declaredSort statement path = some [path] := by
  cases statement <;>
    simp_all [executeExecutableHeapStmt.eq_1, executeExecutableHeapStmt.eq_2,
      executeExecutableHeapStmt.eq_3, executeExecutableHeapStmt.eq_4,
      executeExecutableHeapStmt.eq_5, executeExecutableHeapStmt.eq_6,
      executeExecutableHeapStmt.eq_7, executeExecutableHeapStmt.eq_8]

theorem executable_field_write_advances_only_its_path_heap
    (write : ExecutableSourceFieldWriteEffect) (path result : ExecutableHeapPath)
    (normal : path.status = .normal)
    (proved : write.permissionDisposition = .proved)
    (accepted : executeExecutableHeapEffect (.sourceFieldWrite write) path = some result) :
    result.guard = path.guard ∧ result.state.heap = path.state.heap + 1 ∧
      result.state.mask = path.state.mask := by
  cases path
  simp_all [executeExecutableHeapEffect]
  rcases accepted with ⟨_, rfl⟩
  simp

theorem executable_refuted_field_write_is_state_nonextending
    (write : ExecutableSourceFieldWriteEffect) (path result : ExecutableHeapPath)
    (normal : path.status = .normal)
    (failed : Term)
    (refuted : write.permissionDisposition = .refuted failed)
    (accepted : executeExecutableHeapEffect (.sourceFieldWrite write) path = some result) :
    result.state.heap = path.state.heap ∧ result.state.mask = path.state.mask ∧
      result.status = .halted failed := by
  cases path
  simp_all [executeExecutableHeapEffect, executableHaltPath]
  rcases accepted with ⟨_, rfl⟩
  simp

theorem executable_if_never_merges_branch_path_lists
    (declaredSort : ValueSort) (condition : Term)
    (thenBody elseBody : List ExecutableHeapStmt) (path : ExecutableHeapPath)
    (thenPath elsePath : ExecutableHeapPath)
    (thenPaths elsePaths result : List ExecutableHeapPath)
    (split : executableSplitPath condition path = some (thenPath, elsePath))
    (thenExecuted : executeExecutableHeapBlock declaredSort thenBody [thenPath] = some thenPaths)
    (elseExecuted : executeExecutableHeapBlock declaredSort elseBody [elsePath] = some elsePaths)
    (normal : path.status = .normal)
    (executed : executeExecutableHeapStmt declaredSort
      (.ifThenElse condition thenBody elseBody) path = some result) :
    result = thenPaths ++ elsePaths := by
  simp [executeExecutableHeapStmt, normal, split, thenExecuted, elseExecuted] at executed
  exact executed.symm

theorem executable_actual_return_exit_gets_exact_bound_postconditions
    (function : ExecutableHeapFunction) (path : ExecutableHeapPath)
    (value : Term) (exit : ExecutableHeapReturnExit)
    (returned : path.status = .returned value)
    (finalized : finalizeExecutableHeapPath function path = some (.returned exit)) :
    exit.postconditionObligations = executableInstantiatePostconditions
      function.postconditions path.guard value path.state := by
  simp [finalizeExecutableHeapPath, returned] at finalized
  rcases finalized with ⟨_, rfl⟩
  rfl

theorem executable_nonunit_fallthrough_is_guarded_implicit_none_mismatch
    (function : ExecutableHeapFunction) (path : ExecutableHeapPath)
    (normal : path.status = .normal)
    (nonunit : (function.declaredSort == .unit) = false) :
    let obligations := [executableGuardedImplicitNoneMismatch path.guard]
    finalizeExecutableHeapPath function path = some (.implicitNoneMismatch {
      guard := path.guard
      value := .unitLiteral
      state := { path.state with obligations := path.state.obligations ++ obligations }
      postconditionObligations := obligations
      sourceLine := function.sourceLine
    }) := by
  simp [finalizeExecutableHeapPath, normal, bne, nonunit]

/- The assertion expression itself is a VC, not a control-flow test.  Prerequisite
failures are represented by the typed effect/evaluation steps that precede it. -/
theorem executable_assertion_adds_vc_and_continues
    (declaredSort : ValueSort) (condition : Term) (path : ExecutableHeapPath)
    (normal : path.status = .normal)
    (typed : inferSort condition = some .bool) :
    executeExecutableHeapStmt declaredSort (.assertion condition) path =
      some [{ path with state := {
        path.state with obligations := path.state.obligations ++ [condition]
      }}] := by
  have notDifferent : (some ValueSort.bool != some ValueSort.bool) = false := by rfl
  simp [executeExecutableHeapStmt.eq_2, normal, typed, notDifferent]

theorem executable_halted_path_receives_no_postcondition_instances
    (function : ExecutableHeapFunction) (path : ExecutableHeapPath) (failed : Term)
    (halted : path.status = .halted failed) :
    finalizeExecutableHeapPath function path = some (.halted path) := by
  cases path with
  | mk guard state status =>
      cases halted
      rfl

/-! Executable v45 object narrowing, raw reads, and scalar conditional expressions. -/

theorem executable_opaque_object_parameter_has_no_nominal_or_exact_metadata
    (name : String) (value : Term) (binding : HeapStatementLocal)
    (accepted : executableOpaqueObjectParameter name value = some binding) :
    binding.valueType = .opaqueObject ∧
      binding.exactRuntimeClassProved = false ∧
      binding.sourceConstructedProved = false := by
  unfold executableOpaqueObjectParameter at accepted
  split at accepted
  · contradiction
  · cases accepted
    simp

theorem executable_opaque_object_is_not_a_source_receiver :
    executableSourceReceiverTypeValid .opaqueObject = false := by
  rfl

theorem executable_opaque_object_cannot_flow_into_nominal_field
    (field : HeapStatementNominalType) (evidence : GuardedFieldWriteNominalEvidence) :
    guardedFieldWriteTypesCompatible (.nominal field) .opaqueObject evidence = false := by
  rfl

theorem executable_catalog_subtype_requires_valid_checked_edges
    (catalog : ExecutableCompleteSourceClassCatalog) (actual expected : String)
    (proved : executableCatalogProvesSubtype catalog actual expected = true) :
    executableSourceClassCatalogValid catalog = true := by
  unfold executableCatalogProvesSubtype at proved
  split at proved
  · simp_all
  · simpa using ‹¬(!executableSourceClassCatalogValid catalog) = true›

theorem executable_two_node_source_class_cycle_is_invalid :
    executableSourceClassCatalogValid {
      classes := [
        { name := "A", directBase := some "B", fields := [], pureMethods := [] },
        { name := "B", directBase := some "A", fields := [], pureMethods := [] }
      ]
    } = false := by
  rfl

theorem executable_dynamic_isinstance_predicate_is_boolean
    (value : Term) (targetClass : String)
    (reference : inferSort value = some .reference)
    (named : targetClass.isEmpty = false) :
    inferSort (executableInstanceOfDynamicPredicate value targetClass) = some .bool := by
  simp [executableInstanceOfDynamicPredicate, inferSort, allBool, reference, named,
    instBEqValueSort, valueSortBeq]

theorem executable_opaque_isinstance_true_branch_is_nonoptional_source_nominal
    (catalog : ExecutableCompleteSourceClassCatalog) (name targetClass : String) (value : Term) :
    let binding : HeapStatementLocal := {
      name
      value
      valueType := .opaqueObject
      exactRuntimeClassProved := false
      sourceConstructedProved := false
    }
    (executableInstanceOfTrueBinding catalog binding targetClass).valueType =
      executableSourceLocalType { canonicalClass := targetClass, optional := false } := by
  rfl

theorem executable_instanceof_split_preserves_heap_mask_and_obligations
    (request : ExecutableInstanceOfRequest) (path : ExecutableHeapPath)
    (split : ExecutableInstanceOfSplit)
    (accepted : executableSplitInstanceOf request path = some split) :
    split.thenPath.state.heap = path.state.heap ∧
      split.elsePath.state.heap = path.state.heap ∧
      split.thenPath.state.mask = path.state.mask ∧
      split.elsePath.state.mask = path.state.mask ∧
      split.thenPath.state.obligations = path.state.obligations ∧
      split.elsePath.state.obligations = path.state.obligations := by
  unfold executableSplitInstanceOf at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases accepted
  simp

theorem executable_instanceof_split_uses_one_condition_and_preserves_false_metadata
    (request : ExecutableInstanceOfRequest) (path : ExecutableHeapPath)
    (split : ExecutableInstanceOfSplit)
    (accepted : executableSplitInstanceOf request path = some split) :
    split.thenPath.guard = .and [path.guard, split.condition] ∧
      split.elsePath.guard = .and [path.guard, .not split.condition] ∧
      split.elsePath.state.environment = path.state.environment := by
  unfold executableSplitInstanceOf at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases accepted
  simp

theorem executable_known_nominal_subtype_survives_true_narrowing
    (catalog : ExecutableCompleteSourceClassCatalog)
    (actualClass targetClass name : String) (value : Term)
    (named : actualClass.isEmpty = false)
    (subtype : executableCatalogProvesSubtype catalog actualClass targetClass = true) :
    let nominal : HeapStatementNominalType := {
      canonicalClass := actualClass
      optional := true
      sourceOwned := true
      checkedExternalContractHash := ""
    }
    let binding : HeapStatementLocal := {
      name
      value
      valueType := .nominal nominal
      exactRuntimeClassProved := false
      sourceConstructedProved := false
    }
    (executableInstanceOfTrueBinding catalog binding targetClass).valueType =
      .nominal { nominal with optional := false } := by
  simp [executableInstanceOfTrueBinding, heapStatementNominalTypeValidated, named, subtype]

theorem executable_instanceof_pure_pass_restores_entire_incoming_environment
    (request : ExecutableInstanceOfRequest) (path : ExecutableHeapPath)
    (split : ExecutableInstanceOfSplit)
    (accepted : executableSplitInstanceOf request path = some split) :
    executableJoinInstanceOfPurePass request path = some path.state.environment := by
  simp [executableJoinInstanceOfPurePass, accepted]

theorem executable_opaque_binding_refuses_raw_field_resolution
    (read : ExecutableRawFieldRead) (path : ExecutableHeapPath)
    (binding : HeapStatementLocal)
    (found : executableLookupLocal path.state.environment read.receiverName = some binding)
    (opaqueType : binding.valueType = .opaqueObject) :
    executableResolveRawFieldRead read path = none := by
  simp [executableResolveRawFieldRead, found, opaqueType, executableSourceReceiverTypeValid]

theorem executable_lookup_local_result_has_requested_name
    (environment : HeapStatementEnvironment) (name : String) (binding : HeapStatementLocal)
    (found : executableLookupLocal environment name = some binding) :
    binding.name = name := by
  induction environment with
  | nil => simp [executableLookupLocal] at found
  | cons head rest ih =>
      simp only [executableLookupLocal] at found
      split at found
      · cases found
        simp_all
      · exact ih found

theorem executable_catalog_backed_narrowing_enables_declared_raw_field_resolution
    (catalog : ExecutableCompleteSourceClassCatalog)
    (receiverName targetClass fieldName : String) (value : Term)
    (field : ExecutableSourceFieldRecord)
    (targetNamed : targetClass.isEmpty = false)
    (fieldNamed : fieldName.isEmpty = false)
    (reference : inferSort value = some .reference)
    (foundField : executableCatalogLookupField catalog targetClass fieldName = some field) :
    let original : HeapStatementLocal := {
      name := receiverName
      value
      valueType := .opaqueObject
      exactRuntimeClassProved := false
      sourceConstructedProved := false
    }
    let narrowed := executableInstanceOfTrueBinding catalog original targetClass
    let path : ExecutableHeapPath := {
      guard := .boolLiteral true
      state := {
        environment := [narrowed]
        heap := 0
        mask := 0
        assumptions := []
        obligations := []
      }
      status := .normal
    }
    executableResolveRawFieldRead {
      receiverName
      fieldName
      catalog
      permissionDisposition := .proved
    } path = some { receiver := value, field } := by
  have sameReference : (some ValueSort.reference != some ValueSort.reference) = false := by rfl
  simp [executableResolveRawFieldRead, executableInstanceOfTrueBinding,
    executableLookupLocal, executableSourceReceiverTypeValid,
    executableSourceLocalType, heapStatementNominalTypeValidated,
    targetNamed, fieldNamed, reference, foundField, sameReference]

theorem executable_checked_instanceof_then_raw_field_resolution_composes
    (catalog : ExecutableCompleteSourceClassCatalog)
    (receiverName targetClass fieldName : String)
    (path : ExecutableHeapPath) (original : HeapStatementLocal)
    (split : ExecutableInstanceOfSplit) (field : ExecutableSourceFieldRecord)
    (normal : path.status = .normal)
    (found : executableLookupLocal path.state.environment receiverName = some original)
    (opaqueType : original.valueType = .opaqueObject)
    (reference : inferSort original.value = some .reference)
    (targetSafe : executableCatalogHasSourceSafeClass catalog targetClass = true)
    (targetNamed : targetClass.isEmpty = false)
    (fieldNamed : fieldName.isEmpty = false)
    (foundField : executableCatalogLookupField catalog targetClass fieldName = some field)
    (accepted : executableSplitInstanceOf {
      subjectName := receiverName
      targetClass
      catalog
    } path = some split) :
    executableResolveRawFieldRead {
      receiverName
      fieldName
      catalog
      permissionDisposition := .proved
    } split.thenPath = some { receiver := original.value, field } := by
  have sameName := executable_lookup_local_result_has_requested_name
    path.state.environment receiverName original found
  unfold executableSplitInstanceOf at accepted
  rw [normal] at accepted
  simp [targetSafe, found, reference] at accepted
  rcases accepted with ⟨_, rfl⟩
  have sameReference : (some ValueSort.reference != some ValueSort.reference) = false := by rfl
  simp [executableResolveRawFieldRead, executableLookupLocal, executableBindLocal,
    executableInstanceOfTrueBinding, executableSourceReceiverTypeValid,
    executableSourceLocalType, heapStatementNominalTypeValidated,
    opaqueType, sameName, targetNamed, fieldNamed, reference, foundField, sameReference]

theorem executable_raw_field_permission_uses_current_path_mask
    (read : ExecutableResolvedRawFieldRead) (path : ExecutableHeapPath) :
    .permissionAtLeast path.state.mask read.receiver read.field.name 1 1 ∈
      executableRawFieldReadObligations read path := by
  simp [executableRawFieldReadObligations]

theorem executable_raw_field_refutation_is_path_local_and_state_nonextending
    (request : ExecutableRawFieldRead) (path result : ExecutableHeapPath)
    (failed : Term) (normal : path.status = .normal)
    (refuted : request.permissionDisposition = .refuted failed)
    (accepted : executeExecutableRawFieldReturn request path = some result) :
    result.guard = path.guard ∧ result.state.heap = path.state.heap ∧
      result.state.mask = path.state.mask ∧ result.status = .halted failed ∧
      ∃ read, executableResolveRawFieldRead request path = some read ∧
        result.state.obligations = path.state.obligations ++
          executableRawFieldReadObligations read path := by
  unfold executeExecutableRawFieldReturn at accepted
  simp [normal] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  simp [refuted, executableHaltPath] at accepted
  cases accepted
  simp_all

theorem executable_proved_raw_field_read_returns_catalog_resolved_current_heap_value
    (request : ExecutableRawFieldRead) (path result : ExecutableHeapPath)
    (read : ExecutableResolvedRawFieldRead)
    (normal : path.status = .normal)
    (resolved : executableResolveRawFieldRead request path = some read)
    (proved : request.permissionDisposition = .proved)
    (accepted : executeExecutableRawFieldReturn request path = some result) :
    result.status = .returned (executableRawFieldReadTerm read path) ∧
      result.state.heap = path.state.heap ∧ result.state.mask = path.state.mask ∧
      result.state.obligations = path.state.obligations ++
        executableRawFieldReadObligations read path := by
  cases path
  simp_all [executeExecutableRawFieldReturn]
  rcases accepted with ⟨_, rfl⟩
  simp

theorem executable_scalar_ifexp_never_accepts_reference_branches
    (condition : Term) :
    executeScalarIfExp condition (.variable "left" .reference)
      (.variable "right" .reference) = none := by
  simp [executeScalarIfExp, executableReadFreeScalarTerm]

theorem executable_scalar_ifexp_never_accepts_class_branches
    (condition : Term) :
    executeScalarIfExp condition (.variable "left" .class)
      (.variable "right" .class) = none := by
  simp [executeScalarIfExp, executableReadFreeScalarTerm]

theorem executable_scalar_ifexp_rejects_heap_field_reads
    (condition receiver : Term) (heap : Nat) (field : String) :
    executeScalarIfExp condition (.fieldRead heap receiver field .int) (.intLiteral 0) = none := by
  simp [executeScalarIfExp, executableReadFreeScalarTerm]

theorem executable_bool_scalar_ifexp_constructs_boolean_ite :
    executeScalarIfExp (.boolLiteral true) (.boolLiteral false) (.boolLiteral true) =
      some {
        value := .ite (.boolLiteral true) (.boolLiteral false) (.boolLiteral true)
        sort := .bool
      } := by
  rfl

theorem executable_bool_int_scalar_ifexp_promotes_only_the_boolean_branch :
    executeScalarIfExp (.boolLiteral true) (.boolLiteral false) (.intLiteral 7) =
      some {
        value := .ite (.boolLiteral true)
          (promoteHeapConditionalBoolToInt (.boolLiteral false)) (.intLiteral 7)
        sort := .int
  } := by
  rfl

/-! Executable v46 short-circuit conditions, catalog dispatch, and implicit `None`. -/

def executableV46ReadyMethod : ExecutablePureMethodRecord := {
  name := "ready"
  resultRule := .selectedBody (.receiverField "flag")
  preconditions := []
  postconditions := []
}

def executableV46DispatchCatalog : ExecutableCompleteSourceClassCatalog := {
  classes := [
    {
      name := "Base"
      directBase := none
      fields := [{ name := "flag", type := .scalar .bool }]
      pureMethods := [executableV46ReadyMethod]
    },
    {
      name := "Child"
      directBase := some "Base"
      fields := []
      pureMethods := []
    }
  ]
}

def executableV46ExactChildBinding : HeapStatementLocal := {
  name := "value"
  value := .variable "value" .reference
  valueType := .nominal {
    canonicalClass := "Child"
    optional := false
    sourceOwned := true
    checkedExternalContractHash := ""
  }
  exactRuntimeClassProved := true
  sourceConstructedProved := true
}

def executableV46DynamicBaseBinding : HeapStatementLocal := {
  name := "value"
  value := .variable "value" .reference
  valueType := .nominal {
    canonicalClass := "Base"
    optional := false
    sourceOwned := true
    checkedExternalContractHash := ""
  }
  exactRuntimeClassProved := false
  sourceConstructedProved := false
}

theorem executable_v46_exact_inherited_pure_dispatch_agrees :
    executableResolvePureMethodDispatch executableV46DispatchCatalog
      executableV46ExactChildBinding "ready" = some {
        receiverClass := "Child"
        method := executableV46ReadyMethod
      } := by
  rfl

theorem executable_v46_selected_body_relation_uses_current_heap_and_mask
    (path : ExecutableHeapPath) :
    executableInvokePureMethod executableV46DispatchCatalog executableV46ExactChildBinding
      "ready" path = some {
        result := .fieldRead path.state.heap executableV46ExactChildBinding.value "flag" .bool
        obligations := [
          .not (.equal executableV46ExactChildBinding.value .nullReference),
          .permissionAtLeast path.state.mask executableV46ExactChildBinding.value "flag" 1 1
        ]
        assumptions := []
      } := by
  rfl

theorem executable_v46_nonexact_dynamic_dispatch_refuses_even_when_catalog_looks_uniform :
    executableResolvePureMethodDispatch executableV46DispatchCatalog
      executableV46DynamicBaseBinding "ready" = none := by
  rfl

theorem executable_v46_refutation_precedes_unmodeled_siblings
    (flow : ExecutableConditionFlow) (failed : ExecutableHeapPath)
    (rest : List ExecutableHeapPath)
    (hasFailure : flow.haltedPaths = failed :: rest) :
    executableConditionDisposition flow = .refuted := by
  simp [executableConditionDisposition, hasFailure]

theorem executable_v46_unmodeled_prevents_modeled_without_a_refutation
    (flow : ExecutableConditionFlow) (unknown : ExecutableHeapPath)
    (rest : List ExecutableHeapPath)
    (noFailure : flow.haltedPaths = [])
    (hasUnknown : flow.unmodeledPaths = unknown :: rest) :
    executableConditionDisposition flow = .unmodeled := by
  simp [executableConditionDisposition, noFailure, hasUnknown]

theorem executable_v46_and_evaluates_rhs_only_on_left_true_paths
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (left right : ExecutableHeapCondition) (path : ExecutableHeapPath)
    (narrowed fallback : ExecutableHeapPath) (rightFlow : ExecutableConditionFlow)
    (leftExecuted : executeExecutableHeapCondition proofKernel catalog left path = some {
      truePaths := [narrowed]
      falsePaths := [fallback]
      haltedPaths := []
      unmodeledPaths := []
    })
    (rightExecuted : executeExecutableHeapCondition proofKernel catalog right narrowed =
      some rightFlow) :
    executeExecutableHeapCondition proofKernel catalog (.and left right) path = some {
      truePaths := rightFlow.truePaths
      falsePaths := [fallback] ++ rightFlow.falsePaths
      haltedPaths := rightFlow.haltedPaths
      unmodeledPaths := rightFlow.unmodeledPaths
    } := by
  simp [executeExecutableHeapCondition, leftExecuted, rightExecuted,
    executableUnionConditionFlows]

theorem executable_v46_instanceof_true_narrowing_is_the_only_rhs_entry
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (request : ExecutableInstanceOfRequest) (right : ExecutableHeapCondition)
    (path : ExecutableHeapPath) (split : ExecutableInstanceOfSplit)
    (rightFlow : ExecutableConditionFlow)
    (splitAccepted : executableSplitInstanceOf request path = some split)
    (thenFeasible : executableClassifyPathFeasibility proofKernel split.thenPath = .feasible)
    (elseFeasible : executableClassifyPathFeasibility proofKernel split.elsePath = .feasible)
    (rightExecuted : executeExecutableHeapCondition proofKernel catalog right split.thenPath =
      some rightFlow) :
    executeExecutableHeapCondition proofKernel catalog
      (.and (.instanceOf request) right) path = some {
        truePaths := rightFlow.truePaths
        falsePaths := [split.elsePath] ++ rightFlow.falsePaths
        haltedPaths := rightFlow.haltedPaths
        unmodeledPaths := rightFlow.unmodeledPaths
      } := by
  apply executable_v46_and_evaluates_rhs_only_on_left_true_paths
      proofKernel catalog (.instanceOf request) right path split.thenPath split.elsePath
      rightFlow
  · simp [executeExecutableHeapCondition, splitAccepted,
      executableConditionFlowFromSplit, executableClassifyConditionPaths,
      thenFeasible, elseFeasible]
  · exact rightExecuted

theorem executable_v46_and_skips_rhs_when_left_has_no_true_path
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (left right : ExecutableHeapCondition) (path : ExecutableHeapPath)
    (falsePaths haltedPaths unmodeledPaths : List ExecutableHeapPath)
    (leftExecuted : executeExecutableHeapCondition proofKernel catalog left path = some {
      truePaths := []
      falsePaths
      haltedPaths
      unmodeledPaths
    }) :
    executeExecutableHeapCondition proofKernel catalog (.and left right) path = some {
      truePaths := []
      falsePaths
      haltedPaths
      unmodeledPaths
    } := by
  simp [executeExecutableHeapCondition, leftExecuted, executableUnionConditionFlows]

theorem executable_v46_or_skips_rhs_when_left_has_no_false_path
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (left right : ExecutableHeapCondition) (path : ExecutableHeapPath)
    (truePaths haltedPaths unmodeledPaths : List ExecutableHeapPath)
    (leftExecuted : executeExecutableHeapCondition proofKernel catalog left path = some {
      truePaths
      falsePaths := []
      haltedPaths
      unmodeledPaths
    }) :
    executeExecutableHeapCondition proofKernel catalog (.or left right) path = some {
      truePaths
      falsePaths := []
      haltedPaths
      unmodeledPaths
    } := by
  simp [executeExecutableHeapCondition, leftExecuted, executableUnionConditionFlows]

theorem executable_v46_refuted_pure_call_halts_only_its_current_path
    (catalog : ExecutableCompleteSourceClassCatalog)
    (atom : ExecutablePureMethodAtom) (condition : Term)
    (path : ExecutableHeapPath) (binding : HeapStatementLocal)
    (result failed : Term) (rest assumptions : List Term)
    (normal : path.status = .normal)
    (found : executableLookupLocal path.state.environment
      (executablePureMethodAtomReceiver atom) = some binding)
    (invoked : executableInvokePureMethod catalog binding
      (executablePureMethodAtomMethod atom) path = some {
      result
      obligations := failed :: rest
      assumptions
    })
    (conditionBuilt : executablePureMethodAtomCondition {
      result
      obligations := failed :: rest
      assumptions
    } atom = some condition) :
    executeExecutableHeapCondition executableRefuteFirstKernel catalog
        (.pureMethod atom) path = some {
          truePaths := []
          falsePaths := []
          haltedPaths := [executableHaltPath path (failed :: rest) failed]
          unmodeledPaths := []
        } := by
  simp [executeExecutableHeapCondition, normal, found, invoked, conditionBuilt,
    executableRefuteFirstKernel]

theorem executable_v46_compound_condition_executes_only_constructed_branch_paths
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (declaredSort : ValueSort) (condition : ExecutableHeapCondition)
    (thenBody elseBody : List ExecutableHeapStmt) (path : ExecutableHeapPath)
    (flow : ExecutableConditionFlow) (trueExits falseExits : List ExecutableHeapPath)
    (normal : path.status = .normal)
    (conditionExecuted : executeExecutableHeapCondition proofKernel catalog condition path =
      some flow)
    (thenExecuted : executeExecutableHeapBlock declaredSort thenBody flow.truePaths =
      some trueExits)
    (elseExecuted : executeExecutableHeapBlock declaredSort elseBody flow.falsePaths =
      some falseExits) :
    executeExecutableHeapConditionalBlock proofKernel catalog declaredSort condition
      thenBody elseBody path = some {
        modeledExits := trueExits ++ falseExits ++ flow.haltedPaths
        unmodeledPaths := flow.unmodeledPaths
      } := by
  simp [executeExecutableHeapConditionalBlock, normal, conditionExecuted,
    thenExecuted, elseExecuted]

theorem executable_v46_guarded_implicit_none_mismatch_is_boolean
    (guard : Term) (typed : inferSort guard = some .bool) :
    inferSort (executableGuardedImplicitNoneMismatch guard) = some .bool := by
  simp [executableGuardedImplicitNoneMismatch, inferSort, typed,
    instBEqValueSort, valueSortBeq]

theorem executable_v46_reachable_nonunit_fallthrough_is_not_dropped
    (function : ExecutableHeapFunction) (path : ExecutableHeapPath)
    (normal : path.status = .normal)
    (nonunit : (function.declaredSort == .unit) = false) :
    ∃ exit, finalizeExecutableHeapPath function path = some (.implicitNoneMismatch exit) ∧
      executableGuardedImplicitNoneMismatch path.guard ∈ exit.postconditionObligations := by
  let obligations := [executableGuardedImplicitNoneMismatch path.guard]
  refine ⟨{
    guard := path.guard
    value := .unitLiteral
    state := { path.state with obligations := path.state.obligations ++ obligations }
    postconditionObligations := obligations
    sourceLine := function.sourceLine
  }, ?_, ?_⟩
  · exact executable_nonunit_fallthrough_is_guarded_implicit_none_mismatch
      function path normal nonunit
  · simp [obligations]

theorem executable_v46_feasibility_uses_complete_path_assumptions
    (proofKernel : ExecutableProofKernel) (path : ExecutableHeapPath)
    (classified : proofKernel [executablePathInfeasibilityObligation path] = .proved) :
    executableClassifyPathFeasibility proofKernel path = .infeasible := by
  simp [executableClassifyPathFeasibility, classified]

theorem executable_v46_infeasibility_query_contains_assumptions_and_guard
    (path : ExecutableHeapPath) :
    executablePathInfeasibilityObligation path =
      .implies (.and (path.state.assumptions ++ [path.guard])) (.boolLiteral false) := by
  rfl

theorem executable_v46_unresolved_feasibility_is_unmodeled
    (proofKernel : ExecutableProofKernel) (path : ExecutableHeapPath)
    (classified : proofKernel [executablePathInfeasibilityObligation path] = .unresolved) :
    executableClassifyPathFeasibility proofKernel path = .unmodeled := by
  simp [executableClassifyPathFeasibility, classified]

theorem executable_v46_refuted_infeasibility_vc_keeps_path_feasible
    (proofKernel : ExecutableProofKernel) (path : ExecutableHeapPath)
    (failed : Term)
    (member : failed ∈ [executablePathInfeasibilityObligation path])
    (classified : proofKernel [executablePathInfeasibilityObligation path] =
      .refuted failed member) :
    executableClassifyPathFeasibility proofKernel path = .feasible := by
  simp [executableClassifyPathFeasibility, classified]

theorem executable_v46_final_refutation_wins_over_unmodeled_siblings
    (proofKernel : ExecutableProofKernel)
    (modeledExits : List ExecutableHeapFinalPath)
    (unknown : ExecutableHeapPath) (unknownRest : List ExecutableHeapPath)
    (failed : Term)
    (member : failed ∈ executableModeledExitObligations modeledExits)
    (classified : proofKernel (executableModeledExitObligations modeledExits) =
      .refuted failed member) :
    executableFinalDisposition proofKernel modeledExits (unknown :: unknownRest) =
      .refuted failed := by
  simp [executableFinalDisposition, classified]

theorem executable_v46_unmodeled_sibling_blocks_an_otherwise_proved_result
    (proofKernel : ExecutableProofKernel)
    (modeledExits : List ExecutableHeapFinalPath)
    (unknown : ExecutableHeapPath) (unknownRest : List ExecutableHeapPath)
    (classified : proofKernel (executableModeledExitObligations modeledExits) = .proved) :
    executableFinalDisposition proofKernel modeledExits (unknown :: unknownRest) =
      .unmodeled := by
  simp [executableFinalDisposition, classified]

theorem executable_v46_proved_modeled_exits_without_unknowns_are_proved
    (proofKernel : ExecutableProofKernel)
    (modeledExits : List ExecutableHeapFinalPath)
    (classified : proofKernel (executableModeledExitObligations modeledExits) = .proved) :
    executableFinalDisposition proofKernel modeledExits [] = .proved := by
  simp [executableFinalDisposition, classified]

theorem executable_v46_exact_or_source_constructed_closes_dispatch :
    executableBindingExactSourceClass {
      name := "value"
      value := .variable "value" .reference
      valueType := executableSourceLocalType {
        canonicalClass := "A"
        optional := false
      }
      exactRuntimeClassProved := false
      sourceConstructedProved := true
    } = some "A" := by
  rfl

theorem executable_v46_bool_int_comparison_promotes_the_boolean_operand :
    executableScalarComparisonTerm .less (.boolLiteral false) (.intLiteral 1) =
      some (.less (promoteHeapConditionalBoolToInt (.boolLiteral false)) (.intLiteral 1)) := by
  rfl

theorem executable_v46_call_on_right_comparison_preserves_python_operand_order :
    executablePureMethodAtomCondition {
      result := .intLiteral 2
      obligations := []
      assumptions := []
    } (.compareCallRight (.intLiteral 1) .less "value" "number") =
      some (.less (.intLiteral 1) (.intLiteral 2)) := by
  rfl

theorem executable_v46_direct_boolean_method_atom_uses_boolean_result :
    executablePureMethodAtomCondition {
      result := .boolLiteral true
      obligations := []
      assumptions := []
    } (.boolean "value" "ready") = some (.boolLiteral true) := by
  rfl

theorem executable_v46_not_equal_method_comparison_is_explicit_negated_equality :
    executablePureMethodAtomCondition {
      result := .intLiteral 2
      obligations := []
      assumptions := []
    } (.compareCallLeft "value" "number" .notEqual (.intLiteral 1)) =
      some (.not (.equal (.intLiteral 2) (.intLiteral 1))) := by
  rfl

def executableV46ContractMethod : ExecutablePureMethodRecord := {
  name := "number"
  resultRule := .contractResult .int
  preconditions := []
  postconditions := [.equal .methodResult (.intLiteral 1)]
}

def executableV46ContractCatalog : ExecutableCompleteSourceClassCatalog := {
  classes := [{
    name := "A"
    directBase := none
    fields := []
    pureMethods := [executableV46ContractMethod]
  }]
}

def executableV46ExactABinding : HeapStatementLocal := {
  name := "value"
  value := .variable "value" .reference
  valueType := executableSourceLocalType {
    canonicalClass := "A"
    optional := false
  }
  exactRuntimeClassProved := true
  sourceConstructedProved := false
}

theorem executable_v46_selected_contract_summary_constructs_result_assumption
    (path : ExecutableHeapPath) :
    executableInvokePureMethod executableV46ContractCatalog executableV46ExactABinding
      "number" path = some {
        result := .variable
          (executablePureContractResultName "A" "number" executableV46ExactABinding path) .int
        obligations := [
          .not (.equal executableV46ExactABinding.value .nullReference)
        ]
        assumptions := [
          .equal (.variable
            (executablePureContractResultName "A" "number" executableV46ExactABinding path) .int)
            (.intLiteral 1)
        ]
      } := by
  rfl

theorem executable_v46_implicit_none_emits_only_guarded_false_at_function_line
    (function : ExecutableHeapFunction) (path : ExecutableHeapPath)
    (normal : path.status = .normal)
    (nonunit : (function.declaredSort == .unit) = false)
    (exit : ExecutableHeapReturnExit)
    (finalized : finalizeExecutableHeapPath function path =
      some (.implicitNoneMismatch exit)) :
    exit.postconditionObligations = [executableGuardedImplicitNoneMismatch path.guard] ∧
      exit.sourceLine = function.sourceLine := by
  simp [finalizeExecutableHeapPath, normal, bne, nonunit] at finalized
  cases finalized
  simp

/-! Executable v47 unary negation over the v46 condition partition. -/

theorem executable_v47_not_swaps_only_true_and_false_paths
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (condition : ExecutableHeapCondition) (path : ExecutableHeapPath)
    (flow : ExecutableConditionFlow)
    (executed : executeExecutableHeapCondition proofKernel catalog condition path = some flow) :
    executeExecutableHeapCondition proofKernel catalog (.not condition) path = some {
      truePaths := flow.falsePaths
      falsePaths := flow.truePaths
      haltedPaths := flow.haltedPaths
      unmodeledPaths := flow.unmodeledPaths
    } := by
  simp [executeExecutableHeapCondition, executed, executableNegateConditionFlow]

theorem executable_v47_not_is_involutive
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (condition : ExecutableHeapCondition) (path : ExecutableHeapPath) :
    executeExecutableHeapCondition proofKernel catalog (.not (.not condition)) path =
      executeExecutableHeapCondition proofKernel catalog condition path := by
  cases executed : executeExecutableHeapCondition proofKernel catalog condition path with
  | none => simp [executeExecutableHeapCondition, executed]
  | some flow =>
      simp [executeExecutableHeapCondition, executed, executableNegateConditionFlow]

theorem executable_v47_not_preserves_partition_count
    (flow : ExecutableConditionFlow) :
    executableConditionFlowCount (executableNegateConditionFlow flow) =
      executableConditionFlowCount flow := by
  simp [executableConditionFlowCount, executableNegateConditionFlow]
  omega

theorem executable_v47_not_preserves_modeled_unmodeled_refuted_disposition
    (flow : ExecutableConditionFlow) :
    executableConditionDisposition (executableNegateConditionFlow flow) =
      executableConditionDisposition flow := by
  rfl

theorem executable_v47_not_preserves_feasibility_classification
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (condition : ExecutableHeapCondition) (path : ExecutableHeapPath)
    (flow : ExecutableConditionFlow)
    (executed : executeExecutableHeapCondition proofKernel catalog condition path = some flow) :
    let negated := executableNegateConditionFlow flow
    executeExecutableHeapCondition proofKernel catalog (.not condition) path = some negated ∧
      negated.truePaths = flow.falsePaths ∧
      negated.falsePaths = flow.truePaths ∧
      negated.haltedPaths = flow.haltedPaths ∧
      negated.unmodeledPaths = flow.unmodeledPaths := by
  simp [executeExecutableHeapCondition, executed, executableNegateConditionFlow]

theorem executable_v47_and_not_evaluates_rhs_only_on_original_false_paths
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (left right : ExecutableHeapCondition) (path : ExecutableHeapPath)
    (originalTrue originalFalse : ExecutableHeapPath)
    (rightFlow : ExecutableConditionFlow)
    (leftExecuted : executeExecutableHeapCondition proofKernel catalog left path = some {
      truePaths := [originalTrue]
      falsePaths := [originalFalse]
      haltedPaths := []
      unmodeledPaths := []
    })
    (rightExecuted : executeExecutableHeapCondition proofKernel catalog right originalFalse =
      some rightFlow) :
    executeExecutableHeapCondition proofKernel catalog (.and (.not left) right) path = some {
      truePaths := rightFlow.truePaths
      falsePaths := [originalTrue] ++ rightFlow.falsePaths
      haltedPaths := rightFlow.haltedPaths
      unmodeledPaths := rightFlow.unmodeledPaths
    } := by
  simp [executeExecutableHeapCondition, leftExecuted, executableNegateConditionFlow,
    rightExecuted, executableUnionConditionFlows]

theorem executable_v47_or_not_evaluates_rhs_only_on_original_true_paths
    (proofKernel : ExecutableProofKernel)
    (catalog : ExecutableCompleteSourceClassCatalog)
    (left right : ExecutableHeapCondition) (path : ExecutableHeapPath)
    (originalTrue originalFalse : ExecutableHeapPath)
    (rightFlow : ExecutableConditionFlow)
    (leftExecuted : executeExecutableHeapCondition proofKernel catalog left path = some {
      truePaths := [originalTrue]
      falsePaths := [originalFalse]
      haltedPaths := []
      unmodeledPaths := []
    })
    (rightExecuted : executeExecutableHeapCondition proofKernel catalog right originalTrue =
      some rightFlow) :
    executeExecutableHeapCondition proofKernel catalog (.or (.not left) right) path = some {
      truePaths := [originalFalse] ++ rightFlow.truePaths
      falsePaths := rightFlow.falsePaths
      haltedPaths := rightFlow.haltedPaths
      unmodeledPaths := rightFlow.unmodeledPaths
    } := by
  simp [executeExecutableHeapCondition, leftExecuted, executableNegateConditionFlow,
    rightExecuted, executableUnionConditionFlows]

/-!
## Live ordinary-instance-method `if` wrapper

The recursive `ExecutableHeapStmt` executor above provides the state machine used by the live
ordinary-instance-method frontend: guarded branch construction, path-local locals/heap/mask,
normal/returned/halted status, typed source effects, complete path retention, and postcondition instances on
actual exits.  This section adds the missing method-entry boundary instead of defining a second
path executor.

The accepted IR method is deliberately narrow: a nonoptional verified-source receiver, distinct
well-typed `bool`/`int` or verified-source nominal parameters, Boolean Requires assumptions and
entry obligations, a Unit/Bool/Int result, and at least one structural `if`/`isinstance` statement.
Its body has a smaller source-instance statement algebra that constructs the existing executable
statements while binding every field effect to the method receiver. Calls, construction,
predicate actions, checked-external/dynamic effects, exceptional outcomes, Python descriptors,
nominal returns, and unsupported RHS expressions have no constructor and must refuse.

This proves only the reusable IR composition. Python-AST correspondence, recursive collection of
the method's complete direct-self write set, selected-summary truth, and proof-kernel dispositions
remain frontend obligations.
-/

def executableOrdinaryMethodParameterTypeValid : HeapStatementLocalType -> Bool
  | .scalar .bool | .scalar .int => true
  | .nominal nominal =>
      nominal.sourceOwned && heapStatementNominalTypeValidated nominal
  | .nullOnly | .opaqueObject | .scalar _ => false

def executableOrdinaryMethodBindingValid (binding : HeapStatementLocal) : Bool :=
  !binding.name.isEmpty &&
    executableOrdinaryMethodParameterTypeValid binding.valueType &&
    inferSort binding.value == some (heapStatementLocalTypeSort binding.valueType)

structure ExecutableOrdinaryMethodExpr where
  value : Term
  readObligations : List Term
  readDisposition : ExecutableProofDisposition

structure ExecutableOrdinaryMethodSelfFieldWrite where
  field : String
  fieldType : HeapStatementLocalType
  value : ExecutableOrdinaryMethodExpr
  valueType : HeapStatementLocalType
  nominalEvidence : GuardedFieldWriteNominalEvidence
  framedFields : List ExecutableHeapFieldLayout
  permissionDisposition : ExecutableProofDisposition

inductive ExecutableOrdinaryMethodStmt where
  | pass
  | assertion (condition : ExecutableOrdinaryMethodExpr)
  | assignScalar (name : String) (value : ExecutableOrdinaryMethodExpr) (sort : ValueSort)
  | selfFieldWrite (write : ExecutableOrdinaryMethodSelfFieldWrite)
  | ifThenElse (condition : ExecutableOrdinaryMethodExpr)
      (thenBody elseBody : List ExecutableOrdinaryMethodStmt)
  | returnScalar (value : ExecutableOrdinaryMethodExpr)

def executeExecutableOrdinaryMethodExpr
    (expression : ExecutableOrdinaryMethodExpr) (path : ExecutableHeapPath) :
    Option ExecutableHeapPath :=
  match path.status with
  | .returned _ | .halted _ => some path
  | .normal =>
      if !executableTermsAreBoolean expression.readObligations then none
      else
        match expression.readDisposition with
        | .unresolved => none
        | .refuted failed => some (executableHaltPath path
            expression.readObligations failed)
        | .proved => some { path with state := { path.state with
            obligations := path.state.obligations ++ expression.readObligations }}

theorem executable_ordinary_method_refuted_read_halts_before_use
    (expression : ExecutableOrdinaryMethodExpr) (path : ExecutableHeapPath)
    (failed : Term)
    (normal : path.status = .normal)
    (typed : executableTermsAreBoolean expression.readObligations = true)
    (refuted : expression.readDisposition = .refuted failed) :
    executeExecutableOrdinaryMethodExpr expression path =
      some (executableHaltPath path expression.readObligations failed) := by
  simp [executeExecutableOrdinaryMethodExpr, normal, typed, refuted]

theorem executable_ordinary_method_proved_read_appends_exact_obligations
    (expression : ExecutableOrdinaryMethodExpr) (path checked : ExecutableHeapPath)
    (normal : path.status = .normal)
    (typed : executableTermsAreBoolean expression.readObligations = true)
    (proved : expression.readDisposition = .proved)
    (checkedEq : checked = { path with state := { path.state with
      obligations := path.state.obligations ++ expression.readObligations }}) :
    executeExecutableOrdinaryMethodExpr expression path = some checked := by
  subst checked
  simp [executeExecutableOrdinaryMethodExpr, normal, typed, proved]

mutual

  def executableOrdinaryMethodStmtContainsConditional : ExecutableOrdinaryMethodStmt -> Bool
    | .ifThenElse _ _ _ => true
    | _ => false

  def executableOrdinaryMethodBlockContainsConditional :
      List ExecutableOrdinaryMethodStmt -> Bool
    | [] => false
    | statement :: rest =>
        executableOrdinaryMethodStmtContainsConditional statement ||
          executableOrdinaryMethodBlockContainsConditional rest

  def executeExecutableOrdinaryMethodStmt
      (receiver : HeapStatementLocal) (declaredSort : ValueSort)
      (statement : ExecutableOrdinaryMethodStmt) (path : ExecutableHeapPath) :
      Option (List ExecutableHeapPath) :=
    match path.status with
    | .returned _ | .halted _ => some [path]
    | .normal =>
        match statement with
        | .pass => some [path]
        | .assertion condition =>
            match executeExecutableOrdinaryMethodExpr condition path with
            | none => none
            | some checked =>
                match checked.status with
                | .halted _ => some [checked]
                | .returned _ => none
                | .normal => executeExecutableHeapStmt declaredSort
                    (.assertion condition.value) checked
        | .assignScalar name value sort =>
            if sort != .bool && sort != .int then none
            else
              match executeExecutableOrdinaryMethodExpr value path with
              | none => none
              | some checked =>
                  match checked.status with
                  | .halted _ => some [checked]
                  | .returned _ => none
                  | .normal => executeExecutableHeapStmt declaredSort
                      (.assignLocal name value.value (.scalar sort)) checked
        | .selfFieldWrite write =>
            match write.fieldType with
            | .scalar .bool | .scalar .int =>
              match executeExecutableOrdinaryMethodExpr write.value path with
              | none => none
              | some checked =>
                  match checked.status with
                  | .halted _ => some [checked]
                  | .returned _ => none
                  | .normal => executeExecutableHeapStmt declaredSort
                      (.effect (.sourceFieldWrite {
                        receiver := receiver.value
                        receiverType := receiver.valueType
                        field := write.field
                        fieldType := write.fieldType
                        value := write.value.value
                        valueType := write.valueType
                        nominalEvidence := write.nominalEvidence
                        framedFields := write.framedFields
                        permissionDisposition := write.permissionDisposition
                      })) checked
            | _ => none
        | .ifThenElse condition thenBody elseBody =>
            match executeExecutableOrdinaryMethodExpr condition path with
            | none => none
            | some checked =>
                match checked.status with
                | .halted _ => some [checked]
                | .returned _ => none
                | .normal =>
                    match executableSplitPath condition.value checked with
                    | none => none
                    | some (thenPath, elsePath) =>
                        match executeExecutableOrdinaryMethodBlock receiver declaredSort
                            thenBody [thenPath],
                            executeExecutableOrdinaryMethodBlock receiver declaredSort
                              elseBody [elsePath] with
                        | some thenPaths, some elsePaths =>
                            some (thenPaths ++ elsePaths)
                        | _, _ => none
        | .returnScalar value =>
            match executeExecutableOrdinaryMethodExpr value path with
            | none => none
            | some checked =>
                match checked.status with
                | .halted _ => some [checked]
                | .returned _ => none
                | .normal => executeExecutableHeapStmt declaredSort
                    (.returnValue value.value) checked

  def executeExecutableOrdinaryMethodBlock
      (receiver : HeapStatementLocal) (declaredSort : ValueSort)
      (statements : List ExecutableOrdinaryMethodStmt)
      (paths : List ExecutableHeapPath) : Option (List ExecutableHeapPath) :=
    match statements with
    | [] => some paths
    | statement :: rest =>
        match paths.mapM
            (executeExecutableOrdinaryMethodStmt receiver declaredSort statement) with
        | none => none
        | some nested =>
            executeExecutableOrdinaryMethodBlock receiver declaredSort rest nested.flatten

end

structure ExecutableOrdinaryMethodIf where
  receiver : HeapStatementLocal
  parameters : List HeapStatementLocal
  preconditionAssumptions : List Term
  entryObligations : List Term
  declaredSort : ValueSort
  body : List ExecutableOrdinaryMethodStmt
  postconditions : List ExecutableHeapPostcondition
  sourceLine : Nat

def executableOrdinaryMethodLocalNames
    (method : ExecutableOrdinaryMethodIf) : List String :=
  method.receiver.name :: method.parameters.map (fun parameter => parameter.name)

def executableOrdinaryMethodEntryValid
    (method : ExecutableOrdinaryMethodIf) : Bool :=
  let names := executableOrdinaryMethodLocalNames method
  executableSourceReceiverTypeValid method.receiver.valueType &&
    inferSort method.receiver.value == some .reference &&
    method.parameters.all executableOrdinaryMethodBindingValid &&
    names.eraseDups.length == names.length &&
    executableTermsAreBoolean method.preconditionAssumptions &&
    executableTermsAreBoolean method.entryObligations &&
    heapV43ReturnSortSupported method.declaredSort &&
    executableOrdinaryMethodBlockContainsConditional method.body &&
    true

def executableOrdinaryMethodEntry
    (method : ExecutableOrdinaryMethodIf) : Option ExecutableHeapPath :=
  if executableOrdinaryMethodEntryValid method then some {
    guard := .boolLiteral true
    state := {
      environment := method.receiver :: method.parameters
      heap := 0
      mask := 0
      assumptions := method.preconditionAssumptions
      obligations := method.entryObligations
    }
    status := .normal
  } else none

def executeExecutableOrdinaryMethodIf
    (method : ExecutableOrdinaryMethodIf) : Option (List ExecutableHeapFinalPath) :=
  match executableOrdinaryMethodEntry method with
  | none => none
  | some entry =>
      match executeExecutableOrdinaryMethodBlock method.receiver method.declaredSort
          method.body [entry] with
      | none => none
      | some paths => paths.mapM (finalizeExecutableHeapPath {
            declaredSort := method.declaredSort
            body := []
            postconditions := method.postconditions
            sourceLine := method.sourceLine
          })

theorem executable_ordinary_method_entry_preserves_bound_contract_state
    (method : ExecutableOrdinaryMethodIf) (entry : ExecutableHeapPath)
    (accepted : executableOrdinaryMethodEntry method = some entry) :
    entry.guard = .boolLiteral true ∧
      entry.state.heap = 0 ∧ entry.state.mask = 0 ∧
      entry.state.assumptions = method.preconditionAssumptions ∧
      entry.state.obligations = method.entryObligations ∧
      entry.status = .normal := by
  unfold executableOrdinaryMethodEntry at accepted
  split at accepted
  · cases accepted
    simp
  · contradiction

theorem executable_ordinary_method_uses_the_authoritative_path_finalizer
    (method : ExecutableOrdinaryMethodIf) (entry : ExecutableHeapPath)
    (paths : List ExecutableHeapPath)
    (accepted : executableOrdinaryMethodEntry method = some entry)
    (executed : executeExecutableOrdinaryMethodBlock method.receiver method.declaredSort
      method.body [entry] = some paths) :
    executeExecutableOrdinaryMethodIf method = paths.mapM (finalizeExecutableHeapPath {
      declaredSort := method.declaredSort
      body := []
      postconditions := method.postconditions
      sourceLine := method.sourceLine
    }) := by
  simp [executeExecutableOrdinaryMethodIf, accepted, executed]

theorem executable_ordinary_method_external_receiver_refuses
    (method : ExecutableOrdinaryMethodIf) (nominal : HeapStatementNominalType)
    (external : nominal.sourceOwned = false)
    (receiverType : method.receiver.valueType = .nominal nominal) :
    executableOrdinaryMethodEntry method = none := by
  unfold executableOrdinaryMethodEntry
  simp [executableOrdinaryMethodEntryValid, executableSourceReceiverTypeValid,
    receiverType, external]

theorem executable_ordinary_method_without_conditional_refuses
    (method : ExecutableOrdinaryMethodIf)
    (noConditional : executableOrdinaryMethodBlockContainsConditional method.body = false) :
    executableOrdinaryMethodEntry method = none := by
  unfold executableOrdinaryMethodEntry
  simp [executableOrdinaryMethodEntryValid, noConditional]

theorem executable_ordinary_method_duplicate_binding_refuses
    (method : ExecutableOrdinaryMethodIf)
    (duplicate : ¬(executableOrdinaryMethodLocalNames method).eraseDups.length =
      (executableOrdinaryMethodLocalNames method).length) :
    executableOrdinaryMethodEntry method = none := by
  unfold executableOrdinaryMethodEntry
  simp [executableOrdinaryMethodEntryValid, duplicate]

theorem executable_ordinary_method_self_write_binds_exact_receiver
    (receiver : HeapStatementLocal) (write : ExecutableOrdinaryMethodSelfFieldWrite) :
    ({ receiver := receiver.value
       receiverType := receiver.valueType
       field := write.field
       fieldType := write.fieldType
       value := write.value.value
       valueType := write.valueType
       nominalEvidence := write.nominalEvidence
       framedFields := write.framedFields
       permissionDisposition := write.permissionDisposition } :
      ExecutableSourceFieldWriteEffect).receiver = receiver.value := by
  rfl

theorem executable_ordinary_method_reference_result_entry_refuses
    (method : ExecutableOrdinaryMethodIf)
    (reference : method.declaredSort = .reference) :
    executableOrdinaryMethodEntry method = none := by
  unfold executableOrdinaryMethodEntry
  simp [executableOrdinaryMethodEntryValid, reference, heapV43ReturnSortSupported]

/-!
## Bounded terminal constructor `if`

This is the executable IR for the first method/constructor statement-`if` tranche.  The
shipped frontend instantiates it only for a sequence of top-level constructor `if` statements
after an already-checked linear prefix; each branch may contain direct `self.field = rhs`,
`pass`, or another constructor `if`.  There is no IR
constructor for calls, field reads, property access, mutation of another receiver, `return`,
or an effect after the terminal top-level `if`, so those Python shapes must refuse before
this semantics is entered.

The frontend must prove that the supplied layout is the complete source-owned constructor
layout and that each `initializeSelfField` came from a direct write to the bound receiver.
The definitions below do not claim to prove Python-AST correspondence.  After that boundary,
however, branch paths, heaps, masks, initialized-field sets, permission obligations, the
complete path list, and per-exit postconditions are constructed rather than vouched for by a
summary witness.
-/

def executableConstructorIfFieldTypeSupported : HeapStatementLocalType -> Bool
  | .scalar .bool | .scalar .int | .opaqueObject => true
  | _ => false

structure ExecutableConstructorIfField where
  name : String
  type : HeapStatementLocalType

def executableConstructorIfLayoutValid
    (fields : List ExecutableConstructorIfField) : Bool :=
  fields.all (fun field =>
    !field.name.isEmpty && executableConstructorIfFieldTypeSupported field.type) &&
    (fields.map (fun field => field.name)).eraseDups.length == fields.length

def executableConstructorIfLookupField
    (fields : List ExecutableConstructorIfField) (name : String) :
    Option ExecutableConstructorIfField :=
  fields.find? (fun field => field.name == name)

inductive ExecutableConstructorIfRhs where
  | readFreeScalar (value : Term)
  | local (name : String)
  | freshOpaqueObject (allocationName : String)
  | unsupported

structure ExecutableConstructorIfResolvedRhs where
  value : Term
  type : HeapStatementLocalType
  assumptions : List Term

def executableConstructorIfResolveRhs
    (locals : HeapStatementEnvironment) : ExecutableConstructorIfRhs ->
    Option ExecutableConstructorIfResolvedRhs
  | .readFreeScalar value =>
      if !executableReadFreeScalarTerm value then none
      else
        match inferSort value with
        | some .bool => some { value, type := .scalar .bool, assumptions := [] }
        | some .int => some { value, type := .scalar .int, assumptions := [] }
        | _ => none
  | .local name =>
      match executableLookupLocal locals name with
      | none => none
      | some binding =>
          if !executableConstructorIfFieldTypeSupported binding.valueType ||
              inferSort binding.value != some (heapStatementLocalTypeSort binding.valueType)
          then none
          else some { value := binding.value, type := binding.valueType, assumptions := [] }
  | .freshOpaqueObject allocationName =>
      if allocationName.isEmpty then none
      else
        let value := Term.nominalReference allocationName "object"
        some {
          value
          type := .opaqueObject
          assumptions := [.not (.equal value .nullReference)]
        }
  | .unsupported => none

def executableConstructorIfTypesCompatible
    (fieldType rhsType : HeapStatementLocalType) : Bool :=
  match fieldType, rhsType with
  | .scalar fieldSort, .scalar rhsSort => fieldSort == rhsSort
  | .opaqueObject, .opaqueObject => true
  | _, _ => false

def executableConstructorIfCoerce
    (_fieldType _rhsType : HeapStatementLocalType) (value : Term) : Term :=
  value

structure ExecutableConstructorIfState where
  locals : HeapStatementEnvironment
  heap : Nat
  mask : Nat
  assumptions : List Term
  obligations : List Term
  initializedFields : List String

inductive ExecutableConstructorIfPathStatus where
  | normal
  | halted (failedObligation : Term)

structure ExecutableConstructorIfPath where
  guard : Term
  state : ExecutableConstructorIfState
  status : ExecutableConstructorIfPathStatus

def executableConstructorIfRecordInitialized
    (field : String) (initialized : List String) : List String :=
  if initialized.contains field then initialized else field :: initialized

def executableConstructorIfAllFieldsInitialized
    (fields : List ExecutableConstructorIfField) (initialized : List String) : Bool :=
  fields.all (fun field => initialized.contains field.name)

def executableConstructorIfFrameFacts
    (fields : List ExecutableConstructorIfField) (written : String)
    (preHeap postHeap : Nat) (self : Term) : List Term :=
  fields.filterMap (fun field =>
    if field.name == written then none
    else some (.equal
      (.fieldRead postHeap self field.name (heapStatementLocalTypeSort field.type))
      (.fieldRead preHeap self field.name (heapStatementLocalTypeSort field.type))))

inductive ExecutableConstructorIfStmt where
  | pass
  | initializeSelfField
      (fieldName : String)
      (rhs : ExecutableConstructorIfRhs)
  | ifThenElse (condition : Term)
      (thenBody elseBody : List ExecutableConstructorIfStmt)

mutual

  def executeConstructorIfStmt
      (self : Term) (fields : List ExecutableConstructorIfField)
      (statement : ExecutableConstructorIfStmt)
      (path : ExecutableConstructorIfPath) :
      Option (List ExecutableConstructorIfPath) :=
    match path.status with
    | .halted _ => some [path]
    | .normal =>
        match statement with
        | .pass => some [path]
        | .initializeSelfField fieldName rhs =>
            match executableConstructorIfLookupField fields fieldName,
                executableConstructorIfResolveRhs path.state.locals rhs with
            | some field, some resolved =>
                if inferSort self != some .reference ||
                    !executableConstructorIfTypesCompatible field.type resolved.type
                then none
                else
                  let value := executableConstructorIfCoerce
                    field.type resolved.type resolved.value
                  if inferSort value != some (heapStatementLocalTypeSort field.type) then none
                  else
                    let permission := Term.permissionAtLeast
                      path.state.mask self field.name 1 1
                    let postHeap := path.state.heap + 1
                    let writeFact := Term.equal
                      (.fieldRead postHeap self field.name
                        (heapStatementLocalTypeSort field.type)) value
                    some [{ path with state := {
                      path.state with
                        heap := postHeap
                        assumptions := path.state.assumptions ++ resolved.assumptions ++
                          [writeFact] ++ executableConstructorIfFrameFacts
                            fields field.name path.state.heap postHeap self
                        obligations := path.state.obligations ++ [permission]
                        initializedFields := executableConstructorIfRecordInitialized
                          field.name path.state.initializedFields
                    }}]
            | _, _ => none
        | .ifThenElse condition thenBody elseBody =>
            if !executableReadFreeScalarTerm condition || inferSort condition != some .bool
            then none
            else
              let thenPath : ExecutableConstructorIfPath := {
                path with
                  guard := .and [path.guard, condition]
                  state := { path.state with
                    assumptions := path.state.assumptions ++ [condition] }
              }
              let elsePath : ExecutableConstructorIfPath := {
                path with
                  guard := .and [path.guard, .not condition]
                  state := { path.state with
                    assumptions := path.state.assumptions ++ [.not condition] }
              }
              match executeConstructorIfBlock self fields thenBody [thenPath],
                  executeConstructorIfBlock self fields elseBody [elsePath] with
              | some thenPaths, some elsePaths =>
                  some (thenPaths ++ elsePaths)
              | _, _ => none

  def executeConstructorIfBlock
      (self : Term) (fields : List ExecutableConstructorIfField)
      (statements : List ExecutableConstructorIfStmt)
      (paths : List ExecutableConstructorIfPath) :
      Option (List ExecutableConstructorIfPath) :=
    match statements with
    | [] => some paths
    | statement :: rest =>
        match paths.mapM (executeConstructorIfStmt self fields statement) with
        | none => none
        | some nestedPaths =>
            executeConstructorIfBlock self fields rest nestedPaths.flatten

end

abbrev ExecutableConstructorIfPostcondition := Term -> Nat -> Nat -> Term

structure ExecutableConstructorIfClause where
  condition : Term
  thenBody : List ExecutableConstructorIfStmt
  elseBody : List ExecutableConstructorIfStmt

def executableConstructorIfClauseStatement
    (clause : ExecutableConstructorIfClause) : ExecutableConstructorIfStmt :=
  .ifThenElse clause.condition clause.thenBody clause.elseBody

def executeConstructorIfClauses
    (self : Term) (fields : List ExecutableConstructorIfField)
    (clauses : List ExecutableConstructorIfClause)
    (paths : List ExecutableConstructorIfPath) :
    Option (List ExecutableConstructorIfPath) :=
  executeConstructorIfBlock self fields
    (clauses.map executableConstructorIfClauseStatement) paths

structure ExecutableSequentialConstructorIf where
  self : Term
  className : String
  fields : List ExecutableConstructorIfField
  clauses : List ExecutableConstructorIfClause
  postconditions : List ExecutableConstructorIfPostcondition
  permissionPostconditionFields : List String
  sourceLine : Nat

structure ExecutableConstructorIfExit where
  path : ExecutableConstructorIfPath
  postconditionObligations : List Term
  sourceLine : Nat

inductive ExecutableConstructorIfFinalPath where
  | completed (exit : ExecutableConstructorIfExit)
  | halted (path : ExecutableConstructorIfPath)

def executableConstructorIfInstantiatePostconditions
    (postconditions : List ExecutableConstructorIfPostcondition)
    (path : ExecutableConstructorIfPath) : List Term :=
  postconditions.map (fun postcondition =>
    .implies path.guard (postcondition .unitLiteral path.state.heap path.state.mask))

def executableConstructorIfMissingFields
    (fields : List ExecutableConstructorIfField) (initialized : List String) : List String :=
  fields.filterMap (fun field =>
    if initialized.contains field.name then none else some field.name)

def executableConstructorIfMissingPermissionObligations
    (missing : List String) (path : ExecutableConstructorIfPath) : List Term :=
  missing.map (fun _ => .implies path.guard (.boolLiteral false))

def finalizeConstructorIfPath
    (function : ExecutableSequentialConstructorIf)
    (path : ExecutableConstructorIfPath) : Option ExecutableConstructorIfFinalPath :=
  match path.status with
  | .halted _ => some (.halted path)
  | .normal =>
      let missing := executableConstructorIfMissingFields
        function.fields path.state.initializedFields
      if !missing.all (fun field => function.permissionPostconditionFields.contains field)
      then none
      else
        let obligations :=
          executableConstructorIfInstantiatePostconditions function.postconditions path ++
            executableConstructorIfMissingPermissionObligations missing path
        if !executableTermsAreBoolean obligations then none
        else some (.completed {
          path := { path with state := { path.state with
            obligations := path.state.obligations ++ obligations }}
          postconditionObligations := obligations
          sourceLine := function.sourceLine
        })

def executeTerminalConstructorIf
    (function : ExecutableSequentialConstructorIf)
    (entry : ExecutableConstructorIfPath) :
    Option (List ExecutableConstructorIfFinalPath) :=
  if inferSort function.self != some .reference || function.className.isEmpty ||
      !executableConstructorIfLayoutValid function.fields ||
      function.clauses.isEmpty ||
      !function.permissionPostconditionFields.all (fun field =>
        (executableConstructorIfLookupField function.fields field).isSome) ||
      inferSort entry.guard != some .bool
  then none
  else
    match entry.status with
    | .halted _ => none
    | .normal =>
        match executeConstructorIfClauses function.self function.fields
            function.clauses [entry] with
        | some paths => paths.mapM (finalizeConstructorIfPath function)
        | none => none

theorem executable_constructor_if_unsupported_rhs_refuses
    (locals : HeapStatementEnvironment) :
    executableConstructorIfResolveRhs locals .unsupported = none := by
  rfl

theorem executable_constructor_if_bool_does_not_promote_to_int_field :
    executableConstructorIfTypesCompatible (.scalar .int) (.scalar .bool) = false := by
  rfl

theorem executable_constructor_if_fresh_object_is_nonnull_opaque
    (locals : HeapStatementEnvironment) (allocationName : String)
    (nonempty : allocationName.isEmpty = false) :
    executableConstructorIfResolveRhs locals (.freshOpaqueObject allocationName) = some {
      value := .nominalReference allocationName "object"
      type := .opaqueObject
      assumptions := [.not (.equal
        (.nominalReference allocationName "object") .nullReference)]
    } := by
  simp [executableConstructorIfResolveRhs, nonempty]

theorem executable_constructor_if_recorded_field_is_initialized
    (field : String) (initialized : List String) :
    field ∈ executableConstructorIfRecordInitialized field initialized := by
  unfold executableConstructorIfRecordInitialized
  split <;> simp_all

theorem executable_constructor_if_promised_missing_field_adds_guarded_false_vc
    (missing : List String) (path : ExecutableConstructorIfPath) (field : String)
    (member : field ∈ missing) :
    .implies path.guard (.boolLiteral false) ∈
      executableConstructorIfMissingPermissionObligations missing path := by
  simp only [executableConstructorIfMissingPermissionObligations, List.mem_map]
  exact ⟨field, member, trivial⟩

theorem executable_constructor_if_split_preserves_path_local_versions
    (path : ExecutableConstructorIfPath) (condition : Term) :
    let thenPath : ExecutableConstructorIfPath := {
      path with
        guard := .and [path.guard, condition]
        state := { path.state with
          assumptions := path.state.assumptions ++ [condition] }
    }
    let elsePath : ExecutableConstructorIfPath := {
      path with
        guard := .and [path.guard, .not condition]
        state := { path.state with
          assumptions := path.state.assumptions ++ [.not condition] }
    }
    thenPath.state.heap = path.state.heap &&
      thenPath.state.mask = path.state.mask &&
      thenPath.state.initializedFields = path.state.initializedFields &&
      elsePath.state.heap = path.state.heap &&
      elsePath.state.mask = path.state.mask &&
      elsePath.state.initializedFields = path.state.initializedFields := by
  simp

theorem executable_constructor_if_write_advances_and_records_field
    (self : Term) (fields : List ExecutableConstructorIfField)
    (path : ExecutableConstructorIfPath)
    (fieldName : String) (rhs : ExecutableConstructorIfRhs)
    (field : ExecutableConstructorIfField)
    (resolved : ExecutableConstructorIfResolvedRhs)
    (normal : path.status = .normal)
    (foundField : executableConstructorIfLookupField fields fieldName = some field)
    (foundRhs : executableConstructorIfResolveRhs path.state.locals rhs = some resolved)
    (selfTyped : (inferSort self != some .reference) = false)
    (compatible : executableConstructorIfTypesCompatible field.type resolved.type = true)
    (valueTyped : (inferSort (executableConstructorIfCoerce
      field.type resolved.type resolved.value) !=
        some (heapStatementLocalTypeSort field.type)) = false) :
    let value := executableConstructorIfCoerce field.type resolved.type resolved.value
    let postHeap := path.state.heap + 1
    executeConstructorIfStmt self fields
      (.initializeSelfField fieldName rhs) path = some [{
        path with state := {
          path.state with
            heap := postHeap
            assumptions := path.state.assumptions ++ resolved.assumptions ++
              [.equal (.fieldRead postHeap self field.name
                (heapStatementLocalTypeSort field.type)) value] ++
              executableConstructorIfFrameFacts fields field.name
                path.state.heap postHeap self
            obligations := path.state.obligations ++
              [.permissionAtLeast path.state.mask self field.name 1 1]
            initializedFields := executableConstructorIfRecordInitialized
              field.name path.state.initializedFields
        }
      }] := by
  simp [executeConstructorIfStmt, normal, foundField, foundRhs, selfTyped, compatible,
    valueTyped]

theorem executable_constructor_if_halted_path_absorbs_later_branch_statement
    (self : Term) (fields : List ExecutableConstructorIfField)
    (statement : ExecutableConstructorIfStmt)
    (path : ExecutableConstructorIfPath) (failed : Term)
    (halted : path.status = .halted failed) :
    executeConstructorIfStmt self fields statement path = some [path] := by
  cases statement <;> simp [executeConstructorIfStmt, halted]

theorem executable_constructor_nested_if_preserves_disjoint_exit_lists
    (self : Term) (fields : List ExecutableConstructorIfField)
    (condition : Term)
    (thenBody elseBody : List ExecutableConstructorIfStmt)
    (path : ExecutableConstructorIfPath)
    (thenPaths elsePaths : List ExecutableConstructorIfPath)
    (normal : path.status = .normal)
    (readFree : executableReadFreeScalarTerm condition = true)
    (typed : (inferSort condition != some .bool) = false)
    (thenExecuted : executeConstructorIfBlock self fields thenBody [{
      guard := .and [path.guard, condition]
      state := { path.state with
        assumptions := path.state.assumptions ++ [condition] }
      status := .normal
    }] = some thenPaths)
    (elseExecuted : executeConstructorIfBlock self fields elseBody [{
      guard := .and [path.guard, .not condition]
      state := { path.state with
        assumptions := path.state.assumptions ++ [.not condition] }
      status := .normal
    }] = some elsePaths) :
    executeConstructorIfStmt self fields
      (.ifThenElse condition thenBody elseBody) path =
        some (thenPaths ++ elsePaths) := by
  simp [executeConstructorIfStmt, normal, readFree, typed, thenExecuted, elseExecuted]

theorem executable_constructor_if_unpromised_missing_field_refuses_exit
    (function : ExecutableSequentialConstructorIf)
    (path : ExecutableConstructorIfPath)
    (normal : path.status = .normal)
    (unpromised : ¬∀ field,
      field ∈ executableConstructorIfMissingFields
        function.fields path.state.initializedFields ->
      field ∈ function.permissionPostconditionFields) :
    finalizeConstructorIfPath function path = none := by
  simp [finalizeConstructorIfPath, normal, unpromised]

theorem executable_constructor_if_halted_exit_gets_no_postconditions
    (function : ExecutableSequentialConstructorIf)
    (path : ExecutableConstructorIfPath) (failed : Term)
    (halted : path.status = .halted failed) :
    finalizeConstructorIfPath function path = some (.halted path) := by
  simp [finalizeConstructorIfPath, halted]

theorem executable_constructor_if_completed_exit_has_no_unpromised_missing_field
    (function : ExecutableSequentialConstructorIf)
    (path : ExecutableConstructorIfPath)
    (exit : ExecutableConstructorIfExit)
    (completed : finalizeConstructorIfPath function path = some (.completed exit)) :
    ∀ field, field ∈ executableConstructorIfMissingFields
      function.fields path.state.initializedFields ->
        field ∈ function.permissionPostconditionFields := by
  cases statusEq : path.status with
  | halted failed => simp [finalizeConstructorIfPath, statusEq] at completed
  | normal =>
      simp [finalizeConstructorIfPath, statusEq] at completed
      exact completed.1

theorem executable_constructor_if_completed_exit_gets_exact_postconditions
    (function : ExecutableSequentialConstructorIf)
    (path : ExecutableConstructorIfPath)
    (exit : ExecutableConstructorIfExit)
    (completed : finalizeConstructorIfPath function path = some (.completed exit)) :
    exit.postconditionObligations =
      executableConstructorIfInstantiatePostconditions function.postconditions path ++
        executableConstructorIfMissingPermissionObligations
          (executableConstructorIfMissingFields
            function.fields path.state.initializedFields) path := by
  cases statusEq : path.status with
  | halted failed => simp [finalizeConstructorIfPath, statusEq] at completed
  | normal =>
      simp [finalizeConstructorIfPath, statusEq] at completed
      rcases completed with ⟨_, _, rfl⟩
      rfl

end Maledictus
