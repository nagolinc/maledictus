import Maledictus.VC

namespace Maledictus

inductive PrimitiveCallableSort where
  | int
  | bool
  deriving DecidableEq

def PrimitiveCallableSort.toValueSort : PrimitiveCallableSort → ValueSort
  | .int => .int
  | .bool => .bool

structure PrimitiveCallableSignature where
  parameterSorts : List PrimitiveCallableSort
  resultSort : PrimitiveCallableSort
  deriving DecidableEq

structure PrimitiveDirectCall where
  callee : String
  argumentSorts : List PrimitiveCallableSort
  expectedResultSort : PrimitiveCallableSort

structure PrimitiveHeapCallableDeclaration where
  name : String
  signature : PrimitiveCallableSignature
  directCalls : List PrimitiveDirectCall
  directCallTimeGlobals : List String

structure PrimitiveHeapCallableSummary where
  name : String
  signature : PrimitiveCallableSignature
  directCallees : List String
  transitiveCallees : List String
  directCallTimeGlobals : List String
  capturedScalarEnvironment : ModuleEnvironment

abbrev PrimitiveCallableEnvironment := List (String × PrimitiveHeapCallableSummary)

def primitiveCallableLookup :
    PrimitiveCallableEnvironment → String → Option PrimitiveHeapCallableSummary
  | [], _ => none
  | (boundName, summary) :: rest, name =>
      if name = boundName then some summary else primitiveCallableLookup rest name

def primitiveDirectCallMatches
    (call : PrimitiveDirectCall) (signature : PrimitiveCallableSignature) : Prop :=
  call.argumentSorts = signature.parameterSorts ∧
    call.expectedResultSort = signature.resultSort

instance (call : PrimitiveDirectCall) (signature : PrimitiveCallableSignature) :
    Decidable (primitiveDirectCallMatches call signature) := by
  unfold primitiveDirectCallMatches
  infer_instance

def resolvePrimitiveDirectCalls :
    PrimitiveCallableEnvironment → List PrimitiveDirectCall → Option (List String)
  | _, [] => some []
  | availablePrefix, call :: rest =>
      match primitiveCallableLookup availablePrefix call.callee with
      | none => none
      | some calleeSummary =>
          if primitiveDirectCallMatches call calleeSummary.signature
          then
            match resolvePrimitiveDirectCalls availablePrefix rest with
            | none => none
            | some remaining =>
                some (call.callee :: calleeSummary.transitiveCallees ++ remaining)
          else none

def buildPrimitiveHeapCallable
    (availablePrefix : PrimitiveCallableEnvironment)
    (sealedProviderEnvironment : ModuleEnvironment)
    (declaration : PrimitiveHeapCallableDeclaration) :
    Option PrimitiveHeapCallableSummary :=
  if (primitiveCallableLookup availablePrefix declaration.name).isSome
  then none
  else
    match resolvePrimitiveDirectCalls availablePrefix declaration.directCalls with
    | none => none
    | some transitiveCallees =>
        some {
          name := declaration.name
          signature := declaration.signature
          directCallees := declaration.directCalls.map (fun call => call.callee)
          transitiveCallees
          directCallTimeGlobals := declaration.directCallTimeGlobals
          capturedScalarEnvironment := sealedProviderEnvironment
        }

def extendPrimitiveCallablePrefix
    (availablePrefix : PrimitiveCallableEnvironment)
    (sealedProviderEnvironment : ModuleEnvironment)
    (declaration : PrimitiveHeapCallableDeclaration) :
    Option PrimitiveCallableEnvironment :=
  match buildPrimitiveHeapCallable
      availablePrefix sealedProviderEnvironment declaration with
  | none => none
  | some summary => some ((declaration.name, summary) :: availablePrefix)

def executePrimitiveCallableDeclarations :
    PrimitiveCallableEnvironment →
    ModuleEnvironment →
    List PrimitiveHeapCallableDeclaration →
    Option PrimitiveCallableEnvironment
  | availablePrefix, _, [] => some availablePrefix
  | availablePrefix, sealedProviderEnvironment, declaration :: rest =>
      match extendPrimitiveCallablePrefix
          availablePrefix sealedProviderEnvironment declaration with
      | none => none
      | some nextPrefix =>
          executePrimitiveCallableDeclarations nextPrefix sealedProviderEnvironment rest

/-
Python evaluates a function decorator and binds the function in source order, but an ordinary
function body resolves module function names when that body is called.  The prefix executor above
is therefore the right model for module-initializer calls, while a call made after successful
module initialization needs the complete, duplicate-free declaration catalog below.  Every
catalog key and direct-call edge contains its provider identity.  An imported summary therefore
retains the provider-owned callee closure instead of reinterpreting a bare helper name in the
consumer module.  Resolution still checks every direct-call signature and performs a bounded DFS,
so a missing edge, a type mismatch, self recursion, or mutual recursion fails closed rather than
becoming an assumed summary.

The Python frontend remains responsible for translating the real decorator binding, lexical
scope, expressions, and statements into this IR.  In particular, a qualified edge is admissible
only after source name resolution; the executable lexical check below independently rejects both
parameter shadowing and every local assigned anywhere in the complete modeled body.  These
definitions prove the IR execution and summary algebra, not Python-AST correspondence.
-/
structure PrimitiveCallableIdentity where
  provider : String
  name : String
  deriving DecidableEq

structure QualifiedPrimitiveDirectCall where
  sourceName : String
  callee : PrimitiveCallableIdentity
  argumentSorts : List PrimitiveCallableSort
  expectedResultSort : PrimitiveCallableSort

def qualifiedPrimitiveDirectCallMatches
    (call : QualifiedPrimitiveDirectCall)
    (signature : PrimitiveCallableSignature) : Prop :=
  call.argumentSorts = signature.parameterSorts ∧
    call.expectedResultSort = signature.resultSort

instance (call : QualifiedPrimitiveDirectCall) (signature : PrimitiveCallableSignature) :
    Decidable (qualifiedPrimitiveDirectCallMatches call signature) := by
  unfold qualifiedPrimitiveDirectCallMatches
  infer_instance

mutual

  def primitiveScalarTermReadFree : Term → Bool
    | .boolLiteral _ | .intLiteral _ => true
    | .variable _ .bool | .variable _ .int => true
    | .not value | .negate value => primitiveScalarTermReadFree value
    | .and values | .or values => primitiveScalarTermsReadFree values
    | .implies left right | .equal left right | .less left right | .lessEqual left right |
        .greater left right | .greaterEqual left right | .add left right | .subtract left right |
        .multiply left right =>
        primitiveScalarTermReadFree left && primitiveScalarTermReadFree right
    | .floorDivideByPositive value _ => primitiveScalarTermReadFree value
    | .ite condition thenValue elseValue =>
        primitiveScalarTermReadFree condition &&
          primitiveScalarTermReadFree thenValue && primitiveScalarTermReadFree elseValue
    | _ => false

  def primitiveScalarTermsReadFree : List Term → Bool
    | [] => true
    | value :: rest =>
        primitiveScalarTermReadFree value && primitiveScalarTermsReadFree rest

end

inductive PrimitiveScalarStmt where
  | pass
  | assignLocal (name : String) (value : Term) (sort : PrimitiveCallableSort)
  | returnValue (value : Term)
  | ifThenElse (condition : Term)
      (thenBody elseBody : List PrimitiveScalarStmt)

mutual

  def primitiveScalarStmtAssignedNames : PrimitiveScalarStmt → List String
    | .pass => []
    | .assignLocal name _ _ => [name]
    | .returnValue _ => []
    | .ifThenElse _ thenBody elseBody =>
        primitiveScalarBlockAssignedNames thenBody ++
          primitiveScalarBlockAssignedNames elseBody

  def primitiveScalarBlockAssignedNames : List PrimitiveScalarStmt → List String
    | [] => []
    | statement :: rest =>
        primitiveScalarStmtAssignedNames statement ++
          primitiveScalarBlockAssignedNames rest

end

inductive PrimitiveScalarPathStatus where
  | normal
  | returned (value : Term)

structure PrimitiveScalarPath where
  guard : Term
  environment : ModuleEnvironment
  obligations : List Term
  status : PrimitiveScalarPathStatus

def primitiveCallableResultSort (sort : PrimitiveCallableSort) : ValueSort :=
  sort.toValueSort

def coercePrimitiveScalarValue
    (expected : PrimitiveCallableSort) (value : Term) : Term :=
  match expected with
  | .int =>
      if inferSort value == some .bool
      then .ite value (.intLiteral 1) (.intLiteral 0)
      else value
  | .bool => value

mutual

  def executePrimitiveScalarStmt
      (declaredSort : PrimitiveCallableSort)
      (statement : PrimitiveScalarStmt)
      (path : PrimitiveScalarPath) : Option (List PrimitiveScalarPath) :=
    match path.status with
    | .returned _ => some [path]
    | .normal =>
        match statement with
        | .pass => some [path]
        | .assignLocal name value sort =>
            let coerced := coercePrimitiveScalarValue sort value
            if name.isEmpty || !primitiveScalarTermReadFree value ||
                inferSort coerced != some (primitiveCallableResultSort sort)
            then none
            else some [{ path with
              environment :=
                (name, coerced) :: eraseModuleBinding path.environment name
            }]
        | .returnValue value =>
            let coerced := coercePrimitiveScalarValue declaredSort value
            if primitiveScalarTermReadFree value &&
                inferSort coerced == some (primitiveCallableResultSort declaredSort)
            then some [{ path with status := .returned coerced }]
            else none
        | .ifThenElse condition thenBody elseBody =>
            if !primitiveScalarTermReadFree condition || inferSort condition != some .bool
            then none
            else
              let thenPath : PrimitiveScalarPath := {
                guard := .and [path.guard, condition]
                environment := path.environment
                obligations := path.obligations
                status := .normal
              }
              let elsePath : PrimitiveScalarPath := {
                guard := .and [path.guard, .not condition]
                environment := path.environment
                obligations := path.obligations
                status := .normal
              }
              match executePrimitiveScalarBlock declaredSort thenBody [thenPath],
                  executePrimitiveScalarBlock declaredSort elseBody [elsePath] with
              | some thenPaths, some elsePaths =>
                  some (thenPaths ++ elsePaths)
              | _, _ => none

  def executePrimitiveScalarBlock
      (declaredSort : PrimitiveCallableSort)
      (statements : List PrimitiveScalarStmt)
      (paths : List PrimitiveScalarPath) : Option (List PrimitiveScalarPath) :=
    match statements with
    | [] => some paths
    | statement :: rest =>
        match paths.mapM (executePrimitiveScalarStmt declaredSort statement) with
        | none => none
        | some nestedPaths =>
            executePrimitiveScalarBlock declaredSort rest nestedPaths.flatten

end

inductive PrimitiveScalarExit where
  | returned (path : PrimitiveScalarPath) (value : Term)
  | implicitNoneMismatch (path : PrimitiveScalarPath)

def finalizePrimitiveScalarPath (path : PrimitiveScalarPath) : PrimitiveScalarExit :=
  match path.status with
  | .returned value => .returned path value
  | .normal => .implicitNoneMismatch {
      path with obligations := path.obligations ++ [.not path.guard]
    }

def primitiveScalarExitObligations : PrimitiveScalarExit → List Term
  | .returned path _ | .implicitNoneMismatch path => path.obligations

def executePrimitiveScalarBodyPaths
    (declaredSort : PrimitiveCallableSort)
    (entryEnvironment : ModuleEnvironment)
    (body : List PrimitiveScalarStmt) : Option (List PrimitiveScalarPath) :=
  executePrimitiveScalarBlock declaredSort body [{
    guard := .boolLiteral true
    environment := entryEnvironment
    obligations := []
    status := .normal
  }]

def executeCompletePrimitiveScalarBody
    (declaredSort : PrimitiveCallableSort)
    (entryEnvironment : ModuleEnvironment)
    (body : List PrimitiveScalarStmt) : Option (List PrimitiveScalarExit) :=
  match executePrimitiveScalarBodyPaths declaredSort entryEnvironment body with
  | none => none
  | some paths => some (paths.map finalizePrimitiveScalarPath)

def mergePrimitiveScalarReturnedPaths :
    List PrimitiveScalarPath → Option Term
  | [] => none
  | [path] =>
      match path.status with
      | .returned value => some value
      | .normal => none
  | path :: rest =>
      match path.status, mergePrimitiveScalarReturnedPaths rest with
      | .returned value, some remaining =>
          some (.ite path.guard value remaining)
      | _, _ => none

structure PostInitPrimitiveCallableDeclaration where
  identity : PrimitiveCallableIdentity
  signature : PrimitiveCallableSignature
  parameterNames : List String
  directCalls : List QualifiedPrimitiveDirectCall
  directCallTimeGlobals : List String
  body : List PrimitiveScalarStmt

def postInitPrimitiveDeclarationLexicallyClosed
    (declaration : PostInitPrimitiveCallableDeclaration) : Bool :=
  let lexicalNames :=
    declaration.parameterNames ++ primitiveScalarBlockAssignedNames declaration.body
  declaration.parameterNames.length == declaration.signature.parameterSorts.length &&
    declaration.directCalls.all
      (fun call => !call.sourceName.isEmpty && call.sourceName ∉ lexicalNames)

inductive PrimitiveCallableExecutionPhase where
  | moduleInitialization
  | postInitialization

def primitiveCallableExecutionEnvironment
    (phase : PrimitiveCallableExecutionPhase)
    (currentProvider : String)
    (callee : PrimitiveCallableIdentity)
    (currentModulePrefix sealedProviderEnvironment : ModuleEnvironment) : ModuleEnvironment :=
  match phase with
  | .postInitialization => sealedProviderEnvironment
  | .moduleInitialization =>
      if callee.provider = currentProvider
      then currentModulePrefix
      else sealedProviderEnvironment

abbrev PrimitiveCallableDeclarationCatalog :=
  List (PrimitiveCallableIdentity × PostInitPrimitiveCallableDeclaration)

def primitiveCallableIdentityText (identity : PrimitiveCallableIdentity) : String :=
  identity.provider ++ "." ++ identity.name

def primitiveCallableDeclarationLookup :
    PrimitiveCallableDeclarationCatalog →
    PrimitiveCallableIdentity →
    Option PostInitPrimitiveCallableDeclaration
  | [], _ => none
  | (boundIdentity, declaration) :: rest, identity =>
      if identity = boundIdentity then some declaration
      else primitiveCallableDeclarationLookup rest identity

def collectPrimitiveCallableDeclarationCatalog :
    PrimitiveCallableDeclarationCatalog →
    List PostInitPrimitiveCallableDeclaration →
    Option PrimitiveCallableDeclarationCatalog
  | catalog, [] => some catalog
  | catalog, declaration :: rest =>
      if (primitiveCallableDeclarationLookup catalog declaration.identity).isSome
      then none
      else
        collectPrimitiveCallableDeclarationCatalog
          ((declaration.identity, declaration) :: catalog) rest

def primitiveCallableCatalogCallBudget
    (catalog : PrimitiveCallableDeclarationCatalog) : Nat :=
  catalog.length +
    catalog.foldl (fun total entry => total + entry.2.directCalls.length) 0 + 1

def resolvePostInitPrimitiveCalls
    (catalog : PrimitiveCallableDeclarationCatalog) :
    Nat →
    List PrimitiveCallableIdentity →
    List QualifiedPrimitiveDirectCall →
    Option (List PrimitiveCallableIdentity)
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | fuel + 1, active, call :: rest =>
      if call.callee ∈ active then none
      else
        match primitiveCallableDeclarationLookup catalog call.callee with
        | none => none
        | some calleeDeclaration =>
            if postInitPrimitiveDeclarationLexicallyClosed calleeDeclaration &&
                qualifiedPrimitiveDirectCallMatches call calleeDeclaration.signature then
              match resolvePostInitPrimitiveCalls
                  catalog fuel (call.callee :: active) calleeDeclaration.directCalls with
              | none => none
              | some nestedCallees =>
                  match resolvePostInitPrimitiveCalls catalog fuel active rest with
                  | none => none
                  | some remaining =>
                      some (call.callee :: nestedCallees ++ remaining)
            else none

def buildPostInitPrimitiveHeapCallable
    (catalog : PrimitiveCallableDeclarationCatalog)
    (sealedProviderEnvironment : ModuleEnvironment)
    (identity : PrimitiveCallableIdentity) :
    Option (PrimitiveHeapCallableSummary × List Term) :=
  match primitiveCallableDeclarationLookup catalog identity with
  | none => none
  | some declaration =>
      if !postInitPrimitiveDeclarationLexicallyClosed declaration then none
      else
        match resolvePostInitPrimitiveCalls
            catalog
            (primitiveCallableCatalogCallBudget catalog)
            [identity]
            declaration.directCalls,
          executePrimitiveScalarBodyPaths
            declaration.signature.resultSort sealedProviderEnvironment declaration.body with
        | some transitiveCallees, some paths =>
            match mergePrimitiveScalarReturnedPaths paths with
            | none => none
            | some _resultRelation =>
            some ({
              name := primitiveCallableIdentityText declaration.identity
              signature := declaration.signature
              directCallees := declaration.directCalls.map
                (fun call => primitiveCallableIdentityText call.callee)
              transitiveCallees := transitiveCallees.map primitiveCallableIdentityText
              directCallTimeGlobals := declaration.directCallTimeGlobals
              capturedScalarEnvironment := sealedProviderEnvironment
            }, paths.flatMap (fun path => path.obligations))
        | _, _ => none

def primitiveCallableEntryEnvironment
    (summary : PrimitiveHeapCallableSummary)
    (locallyBoundNames : List String)
    (parameters : ModuleEnvironment) : ModuleEnvironment :=
  functionEntryEnvironment
    summary.capturedScalarEnvironment locallyBoundNames parameters

def collectPrimitiveCallTimeGlobals :
    PrimitiveCallableEnvironment → List String → Option (List String)
  | _, [] => some []
  | callablePrefix, callableName :: rest =>
      match primitiveCallableLookup callablePrefix callableName with
      | none => none
      | some summary =>
          match collectPrimitiveCallTimeGlobals callablePrefix rest with
          | none => none
          | some remaining => some (summary.directCallTimeGlobals ++ remaining)

def firstMissingModuleName : ModuleEnvironment → List String → Option String
  | _, [] => none
  | callTimePrefix, name :: rest =>
      if moduleContains callTimePrefix name = true
      then firstMissingModuleName callTimePrefix rest
      else some name

structure PrimitiveConstructorSummary where
  directPrimitiveCalls : List PrimitiveDirectCall

structure TopLevelConstructorCall where
  outerStatement : Nat
  constructor : PrimitiveConstructorSummary

inductive ConstructorCallFailure where
  | unresolvedOrIllTypedDirectCall
  | unresolvedTransitiveCall
  | undefinedCallTimeGlobal : String → ConstructorCallFailure
  | namespaceExtensionRefused

inductive TopLevelConstructorCallOutcome where
  | succeeded : TopLevelConstructorCallOutcome
  | failed : Nat → ConstructorCallFailure → TopLevelConstructorCallOutcome

def resolveTopLevelConstructorCall
    (callablePrefix : PrimitiveCallableEnvironment)
    (callTimePrefix : ModuleEnvironment)
    (statement : TopLevelConstructorCall) : TopLevelConstructorCallOutcome :=
  match resolvePrimitiveDirectCalls
      callablePrefix statement.constructor.directPrimitiveCalls with
  | none => .failed statement.outerStatement .unresolvedOrIllTypedDirectCall
  | some transitiveCallees =>
      match collectPrimitiveCallTimeGlobals callablePrefix transitiveCallees with
      | none => .failed statement.outerStatement .unresolvedTransitiveCall
      | some requiredGlobals =>
          match firstMissingModuleName callTimePrefix requiredGlobals with
          | none => .succeeded
          | some missingName =>
              .failed statement.outerStatement (.undefinedCallTimeGlobal missingName)

inductive ConstructorDefinednessStatement where
  | scalarBinding : Nat → String → Term → ConstructorDefinednessStatement
  | constructorCall : TopLevelConstructorCall → ConstructorDefinednessStatement

inductive ConstructorDefinednessProgress where
  | running : PassiveModuleNamespace → ConstructorDefinednessProgress
  | halted :
      PassiveModuleNamespace → Nat → ConstructorCallFailure →
        ConstructorDefinednessProgress

def advanceConstructorDefinedness
    (callablePrefix : PrimitiveCallableEnvironment)
    (progress : ConstructorDefinednessProgress)
    (statement : ConstructorDefinednessStatement) : ConstructorDefinednessProgress :=
  match progress with
  | .halted moduleState outerStatement failure =>
      .halted moduleState outerStatement failure
  | .running moduleState =>
      match statement with
      | .scalarBinding outerStatement name value =>
          match advancePassiveNamespace moduleState (.scalarBinding name value) with
          | none => .halted moduleState outerStatement .namespaceExtensionRefused
          | some next => .running next
      | .constructorCall constructorStatement =>
          match resolveTopLevelConstructorCall
              callablePrefix moduleState.scalarBindings constructorStatement with
          | .succeeded => .running moduleState
          | .failed outerStatement failure =>
              .halted moduleState outerStatement failure

def executeConstructorDefinedness :
    PrimitiveCallableEnvironment →
    ConstructorDefinednessProgress →
    List ConstructorDefinednessStatement →
    ConstructorDefinednessProgress
  | _, progress, [] => progress
  | callablePrefix, progress, statement :: rest =>
      executeConstructorDefinedness
        callablePrefix
        (advanceConstructorDefinedness callablePrefix progress statement)
        rest

structure VirtualDispatchCandidate where
  className : String
  requiredGlobal : String
  resultSort : PrimitiveCallableSort
  deriving DecidableEq

def firstUnavailableDispatchTarget :
    ModuleEnvironment -> List VirtualDispatchCandidate -> Option (String × String)
  | _, [] => none
  | callTimePrefix, candidate :: rest =>
      if moduleContains callTimePrefix candidate.requiredGlobal = true
      then firstUnavailableDispatchTarget callTimePrefix rest
      else some (candidate.className, candidate.requiredGlobal)

structure TopLevelVirtualDispatchCall where
  outerStatement : Nat
  sourceFunctionAvailable : Bool
  argumentSubtype : Bool
  constructorEffectFree : Bool
  currentlyDefinedCandidates : List VirtualDispatchCandidate

inductive VirtualDispatchFailure where
  | sourceFunctionUnavailable
  | argumentTypeMismatch
  | constructorEffectsUnsupported
  | undefinedOverrideGlobal : String -> String -> VirtualDispatchFailure
  deriving DecidableEq

inductive TopLevelVirtualDispatchOutcome where
  | succeeded : TopLevelVirtualDispatchOutcome
  | failed : Nat -> VirtualDispatchFailure -> TopLevelVirtualDispatchOutcome
  deriving DecidableEq

def resolveTopLevelVirtualDispatch
    (callTimePrefix : ModuleEnvironment)
    (statement : TopLevelVirtualDispatchCall) : TopLevelVirtualDispatchOutcome :=
  if statement.sourceFunctionAvailable = false then
    .failed statement.outerStatement .sourceFunctionUnavailable
  else if statement.argumentSubtype = false then
    .failed statement.outerStatement .argumentTypeMismatch
  else if statement.constructorEffectFree = false then
    .failed statement.outerStatement .constructorEffectsUnsupported
  else
    match firstUnavailableDispatchTarget
        callTimePrefix statement.currentlyDefinedCandidates with
    | none => .succeeded
    | some (className, globalName) =>
        .failed statement.outerStatement
          (.undefinedOverrideGlobal className globalName)

inductive NominalAnnotationTiming where
  | eager
  | deferred
  deriving DecidableEq

structure NominalFunctionAnnotation where
  className : String
  timing : NominalAnnotationTiming
  deriving DecidableEq

def firstUndefinedEagerAnnotation :
    List String -> List NominalFunctionAnnotation -> Option String
  | _, [] => none
  | definedClasses, annotation :: rest =>
      match annotation.timing with
      | .deferred => firstUndefinedEagerAnnotation definedClasses rest
      | .eager =>
          if annotation.className ∈ definedClasses
          then firstUndefinedEagerAnnotation definedClasses rest
          else some annotation.className

structure OrderedAnnotatedFunctionDeclaration where
  outerStatement : Nat
  annotations : List NominalFunctionAnnotation

inductive OrderedAnnotationOutcome where
  | succeeded : OrderedAnnotationOutcome
  | failed : Nat -> String -> OrderedAnnotationOutcome
  deriving DecidableEq

def resolveOrderedFunctionAnnotations
    (definedClassPrefix : List String)
    (declaration : OrderedAnnotatedFunctionDeclaration) : OrderedAnnotationOutcome :=
  match firstUndefinedEagerAnnotation
      definedClassPrefix declaration.annotations with
  | none => .succeeded
  | some className => .failed declaration.outerStatement className

inductive MethodReceiverKind where
  | instance
  | static
  | class
  deriving DecidableEq

structure TypedMethodCallShape where
  receiverKind : MethodReceiverKind
  explicitArgumentSorts : List PrimitiveCallableSort
  deriving DecidableEq

def runtimeArgumentCount (shape : TypedMethodCallShape) : Nat :=
  match shape.receiverKind with
  | .instance => shape.explicitArgumentSorts.length + 1
  | .static => shape.explicitArgumentSorts.length
  | .class => shape.explicitArgumentSorts.length + 1

def receiverKindsOverrideCompatible
    (base derived : MethodReceiverKind) : Bool :=
  base == derived

inductive ClassQualifiedCallOutcome where
  | succeeded
  | instanceReceiverRequired
  deriving DecidableEq

def resolveClassQualifiedCall
    (receiverKind : MethodReceiverKind) : ClassQualifiedCallOutcome :=
  match receiverKind with
  | .static => .succeeded
  | .class => .succeeded
  | .instance => .instanceReceiverRequired

structure DynamicClassConstruction where
  receiverClass : Term
  resultObject : Term

def dynamicClassConstructionWellTyped
    (construction : DynamicClassConstruction) : Bool :=
  inferSort construction.receiverClass == some .class &&
    inferSort construction.resultObject == some .reference

def dynamicClassConstructionFacts
    (construction : DynamicClassConstruction) : List Term :=
  [
    .equal (.runtimeClass construction.resultObject) construction.receiverClass,
    .classSubtype construction.receiverClass construction.receiverClass
  ]

inductive PredicatePermissionAction where
  | fold
  | unfold
  deriving DecidableEq

structure PredicateBodyPermission where
  receiver : Term
  field : String
  numerator : Nat
  denominator : Nat

structure PredicatePermissionExchange where
  preMask : Nat
  postMask : Nat
  predicate : String
  predicateArguments : List Term
  bodyPermissions : List PredicateBodyPermission

def predicateTokenReceiver (exchange : PredicatePermissionExchange) : Term :=
  .predicateInstance exchange.predicate exchange.predicateArguments

def predicatePermissionLocation (predicate : String) : String :=
  "@predicate:" ++ predicate

def predicateExchangeLocations
    (exchange : PredicatePermissionExchange) : List String :=
  predicatePermissionLocation exchange.predicate ::
    exchange.bodyPermissions.map (fun permission => permission.field)

def fullPermissionTransfer (receiver : Term) : Term × Nat × Nat :=
  (receiver, 1, 1)

def predicateBodyTransfer
    (permission : PredicateBodyPermission) : Term × Nat × Nat :=
  (permission.receiver, permission.numerator, permission.denominator)

def predicateBodyTransfersAt
    (exchange : PredicatePermissionExchange)
    (location : String) : List (Term × Nat × Nat) :=
  (exchange.bodyPermissions.filter (fun permission => permission.field == location)).map
    predicateBodyTransfer

def predicateBodyPermissionValid (permission : PredicateBodyPermission) : Bool :=
  inferSort permission.receiver == some .reference &&
    permission.denominator != 0 &&
    permission.numerator != 0 &&
    permission.numerator <= permission.denominator

def predicateExchangeWellFormed (exchange : PredicatePermissionExchange) : Bool :=
  inferSort (predicateTokenReceiver exchange) == some .reference &&
    !exchange.predicate.isEmpty &&
    exchange.preMask != exchange.postMask &&
    exchange.bodyPermissions.all predicateBodyPermissionValid

def predicateBodyComplementCapacity
    (mask : Nat) (permission : PredicateBodyPermission) : Term :=
  .permissionAtMost
    mask
    permission.receiver
    permission.field
    (permission.denominator - permission.numerator)
    permission.denominator

def predicateFoldedCapacityFacts
    (exchange : PredicatePermissionExchange) (mask : Nat) : List Term :=
  .permissionAtLeast
      mask
      (predicateTokenReceiver exchange)
      (predicatePermissionLocation exchange.predicate)
      1
      1 ::
    exchange.bodyPermissions.map (predicateBodyComplementCapacity mask)

def predicateActionFoldedCapacityFacts
    (action : PredicatePermissionAction)
    (exchange : PredicatePermissionExchange) : List Term :=
  match action with
  | .fold => predicateFoldedCapacityFacts exchange exchange.postMask
  | .unfold => predicateFoldedCapacityFacts exchange exchange.preMask

def predicateExchangeFact
    (action : PredicatePermissionAction)
    (exchange : PredicatePermissionExchange)
    (location : String) : Term :=
  let predicateLocation := predicatePermissionLocation exchange.predicate
  let tokenAmount := fullPermissionTransfer (predicateTokenReceiver exchange)
  let bodyAmounts := predicateBodyTransfersAt exchange location
  match action with
  | .fold =>
      if location == predicateLocation then
        .permissionMaskTransition exchange.preMask exchange.postMask location [] [tokenAmount]
      else
        .permissionMaskTransition exchange.preMask exchange.postMask location bodyAmounts []
  | .unfold =>
      if location == predicateLocation then
        .permissionMaskTransition exchange.preMask exchange.postMask location [tokenAmount] []
      else
        .permissionMaskTransition exchange.preMask exchange.postMask location [] bodyAmounts

def predicateExchangeFacts
    (action : PredicatePermissionAction)
    (exchange : PredicatePermissionExchange) : List Term :=
  (predicateExchangeLocations exchange).map (predicateExchangeFact action exchange)

theorem predicate_permission_location_has_reserved_prefix (predicate : String) :
    predicatePermissionLocation predicate = "@predicate:" ++ predicate := by
  rfl

theorem predicate_exchange_locations_are_action_independent
    (exchange : PredicatePermissionExchange) :
    predicateExchangeLocations exchange =
      predicatePermissionLocation exchange.predicate ::
        exchange.bodyPermissions.map (fun permission => permission.field) := by
  rfl

theorem predicate_token_is_keyed_by_name_and_arguments
    (left right : PredicatePermissionExchange)
    (equalTokens : predicateTokenReceiver left = predicateTokenReceiver right) :
    left.predicate = right.predicate ∧
      left.predicateArguments = right.predicateArguments := by
  exact predicate_instance_name_and_arguments_injective equalTokens

theorem different_predicate_arguments_produce_different_tokens
    (left right : PredicatePermissionExchange)
    (differentArguments : left.predicateArguments ≠ right.predicateArguments) :
    predicateTokenReceiver left ≠ predicateTokenReceiver right := by
  intro equalTokens
  exact differentArguments
    (predicate_token_is_keyed_by_name_and_arguments left right equalTokens).2

theorem valid_predicate_body_permission_is_positive_fraction
    (permission : PredicateBodyPermission)
    (valid : predicateBodyPermissionValid permission = true) :
    inferSort permission.receiver = some .reference ∧
      permission.denominator ≠ 0 ∧
      permission.numerator ≠ 0 ∧
      permission.numerator ≤ permission.denominator := by
  simp [predicateBodyPermissionValid] at valid
  exact ⟨(beq_some_reference_true_iff _).mp valid.1.1.1,
    valid.1.1.2, valid.1.2, valid.2⟩

theorem complement_capacity_is_well_typed_while_folded
    (mask : Nat)
    (permission : PredicateBodyPermission)
    (valid : predicateBodyPermissionValid permission = true) :
    inferSort (predicateBodyComplementCapacity mask permission) = some .bool := by
  have properties := valid_predicate_body_permission_is_positive_fraction permission valid
  simp [predicateBodyComplementCapacity, inferSort, properties.1, properties.2.1,
    Nat.sub_le, instBEqValueSort, valueSortBeq]

theorem every_body_permission_has_folded_complement_capacity
    (exchange : PredicatePermissionExchange)
    (mask : Nat)
    (permission : PredicateBodyPermission)
    (member : permission ∈ exchange.bodyPermissions) :
    predicateBodyComplementCapacity mask permission ∈
      predicateFoldedCapacityFacts exchange mask := by
  apply List.mem_cons_of_mem
  exact List.mem_map_of_mem member

theorem fold_records_capacity_in_post_mask
    (exchange : PredicatePermissionExchange) :
    predicateActionFoldedCapacityFacts .fold exchange =
      predicateFoldedCapacityFacts exchange exchange.postMask := by
  rfl

theorem unfold_requires_capacity_in_pre_mask
    (exchange : PredicatePermissionExchange) :
    predicateActionFoldedCapacityFacts .unfold exchange =
      predicateFoldedCapacityFacts exchange exchange.preMask := by
  rfl

def reversePredicateExchange
    (exchange : PredicatePermissionExchange) : PredicatePermissionExchange :=
  { exchange with preMask := exchange.postMask, postMask := exchange.preMask }

theorem reverse_predicate_exchange_preserves_token
    (exchange : PredicatePermissionExchange) :
    predicateTokenReceiver (reversePredicateExchange exchange) =
      predicateTokenReceiver exchange := by
  cases exchange
  rfl

theorem reverse_predicate_exchange_preserves_body_transfers
    (exchange : PredicatePermissionExchange)
    (location : String) :
    predicateBodyTransfersAt (reversePredicateExchange exchange) location =
      predicateBodyTransfersAt exchange location := by
  cases exchange
  rfl

theorem reverse_predicate_exchange_preserves_locations
    (exchange : PredicatePermissionExchange) :
    predicateExchangeLocations (reversePredicateExchange exchange) =
      predicateExchangeLocations exchange := by
  cases exchange
  rfl

def reversePermissionTransition : Term → Option Term
  | .permissionMaskTransition preMask postMask field consumed produced =>
      some (.permissionMaskTransition postMask preMask field produced consumed)
  | _ => none

theorem folding_then_reversing_has_unfold_transfers
    (exchange : PredicatePermissionExchange)
    (location : String) :
    reversePermissionTransition
        (predicateExchangeFact .fold exchange location) =
      some (predicateExchangeFact .unfold (reversePredicateExchange exchange) location) := by
  by_cases tokenLocation : location = predicatePermissionLocation exchange.predicate <;>
    simp [predicateExchangeFact, reversePredicateExchange, reversePermissionTransition,
      predicateTokenReceiver, predicateBodyTransfersAt, tokenLocation]

theorem unfolding_then_reversing_has_fold_transfers
    (exchange : PredicatePermissionExchange)
    (location : String) :
    reversePermissionTransition
        (predicateExchangeFact .unfold exchange location) =
      some (predicateExchangeFact .fold (reversePredicateExchange exchange) location) := by
  by_cases tokenLocation : location = predicatePermissionLocation exchange.predicate <;>
    simp [predicateExchangeFact, reversePredicateExchange, reversePermissionTransition,
      predicateTokenReceiver, predicateBodyTransfersAt, tokenLocation]

theorem reversing_fold_transfers_for_locations
    (exchange : PredicatePermissionExchange)
    (locations : List String) :
    (locations.map (predicateExchangeFact .fold exchange)).map
        reversePermissionTransition =
      locations.map
        (fun location =>
          some (predicateExchangeFact .unfold (reversePredicateExchange exchange) location)) := by
  induction locations with
  | nil => rfl
  | cons location rest inductionHypothesis =>
      simp [folding_then_reversing_has_unfold_transfers, inductionHypothesis]

theorem reversing_unfold_transfers_for_locations
    (exchange : PredicatePermissionExchange)
    (locations : List String) :
    (locations.map (predicateExchangeFact .unfold exchange)).map
        reversePermissionTransition =
      locations.map
        (fun location =>
          some (predicateExchangeFact .fold (reversePredicateExchange exchange) location)) := by
  induction locations with
  | nil => rfl
  | cons location rest inductionHypothesis =>
      simp [unfolding_then_reversing_has_fold_transfers, inductionHypothesis]

theorem folding_then_reversing_all_exchange_facts_is_unfolding
    (exchange : PredicatePermissionExchange) :
    (predicateExchangeFacts .fold exchange).map reversePermissionTransition =
      (predicateExchangeFacts .unfold (reversePredicateExchange exchange)).map some := by
  unfold predicateExchangeFacts
  rw [reverse_predicate_exchange_preserves_locations]
  simpa [List.map_map, Function.comp_def] using
    reversing_fold_transfers_for_locations exchange
      (predicateExchangeLocations exchange)

theorem unfolding_then_reversing_all_exchange_facts_is_folding
    (exchange : PredicatePermissionExchange) :
    (predicateExchangeFacts .unfold exchange).map reversePermissionTransition =
      (predicateExchangeFacts .fold (reversePredicateExchange exchange)).map some := by
  unfold predicateExchangeFacts
  rw [reverse_predicate_exchange_preserves_locations]
  simpa [List.map_map, Function.comp_def] using
    reversing_unfold_transfers_for_locations exchange
      (predicateExchangeLocations exchange)

theorem inserted_primitive_callable_is_available
    (availablePrefix : PrimitiveCallableEnvironment)
    (name : String)
    (summary : PrimitiveHeapCallableSummary) :
    primitiveCallableLookup ((name, summary) :: availablePrefix) name = some summary := by
  simp [primitiveCallableLookup]

theorem virtual_dispatch_missing_override_global_is_attributed_to_outer_call
    (callTimePrefix : ModuleEnvironment)
    (statement : TopLevelVirtualDispatchCall)
    (className globalName : String)
    (functionAvailable : statement.sourceFunctionAvailable = true)
    (argumentTyped : statement.argumentSubtype = true)
    (constructorPure : statement.constructorEffectFree = true)
    (missing : firstUnavailableDispatchTarget
      callTimePrefix statement.currentlyDefinedCandidates =
        some (className, globalName)) :
    resolveTopLevelVirtualDispatch callTimePrefix statement =
      .failed statement.outerStatement
        (.undefinedOverrideGlobal className globalName) := by
  simp [resolveTopLevelVirtualDispatch, functionAvailable, argumentTyped,
    constructorPure, missing]

theorem virtual_dispatch_succeeds_when_current_dispatch_set_is_defined
    (callTimePrefix : ModuleEnvironment)
    (statement : TopLevelVirtualDispatchCall)
    (functionAvailable : statement.sourceFunctionAvailable = true)
    (argumentTyped : statement.argumentSubtype = true)
    (constructorPure : statement.constructorEffectFree = true)
    (complete : firstUnavailableDispatchTarget
      callTimePrefix statement.currentlyDefinedCandidates = none) :
    resolveTopLevelVirtualDispatch callTimePrefix statement = .succeeded := by
  simp [resolveTopLevelVirtualDispatch, functionAvailable, argumentTyped,
    constructorPure, complete]

theorem newly_defined_override_enters_later_dispatch_set
    (callTimePrefix : ModuleEnvironment)
    (earlierCandidates : List VirtualDispatchCandidate)
    (newCandidate : VirtualDispatchCandidate)
    (earlierComplete : firstUnavailableDispatchTarget
      callTimePrefix earlierCandidates = none)
    (newGlobalMissing : moduleContains
      callTimePrefix newCandidate.requiredGlobal = false) :
    firstUnavailableDispatchTarget
        callTimePrefix (earlierCandidates ++ [newCandidate]) =
      some (newCandidate.className, newCandidate.requiredGlobal) := by
  induction earlierCandidates with
  | nil => simp [firstUnavailableDispatchTarget, newGlobalMissing]
  | cons candidate rest inductionHypothesis =>
      simp only [firstUnavailableDispatchTarget] at earlierComplete
      split at earlierComplete <;> try contradiction
      rename_i candidatePresent
      simp only [List.cons_append, firstUnavailableDispatchTarget,
        candidatePresent, if_true]
      exact inductionHypothesis earlierComplete

theorem deferred_annotation_does_not_require_class_in_definition_prefix
    (definedClasses : List String)
    (className : String)
    (remaining : List NominalFunctionAnnotation) :
    firstUndefinedEagerAnnotation definedClasses
        ({ className, timing := .deferred } :: remaining) =
      firstUndefinedEagerAnnotation definedClasses remaining := by
  rfl

theorem missing_eager_annotation_fails_at_function_statement
    (definedClasses : List String)
    (declaration : OrderedAnnotatedFunctionDeclaration)
    (className : String)
    (missing : firstUndefinedEagerAnnotation
      definedClasses declaration.annotations = some className) :
    resolveOrderedFunctionAnnotations definedClasses declaration =
      .failed declaration.outerStatement className := by
  simp [resolveOrderedFunctionAnnotations, missing]

theorem later_class_definition_cannot_repair_eager_annotation
    (definedClassPrefix laterDefinedClasses : List String)
    (declaration : OrderedAnnotatedFunctionDeclaration)
    (className : String)
    (missingNow : firstUndefinedEagerAnnotation
      definedClassPrefix declaration.annotations = some className)
    (_definedLater : className ∈ laterDefinedClasses) :
    resolveOrderedFunctionAnnotations definedClassPrefix declaration =
      .failed declaration.outerStatement className := by
  exact missing_eager_annotation_fails_at_function_statement
    definedClassPrefix declaration className missingNow

theorem static_method_receives_only_explicit_arguments
    (argumentSorts : List PrimitiveCallableSort) :
    runtimeArgumentCount {
      receiverKind := .static
      explicitArgumentSorts := argumentSorts
    } = argumentSorts.length := by
  rfl

theorem instance_method_receives_one_additional_receiver
    (argumentSorts : List PrimitiveCallableSort) :
    runtimeArgumentCount {
      receiverKind := .instance
      explicitArgumentSorts := argumentSorts
    } = argumentSorts.length + 1 := by
  rfl

theorem class_method_receives_one_class_object_receiver
    (argumentSorts : List PrimitiveCallableSort) :
    runtimeArgumentCount {
      receiverKind := .class
      explicitArgumentSorts := argumentSorts
    } = argumentSorts.length + 1 := by
  rfl

theorem static_instance_override_kind_mismatch_is_rejected :
    receiverKindsOverrideCompatible .static .instance = false := by
  rfl

theorem instance_static_override_kind_mismatch_is_rejected :
    receiverKindsOverrideCompatible .instance .static = false := by
  rfl

theorem class_qualified_static_call_is_admissible :
    resolveClassQualifiedCall .static = .succeeded := by
  rfl

theorem class_qualified_classmethod_call_is_admissible :
    resolveClassQualifiedCall .class = .succeeded := by
  rfl

theorem class_qualified_instance_call_requires_receiver :
    resolveClassQualifiedCall .instance = .instanceReceiverRequired := by
  rfl

theorem dynamic_class_construction_is_well_typed_from_real_sorts
    (receiverClass resultObject : Term)
    (classTyped : inferSort receiverClass = some .class)
    (resultTyped : inferSort resultObject = some .reference) :
    dynamicClassConstructionWellTyped {
      receiverClass
      resultObject
    } = true := by
  simp only [dynamicClassConstructionWellTyped, classTyped, resultTyped]
  constructor <;> rfl

theorem dynamic_class_construction_records_runtime_identity
    (construction : DynamicClassConstruction) :
    (dynamicClassConstructionFacts construction).head? = some
      (.equal (.runtimeClass construction.resultObject) construction.receiverClass) := by
  rfl

theorem primitive_callable_sort_is_int_or_bool
    (sort : PrimitiveCallableSort) :
    sort.toValueSort = .int ∨ sort.toValueSort = .bool := by
  cases sort <;> simp [PrimitiveCallableSort.toValueSort]

theorem post_init_call_uses_sealed_provider_environment
    (currentProvider : String)
    (callee : PrimitiveCallableIdentity)
    (currentPrefix sealedProviderEnvironment : ModuleEnvironment) :
    primitiveCallableExecutionEnvironment .postInitialization currentProvider callee
      currentPrefix sealedProviderEnvironment = sealedProviderEnvironment := by
  rfl

theorem imported_initializer_call_uses_provider_environment
    (currentProvider : String)
    (callee : PrimitiveCallableIdentity)
    (currentPrefix sealedProviderEnvironment : ModuleEnvironment)
    (differentProvider : callee.provider ≠ currentProvider) :
    primitiveCallableExecutionEnvironment .moduleInitialization currentProvider callee
      currentPrefix sealedProviderEnvironment = sealedProviderEnvironment := by
  simp [primitiveCallableExecutionEnvironment, differentProvider]

theorem local_initializer_call_uses_current_prefix
    (currentProvider : String)
    (callee : PrimitiveCallableIdentity)
    (currentPrefix sealedProviderEnvironment : ModuleEnvironment)
    (sameProvider : callee.provider = currentProvider) :
    primitiveCallableExecutionEnvironment .moduleInitialization currentProvider callee
      currentPrefix sealedProviderEnvironment = currentPrefix := by
  simp [primitiveCallableExecutionEnvironment, sameProvider]

theorem parameter_shadowed_callable_edge_is_not_lexically_closed
    (declaration : PostInitPrimitiveCallableDeclaration)
    (call : QualifiedPrimitiveDirectCall)
    (rest : List QualifiedPrimitiveDirectCall)
    (calls : declaration.directCalls = call :: rest)
    (shadowed : call.sourceName ∈ declaration.parameterNames) :
    postInitPrimitiveDeclarationLexicallyClosed declaration = false := by
  simp [postInitPrimitiveDeclarationLexicallyClosed, calls, shadowed]

theorem assigned_local_shadowed_callable_edge_is_not_lexically_closed
    (declaration : PostInitPrimitiveCallableDeclaration)
    (call : QualifiedPrimitiveDirectCall)
    (rest : List QualifiedPrimitiveDirectCall)
    (calls : declaration.directCalls = call :: rest)
    (shadowed : call.sourceName ∈ primitiveScalarBlockAssignedNames declaration.body) :
    postInitPrimitiveDeclarationLexicallyClosed declaration = false := by
  simp [postInitPrimitiveDeclarationLexicallyClosed, calls, shadowed]

theorem primitive_scalar_returned_path_absorbs_continuation
    (declaredSort : PrimitiveCallableSort)
    (statement : PrimitiveScalarStmt)
    (path : PrimitiveScalarPath)
    (value : Term)
    (returned : path.status = .returned value) :
    executePrimitiveScalarStmt declaredSort statement path = some [path] := by
  cases statement <;> simp [executePrimitiveScalarStmt, returned]

theorem primitive_scalar_assignment_updates_only_its_path_environment
    (declaredSort assignedSort : PrimitiveCallableSort)
    (path : PrimitiveScalarPath)
    (name : String)
    (value : Term)
    (normal : path.status = .normal)
    (named : name.isEmpty = false)
    (readFree : primitiveScalarTermReadFree value = true)
    (typed : inferSort value = some (primitiveCallableResultSort assignedSort)) :
    executePrimitiveScalarStmt declaredSort (.assignLocal name value assignedSort) path = some [{
      path with environment := (name, value) :: eraseModuleBinding path.environment name
    }] := by
  cases assignedSort with
  | int =>
      have notDifferent : (some ValueSort.int != some ValueSort.int) = false := by rfl
      have notBool : (ValueSort.int == ValueSort.bool) = false := by rfl
      simp [executePrimitiveScalarStmt, normal, named, readFree, typed,
        primitiveCallableResultSort, PrimitiveCallableSort.toValueSort, notDifferent,
        notBool, coercePrimitiveScalarValue]
  | bool =>
      have notDifferent : (some ValueSort.bool != some ValueSort.bool) = false := by rfl
      simp [executePrimitiveScalarStmt, normal, named, readFree, typed,
        primitiveCallableResultSort, PrimitiveCallableSort.toValueSort, notDifferent,
        coercePrimitiveScalarValue]

theorem primitive_scalar_bool_promotes_to_int :
    coercePrimitiveScalarValue .int (.boolLiteral true) =
      .ite (.boolLiteral true) (.intLiteral 1) (.intLiteral 0) := by
  rfl

theorem primitive_scalar_if_constructs_and_preserves_both_path_lists
    (declaredSort : PrimitiveCallableSort)
    (condition : Term)
    (thenBody elseBody : List PrimitiveScalarStmt)
    (path : PrimitiveScalarPath)
    (thenPaths elsePaths : List PrimitiveScalarPath)
    (normal : path.status = .normal)
    (readFree : primitiveScalarTermReadFree condition = true)
    (typed : inferSort condition = some .bool)
    (thenExecuted : executePrimitiveScalarBlock declaredSort thenBody [{
      guard := .and [path.guard, condition]
      environment := path.environment
      obligations := path.obligations
      status := .normal
    }] = some thenPaths)
    (elseExecuted : executePrimitiveScalarBlock declaredSort elseBody [{
      guard := .and [path.guard, .not condition]
      environment := path.environment
      obligations := path.obligations
      status := .normal
    }] = some elsePaths) :
    executePrimitiveScalarStmt declaredSort (.ifThenElse condition thenBody elseBody) path =
      some (thenPaths ++ elsePaths) := by
  have notDifferent : (some ValueSort.bool != some ValueSort.bool) = false := by rfl
  simp [executePrimitiveScalarStmt, normal, readFree, typed, thenExecuted, elseExecuted,
    notDifferent]

theorem primitive_scalar_normal_fallthrough_creates_refutable_guard_obligation
    (path : PrimitiveScalarPath)
    (normal : path.status = .normal) :
    finalizePrimitiveScalarPath path = .implicitNoneMismatch {
      path with obligations := path.obligations ++ [.not path.guard]
    } := by
  simp [finalizePrimitiveScalarPath, normal]

theorem primitive_scalar_empty_body_keeps_implicit_none_mismatch
    (declaredSort : PrimitiveCallableSort)
    (entryEnvironment : ModuleEnvironment) :
    executeCompletePrimitiveScalarBody declaredSort entryEnvironment [] = some [
      .implicitNoneMismatch {
        guard := .boolLiteral true
        environment := entryEnvironment
        obligations := [.not (.boolLiteral true)]
        status := .normal
      }
    ] := by
  rfl

theorem primitive_scalar_two_returned_paths_merge_to_guarded_ite
    (first second : PrimitiveScalarPath)
    (firstValue secondValue : Term)
    (firstReturned : first.status = .returned firstValue)
    (secondReturned : second.status = .returned secondValue) :
    mergePrimitiveScalarReturnedPaths [first, second] =
      some (.ite first.guard firstValue secondValue) := by
  simp [mergePrimitiveScalarReturnedPaths, firstReturned, secondReturned]

theorem primitive_scalar_normal_path_prevents_callable_result_merge
    (path : PrimitiveScalarPath)
    (normal : path.status = .normal) :
    mergePrimitiveScalarReturnedPaths [path] = none := by
  simp [mergePrimitiveScalarReturnedPaths, normal]

theorem duplicate_post_init_callable_declaration_fails
    (catalog : PrimitiveCallableDeclarationCatalog)
    (declaration : PostInitPrimitiveCallableDeclaration)
    (rest : List PostInitPrimitiveCallableDeclaration)
    (duplicate :
      (primitiveCallableDeclarationLookup catalog declaration.identity).isSome = true) :
    collectPrimitiveCallableDeclarationCatalog catalog (declaration :: rest) = none := by
  simp [collectPrimitiveCallableDeclarationCatalog, duplicate]

theorem consumer_same_named_callable_cannot_replace_provider_dependency
    (catalog : PrimitiveCallableDeclarationCatalog)
    (providerIdentity consumerIdentity : PrimitiveCallableIdentity)
    (consumerDeclaration : PostInitPrimitiveCallableDeclaration)
    (differentIdentity : providerIdentity ≠ consumerIdentity) :
    primitiveCallableDeclarationLookup
        ((consumerIdentity, consumerDeclaration) :: catalog) providerIdentity =
      primitiveCallableDeclarationLookup catalog providerIdentity := by
  simp [primitiveCallableDeclarationLookup, differentIdentity]

theorem post_init_active_callable_refuses_recursion
    (catalog : PrimitiveCallableDeclarationCatalog)
    (active : List PrimitiveCallableIdentity)
    (call : QualifiedPrimitiveDirectCall)
    (rest : List QualifiedPrimitiveDirectCall)
    (fuel : Nat)
    (recursive : call.callee ∈ active) :
    resolvePostInitPrimitiveCalls catalog (fuel + 1) active (call :: rest) = none := by
  simp [resolvePostInitPrimitiveCalls, recursive]

theorem post_init_unresolved_callable_fails
    (catalog : PrimitiveCallableDeclarationCatalog)
    (active : List PrimitiveCallableIdentity)
    (call : QualifiedPrimitiveDirectCall)
    (rest : List QualifiedPrimitiveDirectCall)
    (fuel : Nat)
    (notRecursive : call.callee ∉ active)
    (unresolved : primitiveCallableDeclarationLookup catalog call.callee = none) :
    resolvePostInitPrimitiveCalls catalog (fuel + 1) active (call :: rest) = none := by
  simp [resolvePostInitPrimitiveCalls, notRecursive, unresolved]

theorem post_init_forward_typed_leaf_call_succeeds
    (catalog : PrimitiveCallableDeclarationCatalog)
    (active : List PrimitiveCallableIdentity)
    (call : QualifiedPrimitiveDirectCall)
    (callee : PostInitPrimitiveCallableDeclaration)
    (fuel : Nat)
    (notRecursive : call.callee ∉ active)
    (resolved : primitiveCallableDeclarationLookup catalog call.callee = some callee)
    (lexicallyClosed : postInitPrimitiveDeclarationLexicallyClosed callee = true)
    (typed : qualifiedPrimitiveDirectCallMatches call callee.signature)
    (leaf : callee.directCalls = []) :
    resolvePostInitPrimitiveCalls catalog (fuel + 2) active [call] = some [call.callee] := by
  simp [resolvePostInitPrimitiveCalls, notRecursive, resolved, lexicallyClosed, typed, leaf]

theorem post_init_self_recursive_callable_fails
    (catalog : PrimitiveCallableDeclarationCatalog)
    (identity : PrimitiveCallableIdentity)
    (call : QualifiedPrimitiveDirectCall)
    (fuel : Nat)
    (selfCall : call.callee = identity) :
    resolvePostInitPrimitiveCalls catalog (fuel + 1) [identity] [call] = none := by
  apply post_init_active_callable_refuses_recursion
  simp [selfCall]

theorem built_post_init_callable_captures_sealed_provider_environment
    (catalog : PrimitiveCallableDeclarationCatalog)
    (sealedProviderEnvironment : ModuleEnvironment)
    (identity : PrimitiveCallableIdentity)
    (summary : PrimitiveHeapCallableSummary)
    (obligations : List Term)
    (built : buildPostInitPrimitiveHeapCallable
      catalog sealedProviderEnvironment identity = some (summary, obligations)) :
    summary.capturedScalarEnvironment = sealedProviderEnvironment := by
  unfold buildPostInitPrimitiveHeapCallable at built
  cases lookup : primitiveCallableDeclarationLookup catalog identity with
  | none => simp [lookup] at built
  | some declaration =>
      by_cases closed : postInitPrimitiveDeclarationLexicallyClosed declaration = true
      · cases calls : resolvePostInitPrimitiveCalls catalog
          (primitiveCallableCatalogCallBudget catalog) [identity] declaration.directCalls with
        | none => simp [lookup, closed, calls] at built
        | some transitiveCallees =>
            cases body : executePrimitiveScalarBodyPaths declaration.signature.resultSort
                sealedProviderEnvironment declaration.body with
            | none => simp [lookup, closed, calls, body] at built
            | some paths =>
                cases merged : mergePrimitiveScalarReturnedPaths paths with
                | none => simp [lookup, closed, calls, body, merged] at built
                | some resultRelation =>
                    simp [lookup, closed, calls, body, merged] at built
                    rcases built with ⟨summaryEq, _⟩
                    rw [← summaryEq]
      · simp [lookup, closed] at built

theorem inserted_primitive_callable_preserves_other_names
    (availablePrefix : PrimitiveCallableEnvironment)
    (name other : String)
    (summary : PrimitiveHeapCallableSummary)
    (different : other ≠ name) :
    primitiveCallableLookup ((name, summary) :: availablePrefix) other =
      primitiveCallableLookup availablePrefix other := by
  simp [primitiveCallableLookup, different]

theorem unresolved_primitive_direct_call_fails
    (availablePrefix : PrimitiveCallableEnvironment)
    (call : PrimitiveDirectCall)
    (remainingCalls : List PrimitiveDirectCall)
    (unresolved : primitiveCallableLookup availablePrefix call.callee = none) :
    resolvePrimitiveDirectCalls availablePrefix (call :: remainingCalls) = none := by
  simp [resolvePrimitiveDirectCalls, unresolved]

theorem ill_typed_primitive_direct_call_fails
    (availablePrefix : PrimitiveCallableEnvironment)
    (call : PrimitiveDirectCall)
    (remainingCalls : List PrimitiveDirectCall)
    (calleeSummary : PrimitiveHeapCallableSummary)
    (resolved : primitiveCallableLookup availablePrefix call.callee = some calleeSummary)
    (mismatch : ¬primitiveDirectCallMatches call calleeSummary.signature) :
    resolvePrimitiveDirectCalls availablePrefix (call :: remainingCalls) = none := by
  simp [resolvePrimitiveDirectCalls, resolved, mismatch]

theorem resolved_primitive_call_preserves_transitive_callees
    (availablePrefix : PrimitiveCallableEnvironment)
    (call : PrimitiveDirectCall)
    (remainingCalls : List PrimitiveDirectCall)
    (calleeSummary : PrimitiveHeapCallableSummary)
    (remainingCallees : List String)
    (resolved : primitiveCallableLookup availablePrefix call.callee = some calleeSummary)
    (typed : primitiveDirectCallMatches call calleeSummary.signature)
    (remainingResolved :
      resolvePrimitiveDirectCalls availablePrefix remainingCalls = some remainingCallees) :
    resolvePrimitiveDirectCalls availablePrefix (call :: remainingCalls) =
      some (call.callee :: calleeSummary.transitiveCallees ++ remainingCallees) := by
  simp [resolvePrimitiveDirectCalls, resolved, typed, remainingResolved]

theorem unresolved_call_anywhere_fails_closed
    (availablePrefix : PrimitiveCallableEnvironment)
    (calls : List PrimitiveDirectCall)
    (unresolvedCall : PrimitiveDirectCall)
    (member : unresolvedCall ∈ calls)
    (unresolved :
      primitiveCallableLookup availablePrefix unresolvedCall.callee = none) :
    resolvePrimitiveDirectCalls availablePrefix calls = none := by
  induction calls with
  | nil => simp at member
  | cons call rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with same | inRest
      · subst call
        exact unresolved_primitive_direct_call_fails
          availablePrefix unresolvedCall rest unresolved
      · have restFails := inductionHypothesis inRest
        simp only [resolvePrimitiveDirectCalls]
        cases lookup : primitiveCallableLookup availablePrefix call.callee with
        | none => rfl
        | some calleeSummary =>
            by_cases typed : primitiveDirectCallMatches call calleeSummary.signature
            · simp [typed, restFails]
            · simp [typed]

theorem build_primitive_callable_from_verified_prefix
    (availablePrefix : PrimitiveCallableEnvironment)
    (sealedProviderEnvironment : ModuleEnvironment)
    (declaration : PrimitiveHeapCallableDeclaration)
    (transitiveCallees : List String)
    (fresh : primitiveCallableLookup availablePrefix declaration.name = none)
    (resolved :
      resolvePrimitiveDirectCalls availablePrefix declaration.directCalls =
        some transitiveCallees) :
    buildPrimitiveHeapCallable
        availablePrefix sealedProviderEnvironment declaration = some {
      name := declaration.name
      signature := declaration.signature
      directCallees := declaration.directCalls.map (fun call => call.callee)
      transitiveCallees
      directCallTimeGlobals := declaration.directCallTimeGlobals
      capturedScalarEnvironment := sealedProviderEnvironment
    } := by
  simp [buildPrimitiveHeapCallable, fresh, resolved]

theorem unresolved_call_in_source_prefix_refuses_build
    (availablePrefix finalCallableEnvironment : PrimitiveCallableEnvironment)
    (sealedProviderEnvironment : ModuleEnvironment)
    (declaration : PrimitiveHeapCallableDeclaration)
    (call : PrimitiveDirectCall)
    (member : call ∈ declaration.directCalls)
    (absentFromPrefix :
      primitiveCallableLookup availablePrefix call.callee = none)
    (_presentLater :
      (primitiveCallableLookup finalCallableEnvironment call.callee).isSome = true) :
    buildPrimitiveHeapCallable
        availablePrefix sealedProviderEnvironment declaration = none := by
  have callsFail := unresolved_call_anywhere_fails_closed
    availablePrefix declaration.directCalls call member absentFromPrefix
  simp [buildPrimitiveHeapCallable, callsFail]

theorem later_declaration_cannot_repair_initializer_but_is_callable_post_init
    (availablePrefix : PrimitiveCallableEnvironment)
    (catalog : PrimitiveCallableDeclarationCatalog)
    (sealedProviderEnvironment : ModuleEnvironment)
    (declaration : PrimitiveHeapCallableDeclaration)
    (callee : PostInitPrimitiveCallableDeclaration)
    (call : PrimitiveDirectCall)
    (qualifiedCall : QualifiedPrimitiveDirectCall)
    (callerIdentity : PrimitiveCallableIdentity)
    (fuel : Nat)
    (callerBody : declaration.directCalls = [call])
    (sameSourceName : qualifiedCall.callee.name = call.callee)
    (absentAtInitializer :
      primitiveCallableLookup availablePrefix call.callee = none)
    (presentAfterInit :
      primitiveCallableDeclarationLookup catalog qualifiedCall.callee = some callee)
    (differentFromCaller : qualifiedCall.callee ≠ callerIdentity)
    (lexicallyClosed : postInitPrimitiveDeclarationLexicallyClosed callee = true)
    (typed : qualifiedPrimitiveDirectCallMatches qualifiedCall callee.signature)
    (leaf : callee.directCalls = []) :
    buildPrimitiveHeapCallable
        availablePrefix sealedProviderEnvironment declaration = none ∧
      (resolvePostInitPrimitiveCalls
          catalog (fuel + 2) [callerIdentity] [qualifiedCall] =
            some [qualifiedCall.callee] ∧
        qualifiedCall.callee.name = call.callee) := by
  constructor
  · have callsFail := unresolved_call_anywhere_fails_closed
      availablePrefix declaration.directCalls call (by simp [callerBody]) absentAtInitializer
    simp [buildPrimitiveHeapCallable, callsFail]
  · constructor
    · apply post_init_forward_typed_leaf_call_succeeds
      · simp [differentFromCaller]
      · exact presentAfterInit
      · exact lexicallyClosed
      · exact typed
      · exact leaf
    · exact sameSourceName

theorem failed_callable_declaration_stops_transitive_dependents
    (availablePrefix : PrimitiveCallableEnvironment)
    (sealedProviderEnvironment : ModuleEnvironment)
    (failedDeclaration : PrimitiveHeapCallableDeclaration)
    (laterDeclarations : List PrimitiveHeapCallableDeclaration)
    (failed : buildPrimitiveHeapCallable
      availablePrefix sealedProviderEnvironment failedDeclaration = none) :
    executePrimitiveCallableDeclarations
        availablePrefix
        sealedProviderEnvironment
        (failedDeclaration :: laterDeclarations) = none := by
  simp [executePrimitiveCallableDeclarations, extendPrimitiveCallablePrefix, failed]

theorem built_primitive_callable_captures_sealed_provider_environment
    (availablePrefix : PrimitiveCallableEnvironment)
    (sealedProviderEnvironment : ModuleEnvironment)
    (declaration : PrimitiveHeapCallableDeclaration)
    (summary : PrimitiveHeapCallableSummary)
    (built : buildPrimitiveHeapCallable
      availablePrefix sealedProviderEnvironment declaration = some summary) :
    summary.capturedScalarEnvironment = sealedProviderEnvironment := by
  unfold buildPrimitiveHeapCallable at built
  split at built
  · contradiction
  · cases resolvedCalls :
        resolvePrimitiveDirectCalls availablePrefix declaration.directCalls with
    | none => simp [resolvedCalls] at built
    | some transitiveCallees =>
        simp [resolvedCalls] at built
        cases built
        rfl

theorem primitive_callable_entry_preserves_sealed_global
    (summary : PrimitiveHeapCallableSummary)
    (locallyBoundNames : List String)
    (parameters : ModuleEnvironment)
    (name : String)
    (parameterMissing : moduleLookup parameters name = none)
    (notLocallyBound : name ∉ locallyBoundNames) :
    moduleLookup
        (primitiveCallableEntryEnvironment summary locallyBoundNames parameters)
        name = moduleLookup summary.capturedScalarEnvironment name := by
  exact function_entry_preserves_untouched_captured_global
    summary.capturedScalarEnvironment locallyBoundNames parameters name
    parameterMissing notLocallyBound

theorem unresolved_transitive_callable_fails_collection
    (callablePrefix : PrimitiveCallableEnvironment)
    (callableName : String)
    (remainingNames : List String)
    (unresolved : primitiveCallableLookup callablePrefix callableName = none) :
    collectPrimitiveCallTimeGlobals
        callablePrefix (callableName :: remainingNames) = none := by
  simp [collectPrimitiveCallTimeGlobals, unresolved]

theorem constructor_direct_call_failure_is_attributed_to_outer_statement
    (callablePrefix : PrimitiveCallableEnvironment)
    (callTimePrefix : ModuleEnvironment)
    (statement : TopLevelConstructorCall)
    (failed : resolvePrimitiveDirectCalls
      callablePrefix statement.constructor.directPrimitiveCalls = none) :
    resolveTopLevelConstructorCall callablePrefix callTimePrefix statement =
      .failed statement.outerStatement .unresolvedOrIllTypedDirectCall := by
  simp [resolveTopLevelConstructorCall, failed]

theorem constructor_transitive_call_failure_is_attributed_to_outer_statement
    (callablePrefix : PrimitiveCallableEnvironment)
    (callTimePrefix : ModuleEnvironment)
    (statement : TopLevelConstructorCall)
    (transitiveCallees : List String)
    (resolved : resolvePrimitiveDirectCalls
      callablePrefix statement.constructor.directPrimitiveCalls = some transitiveCallees)
    (unresolved :
      collectPrimitiveCallTimeGlobals callablePrefix transitiveCallees = none) :
    resolveTopLevelConstructorCall callablePrefix callTimePrefix statement =
      .failed statement.outerStatement .unresolvedTransitiveCall := by
  simp [resolveTopLevelConstructorCall, resolved, unresolved]

theorem constructor_missing_global_is_attributed_to_outer_statement
    (callablePrefix : PrimitiveCallableEnvironment)
    (callTimePrefix : ModuleEnvironment)
    (statement : TopLevelConstructorCall)
    (transitiveCallees requiredGlobals : List String)
    (missingName : String)
    (resolved : resolvePrimitiveDirectCalls
      callablePrefix statement.constructor.directPrimitiveCalls = some transitiveCallees)
    (collected :
      collectPrimitiveCallTimeGlobals callablePrefix transitiveCallees =
        some requiredGlobals)
    (missing : firstMissingModuleName callTimePrefix requiredGlobals = some missingName) :
    resolveTopLevelConstructorCall callablePrefix callTimePrefix statement =
      .failed statement.outerStatement (.undefinedCallTimeGlobal missingName) := by
  simp [resolveTopLevelConstructorCall, resolved, collected, missing]

theorem constructor_call_succeeds_when_all_call_time_globals_exist
    (callablePrefix : PrimitiveCallableEnvironment)
    (callTimePrefix : ModuleEnvironment)
    (statement : TopLevelConstructorCall)
    (transitiveCallees requiredGlobals : List String)
    (resolved : resolvePrimitiveDirectCalls
      callablePrefix statement.constructor.directPrimitiveCalls = some transitiveCallees)
    (collected :
      collectPrimitiveCallTimeGlobals callablePrefix transitiveCallees =
        some requiredGlobals)
    (complete : firstMissingModuleName callTimePrefix requiredGlobals = none) :
    resolveTopLevelConstructorCall callablePrefix callTimePrefix statement =
      .succeeded := by
  simp [resolveTopLevelConstructorCall, resolved, collected, complete]

theorem constructor_call_uses_call_time_prefix_not_later_globals
    (callablePrefix : PrimitiveCallableEnvironment)
    (callTimePrefix laterEnvironment : ModuleEnvironment)
    (statement : TopLevelConstructorCall)
    (transitiveCallees requiredGlobals : List String)
    (missingName : String)
    (resolved : resolvePrimitiveDirectCalls
      callablePrefix statement.constructor.directPrimitiveCalls = some transitiveCallees)
    (collected :
      collectPrimitiveCallTimeGlobals callablePrefix transitiveCallees =
        some requiredGlobals)
    (missingNow :
      firstMissingModuleName callTimePrefix requiredGlobals = some missingName)
    (_availableLater : moduleContains laterEnvironment missingName = true) :
    resolveTopLevelConstructorCall callablePrefix callTimePrefix statement =
      .failed statement.outerStatement (.undefinedCallTimeGlobal missingName) := by
  exact constructor_missing_global_is_attributed_to_outer_statement
    callablePrefix callTimePrefix statement transitiveCallees requiredGlobals missingName
    resolved collected missingNow

theorem execute_constructor_definedness_from_halted
    (callablePrefix : PrimitiveCallableEnvironment)
    (moduleState : PassiveModuleNamespace)
    (outerStatement : Nat)
    (failure : ConstructorCallFailure)
    (statements : List ConstructorDefinednessStatement) :
    executeConstructorDefinedness
        callablePrefix
        (.halted moduleState outerStatement failure)
        statements = .halted moduleState outerStatement failure := by
  induction statements with
  | nil => simp [executeConstructorDefinedness]
  | cons statement rest inductionHypothesis =>
      simp [executeConstructorDefinedness, advanceConstructorDefinedness,
        inductionHypothesis]

theorem later_globals_cannot_repair_failed_constructor_call
    (callablePrefix : PrimitiveCallableEnvironment)
    (moduleState : PassiveModuleNamespace)
    (statement : TopLevelConstructorCall)
    (failure : ConstructorCallFailure)
    (laterStatements : List ConstructorDefinednessStatement)
    (failed : resolveTopLevelConstructorCall
      callablePrefix moduleState.scalarBindings statement =
        .failed statement.outerStatement failure) :
    executeConstructorDefinedness
        callablePrefix
        (.running moduleState)
        (.constructorCall statement :: laterStatements) =
      .halted moduleState statement.outerStatement failure := by
  simp [executeConstructorDefinedness, advanceConstructorDefinedness, failed,
    execute_constructor_definedness_from_halted]

/-!
## Source constructor results stored in nominal reference fields

This is an IR premise model for the narrowly supported frontend slice
`self.field = SourceClass(...)`, not a Python/frontend correspondence proof.  It does not assign
freshness to an arbitrary call.  The frontend must first resolve the callee to a verified source
constructor, justify the supplied freshness and frame premises, and supply the active constructor
stack; unresolved or cyclic calls halt without extending the field state.  In particular, the
frame definitions below construct and typecheck the equality requested by the frontend.  They do
not prove semantic preservation of an arbitrary heap location by Python execution.
-/

def allReferenceTerms : List Term → Bool
  | [] => true
  | value :: rest =>
      (inferSort value == some .reference) && allReferenceTerms rest

structure FreshSourceConstruction where
  className : String
  resultObject : Term
  priorReferences : List Term

def freshSourceConstructionValid (construction : FreshSourceConstruction) : Bool :=
  (!construction.className.isEmpty) &&
    ((inferSort construction.resultObject == some .reference) &&
      allReferenceTerms construction.priorReferences)

def freshSourceConstructionFacts
    (construction : FreshSourceConstruction) : List Term :=
  [
    .not (.equal construction.resultObject .nullReference),
    .equal (.runtimeClass construction.resultObject)
      (.classLiteral construction.className)
  ] ++ construction.priorReferences.map (fun prior =>
    .not (.equal construction.resultObject prior))

structure NominalReferenceFieldTarget where
  ownerClass : String
  ownerObject : Term
  fieldName : String
  valueClass : String

structure ConstructorFieldInitialization where
  preHeap : Nat
  postHeap : Nat
  target : NominalReferenceFieldTarget
  construction : FreshSourceConstruction

def constructorFieldInitializationValid
    (initialization : ConstructorFieldInitialization) : Bool :=
  (initialization.preHeap != initialization.postHeap) &&
    ((inferSort initialization.target.ownerObject == some .reference) &&
      ((!initialization.target.ownerClass.isEmpty) &&
        ((!initialization.target.fieldName.isEmpty) &&
          ((initialization.target.valueClass == initialization.construction.className) &&
            freshSourceConstructionValid initialization.construction))))

def constructorFieldPostEquality
    (initialization : ConstructorFieldInitialization) : Term :=
  .equal
    (.fieldRead initialization.postHeap initialization.target.ownerObject
      initialization.target.fieldName .reference)
    initialization.construction.resultObject

def constructorFieldInitializationFacts
    (initialization : ConstructorFieldInitialization) : List Term :=
  freshSourceConstructionFacts initialization.construction ++
    [
      .not (.equal initialization.construction.resultObject
        initialization.target.ownerObject),
      constructorFieldPostEquality initialization
    ]

structure HeapFieldLocation where
  receiver : Term
  fieldName : String
  fieldSort : ValueSort

def heapFieldLocationValid (location : HeapFieldLocation) : Bool :=
  (inferSort location.receiver == some .reference) &&
    ((!location.fieldName.isEmpty) && isHeapFieldSort location.fieldSort)

def constructorUnrelatedFieldFrameFact
    (initialization : ConstructorFieldInitialization)
    (location : HeapFieldLocation)
    (_unrelated :
      location.receiver ≠ initialization.target.ownerObject ∨
        location.fieldName ≠ initialization.target.fieldName) : Term :=
  .equal
    (.fieldRead initialization.postHeap location.receiver
      location.fieldName location.fieldSort)
    (.fieldRead initialization.preHeap location.receiver
      location.fieldName location.fieldSort)

structure SourceConstructorSummary where
  className : String
  verified : Bool
  sourceOwnedOrdinaryAllocation : Bool
  normalOnly : Bool
  effectiveDependencyClosureAcyclic : Bool

abbrev SourceConstructorEnvironment := List (String × SourceConstructorSummary)

def sourceConstructorLookup :
    SourceConstructorEnvironment → String → Option SourceConstructorSummary
  | [], _ => none
  | (boundName, summary) :: rest, name =>
      if name = boundName then some summary else sourceConstructorLookup rest name

structure ConstructorFieldRequest where
  activeConstructorStack : List String
  calleeClass : String
  preHeap : Nat
  postHeap : Nat
  ownerClass : String
  ownerObject : Term
  fieldName : String
  fieldClass : String
  resultObject : Term
  priorReferences : List Term

def constructorFieldRequestInitialization
    (request : ConstructorFieldRequest) : ConstructorFieldInitialization :=
  {
    preHeap := request.preHeap
    postHeap := request.postHeap
    target := {
      ownerClass := request.ownerClass
      ownerObject := request.ownerObject
      fieldName := request.fieldName
      valueClass := request.fieldClass
    }
    construction := {
      className := request.calleeClass
      resultObject := request.resultObject
      priorReferences := request.priorReferences
    }
  }

inductive ConstructorFieldFailure where
  | cyclicConstructor : String → ConstructorFieldFailure
  | unresolvedConstructor : String → ConstructorFieldFailure
  | unverifiedConstructor : String → ConstructorFieldFailure
  | allocatorProvenanceUnsupported : String → ConstructorFieldFailure
  | exceptionalConstructor : String → ConstructorFieldFailure
  | cyclicDependencyClosure : String → ConstructorFieldFailure
  | illTypedInitialization : ConstructorFieldFailure
  deriving DecidableEq

inductive ConstructorFieldResolution where
  | succeeded : ConstructorFieldInitialization → ConstructorFieldResolution
  | failed : ConstructorFieldFailure → ConstructorFieldResolution

def resolveConstructorFieldRequest
    (environment : SourceConstructorEnvironment)
    (request : ConstructorFieldRequest) : ConstructorFieldResolution :=
  if request.activeConstructorStack.contains request.calleeClass then
    .failed (.cyclicConstructor request.calleeClass)
  else
    match sourceConstructorLookup environment request.calleeClass with
    | none => .failed (.unresolvedConstructor request.calleeClass)
    | some summary =>
        if summary.className != request.calleeClass || summary.verified = false then
          .failed (.unverifiedConstructor request.calleeClass)
        else if summary.sourceOwnedOrdinaryAllocation = false then
          .failed (.allocatorProvenanceUnsupported request.calleeClass)
        else if summary.normalOnly = false then
          .failed (.exceptionalConstructor request.calleeClass)
        else if summary.effectiveDependencyClosureAcyclic = false then
          .failed (.cyclicDependencyClosure request.calleeClass)
        else
          let initialization := constructorFieldRequestInitialization request
          if constructorFieldInitializationValid initialization then
            .succeeded initialization
          else
            .failed .illTypedInitialization

abbrev ConstructorFieldState := List ConstructorFieldInitialization

inductive ConstructorFieldProgress where
  | running : ConstructorFieldState → ConstructorFieldProgress
  | halted : ConstructorFieldState → ConstructorFieldFailure → ConstructorFieldProgress

def advanceConstructorFieldProgress
    (environment : SourceConstructorEnvironment)
    (progress : ConstructorFieldProgress)
    (request : ConstructorFieldRequest) : ConstructorFieldProgress :=
  match progress with
  | .halted state failure => .halted state failure
  | .running state =>
      match resolveConstructorFieldRequest environment request with
      | .failed failure => .halted state failure
      | .succeeded initialization => .running (initialization :: state)

def executeConstructorFieldRequests :
    SourceConstructorEnvironment →
    ConstructorFieldProgress →
    List ConstructorFieldRequest →
    ConstructorFieldProgress
  | _, progress, [] => progress
  | environment, progress, request :: rest =>
      executeConstructorFieldRequests environment
        (advanceConstructorFieldProgress environment progress request) rest

theorem valid_fresh_source_construction_has_reference_result
    (construction : FreshSourceConstruction)
    (valid : freshSourceConstructionValid construction = true) :
    inferSort construction.resultObject = some .reference := by
  simp only [freshSourceConstructionValid, Bool.and_eq_true] at valid
  exact (beq_some_reference_true_iff _).mp valid.2.1

theorem all_reference_terms_member_has_reference_sort
    (values : List Term)
    (accepted : allReferenceTerms values = true)
    (value : Term)
    (member : value ∈ values) :
    inferSort value = some .reference := by
  induction values with
  | nil => simp at member
  | cons head rest inductionHypothesis =>
      simp [allReferenceTerms] at accepted
      simp at member
      cases member with
      | inl equal =>
          exact (beq_some_reference_true_iff _).mp (by simpa [equal] using accepted.1)
      | inr inRest => exact inductionHypothesis accepted.2 inRest

theorem valid_fresh_source_construction_has_typed_prior_references
    (construction : FreshSourceConstruction)
    (valid : freshSourceConstructionValid construction = true)
    (prior : Term)
    (member : prior ∈ construction.priorReferences) :
    inferSort prior = some .reference := by
  simp only [freshSourceConstructionValid, Bool.and_eq_true] at valid
  exact all_reference_terms_member_has_reference_sort
    construction.priorReferences valid.2.2 prior member

theorem valid_constructor_field_initialization_changes_heap
    (initialization : ConstructorFieldInitialization)
    (valid : constructorFieldInitializationValid initialization = true) :
    initialization.preHeap ≠ initialization.postHeap := by
  simp only [constructorFieldInitializationValid, Bool.and_eq_true] at valid
  exact bne_iff_ne.mp valid.1

theorem valid_constructor_field_initialization_has_exact_nominal_result
    (initialization : ConstructorFieldInitialization)
    (valid : constructorFieldInitializationValid initialization = true) :
    initialization.target.valueClass = initialization.construction.className := by
  simp only [constructorFieldInitializationValid, Bool.and_eq_true] at valid
  exact beq_iff_eq.mp valid.2.2.2.2.1

theorem fresh_construction_records_nonnull
    (construction : FreshSourceConstruction) :
    .not (.equal construction.resultObject .nullReference) ∈
      freshSourceConstructionFacts construction := by
  simp [freshSourceConstructionFacts]

theorem fresh_construction_records_exact_runtime_class
    (construction : FreshSourceConstruction) :
    .equal (.runtimeClass construction.resultObject)
        (.classLiteral construction.className) ∈
      freshSourceConstructionFacts construction := by
  simp [freshSourceConstructionFacts]

theorem fresh_construction_records_prior_reference_distinctness
    (construction : FreshSourceConstruction)
    (prior : Term)
    (member : prior ∈ construction.priorReferences) :
    .not (.equal construction.resultObject prior) ∈
      freshSourceConstructionFacts construction := by
  simp [freshSourceConstructionFacts, member]

theorem valid_constructor_field_post_equality_is_well_typed
    (initialization : ConstructorFieldInitialization)
    (valid : constructorFieldInitializationValid initialization = true) :
    inferSort (constructorFieldPostEquality initialization) = some .bool := by
  simp only [constructorFieldInitializationValid, Bool.and_eq_true] at valid
  have ownerTyped := (beq_some_reference_true_iff _).mp valid.2.1
  have resultValid : freshSourceConstructionValid initialization.construction = true :=
    valid.2.2.2.2.2
  have resultTyped := valid_fresh_source_construction_has_reference_result
    initialization.construction resultValid
  simp [constructorFieldPostEquality, inferSort, ownerTyped, resultTyped,
    isHeapFieldSort, instBEqValueSort, valueSortBeq]

theorem constructor_field_initialization_records_post_field_value
    (initialization : ConstructorFieldInitialization) :
    constructorFieldPostEquality initialization ∈
      constructorFieldInitializationFacts initialization := by
  simp [constructorFieldInitializationFacts]

theorem constructor_field_initialization_records_owner_freshness
    (initialization : ConstructorFieldInitialization) :
    .not (.equal initialization.construction.resultObject
        initialization.target.ownerObject) ∈
      constructorFieldInitializationFacts initialization := by
  simp [constructorFieldInitializationFacts]

theorem constructor_unrelated_field_frame_fact_has_expected_shape
    (initialization : ConstructorFieldInitialization)
    (location : HeapFieldLocation)
    (unrelated :
      location.receiver ≠ initialization.target.ownerObject ∨
        location.fieldName ≠ initialization.target.fieldName) :
    constructorUnrelatedFieldFrameFact initialization location unrelated =
      .equal
        (.fieldRead initialization.postHeap location.receiver
          location.fieldName location.fieldSort)
        (.fieldRead initialization.preHeap location.receiver
          location.fieldName location.fieldSort) := by
  rfl

theorem valid_unrelated_field_frame_is_well_typed
    (initialization : ConstructorFieldInitialization)
    (location : HeapFieldLocation)
    (unrelated :
      location.receiver ≠ initialization.target.ownerObject ∨
        location.fieldName ≠ initialization.target.fieldName)
    (_initializationValid :
      constructorFieldInitializationValid initialization = true)
    (locationValid : heapFieldLocationValid location = true)
    (sortReflexive : valueSortBeq location.fieldSort location.fieldSort = true) :
    inferSort
        (constructorUnrelatedFieldFrameFact initialization location unrelated) =
      some .bool := by
  simp only [heapFieldLocationValid, Bool.and_eq_true] at locationValid
  have receiverTyped := (beq_some_reference_true_iff _).mp locationValid.1
  simp [constructorUnrelatedFieldFrameFact, inferSort, receiverTyped,
    locationValid.2.2, instBEqValueSort, valueSortBeq, sortReflexive]

theorem cyclic_constructor_field_request_fails
    (environment : SourceConstructorEnvironment)
    (request : ConstructorFieldRequest)
    (cyclic : request.calleeClass ∈ request.activeConstructorStack) :
    resolveConstructorFieldRequest environment request =
      .failed (.cyclicConstructor request.calleeClass) := by
  simp [resolveConstructorFieldRequest, cyclic]

theorem unresolved_constructor_field_request_fails
    (environment : SourceConstructorEnvironment)
    (request : ConstructorFieldRequest)
    (acyclic : request.calleeClass ∉ request.activeConstructorStack)
    (unresolved : sourceConstructorLookup environment request.calleeClass = none) :
    resolveConstructorFieldRequest environment request =
      .failed (.unresolvedConstructor request.calleeClass) := by
  simp [resolveConstructorFieldRequest, acyclic, unresolved]

theorem ill_typed_constructor_field_request_fails
    (environment : SourceConstructorEnvironment)
    (request : ConstructorFieldRequest)
    (summary : SourceConstructorSummary)
    (acyclic : request.calleeClass ∉ request.activeConstructorStack)
    (resolved : sourceConstructorLookup environment request.calleeClass = some summary)
    (sameClass : summary.className = request.calleeClass)
    (verified : summary.verified = true)
    (ordinaryAllocation : summary.sourceOwnedOrdinaryAllocation = true)
    (normalOnly : summary.normalOnly = true)
    (dependencyClosureAcyclic : summary.effectiveDependencyClosureAcyclic = true)
    (illTyped :
      constructorFieldInitializationValid
        (constructorFieldRequestInitialization request) = false) :
    resolveConstructorFieldRequest environment request =
      .failed .illTypedInitialization := by
  simp [resolveConstructorFieldRequest, acyclic, resolved, sameClass, verified,
    ordinaryAllocation, normalOnly, dependencyClosureAcyclic, illTyped]

theorem unsupported_allocator_provenance_fails
    (environment : SourceConstructorEnvironment)
    (request : ConstructorFieldRequest)
    (summary : SourceConstructorSummary)
    (acyclic : request.calleeClass ∉ request.activeConstructorStack)
    (resolved : sourceConstructorLookup environment request.calleeClass = some summary)
    (sameClass : summary.className = request.calleeClass)
    (verified : summary.verified = true)
    (unsupported : summary.sourceOwnedOrdinaryAllocation = false) :
    resolveConstructorFieldRequest environment request =
      .failed (.allocatorProvenanceUnsupported request.calleeClass) := by
  simp [resolveConstructorFieldRequest, acyclic, resolved, sameClass, verified, unsupported]

theorem exceptional_constructor_fails
    (environment : SourceConstructorEnvironment)
    (request : ConstructorFieldRequest)
    (summary : SourceConstructorSummary)
    (acyclic : request.calleeClass ∉ request.activeConstructorStack)
    (resolved : sourceConstructorLookup environment request.calleeClass = some summary)
    (sameClass : summary.className = request.calleeClass)
    (verified : summary.verified = true)
    (ordinaryAllocation : summary.sourceOwnedOrdinaryAllocation = true)
    (exceptional : summary.normalOnly = false) :
    resolveConstructorFieldRequest environment request =
      .failed (.exceptionalConstructor request.calleeClass) := by
  simp [resolveConstructorFieldRequest, acyclic, resolved, sameClass, verified,
    ordinaryAllocation, exceptional]

theorem cyclic_effective_dependency_closure_fails
    (environment : SourceConstructorEnvironment)
    (request : ConstructorFieldRequest)
    (summary : SourceConstructorSummary)
    (acyclicAtCall : request.calleeClass ∉ request.activeConstructorStack)
    (resolved : sourceConstructorLookup environment request.calleeClass = some summary)
    (sameClass : summary.className = request.calleeClass)
    (verified : summary.verified = true)
    (ordinaryAllocation : summary.sourceOwnedOrdinaryAllocation = true)
    (normalOnly : summary.normalOnly = true)
    (cyclicClosure : summary.effectiveDependencyClosureAcyclic = false) :
    resolveConstructorFieldRequest environment request =
      .failed (.cyclicDependencyClosure request.calleeClass) := by
  simp [resolveConstructorFieldRequest, acyclicAtCall, resolved, sameClass, verified,
    ordinaryAllocation, normalOnly, cyclicClosure]

theorem verified_valid_constructor_field_request_succeeds
    (environment : SourceConstructorEnvironment)
    (request : ConstructorFieldRequest)
    (summary : SourceConstructorSummary)
    (acyclic : request.calleeClass ∉ request.activeConstructorStack)
    (resolved : sourceConstructorLookup environment request.calleeClass = some summary)
    (sameClass : summary.className = request.calleeClass)
    (verified : summary.verified = true)
    (ordinaryAllocation : summary.sourceOwnedOrdinaryAllocation = true)
    (normalOnly : summary.normalOnly = true)
    (dependencyClosureAcyclic : summary.effectiveDependencyClosureAcyclic = true)
    (valid :
      constructorFieldInitializationValid
        (constructorFieldRequestInitialization request) = true) :
    resolveConstructorFieldRequest environment request =
      .succeeded (constructorFieldRequestInitialization request) := by
  simp [resolveConstructorFieldRequest, acyclic, resolved, sameClass, verified,
    ordinaryAllocation, normalOnly, dependencyClosureAcyclic, valid]

theorem advance_successful_constructor_field_request_extends_state
    (environment : SourceConstructorEnvironment)
    (state : ConstructorFieldState)
    (request : ConstructorFieldRequest)
    (initialization : ConstructorFieldInitialization)
    (succeeded :
      resolveConstructorFieldRequest environment request = .succeeded initialization) :
    advanceConstructorFieldProgress environment (.running state) request =
      .running (initialization :: state) := by
  simp [advanceConstructorFieldProgress, succeeded]

theorem advance_failed_constructor_field_request_preserves_state
    (environment : SourceConstructorEnvironment)
    (state : ConstructorFieldState)
    (request : ConstructorFieldRequest)
    (failure : ConstructorFieldFailure)
    (failed : resolveConstructorFieldRequest environment request = .failed failure) :
    advanceConstructorFieldProgress environment (.running state) request =
      .halted state failure := by
  simp [advanceConstructorFieldProgress, failed]

theorem execute_constructor_field_requests_from_halted
    (environment : SourceConstructorEnvironment)
    (state : ConstructorFieldState)
    (failure : ConstructorFieldFailure)
    (requests : List ConstructorFieldRequest) :
    executeConstructorFieldRequests environment (.halted state failure) requests =
      .halted state failure := by
  induction requests with
  | nil => simp [executeConstructorFieldRequests]
  | cons request rest inductionHypothesis =>
      simp [executeConstructorFieldRequests, advanceConstructorFieldProgress,
        inductionHypothesis]

theorem later_requests_cannot_extend_failed_constructor_field_state
    (environment : SourceConstructorEnvironment)
    (state : ConstructorFieldState)
    (request : ConstructorFieldRequest)
    (failure : ConstructorFieldFailure)
    (laterRequests : List ConstructorFieldRequest)
    (failed : resolveConstructorFieldRequest environment request = .failed failure) :
    executeConstructorFieldRequests environment (.running state)
        (request :: laterRequests) = .halted state failure := by
  simp [executeConstructorFieldRequests, advanceConstructorFieldProgress, failed,
    execute_constructor_field_requests_from_halted]

/-!
## Pure contextual boolean conjunctions

This is the IR model for independently lowered contextual permission/reference facts joined by
Python `and` inside the accepted contract-expression subset.  `pureContractExpression` is a
frontend premise: this model does not claim that eager IR conjunction preserves Python
short-circuit behavior for effectful operands.  Success requires a nonempty list, a proved-pure
frontend classification for every operand, and a Boolean IR sort for every independently lowered
term.  The operand order and the complete read inventory are retained.
-/

structure PureContextualBoolFact where
  term : Term
  reads : List HeapFieldLocation
  pureContractExpression : Bool

def pureContextualBoolFactsValid : List PureContextualBoolFact → Bool
  | [] => true
  | fact :: rest =>
      fact.pureContractExpression &&
        ((inferSort fact.term == some .bool) && pureContextualBoolFactsValid rest)

def contextualConjunctionTerms (facts : List PureContextualBoolFact) : List Term :=
  facts.map PureContextualBoolFact.term

def contextualConjunctionReads
    (facts : List PureContextualBoolFact) : List HeapFieldLocation :=
  facts.flatMap PureContextualBoolFact.reads

def lowerPureContextualConjunction
    (facts : List PureContextualBoolFact) : Option (Term × List HeapFieldLocation) :=
  match facts with
  | [] => none
  | _ :: _ =>
      if pureContextualBoolFactsValid facts then
        some (.and (contextualConjunctionTerms facts), contextualConjunctionReads facts)
      else
        none

theorem valid_pure_contextual_facts_have_all_bool_terms
    (facts : List PureContextualBoolFact)
    (valid : pureContextualBoolFactsValid facts = true) :
    allBool (contextualConjunctionTerms facts) = true := by
  induction facts with
  | nil => simp [contextualConjunctionTerms, allBool]
  | cons fact rest inductionHypothesis =>
      simp only [pureContextualBoolFactsValid, Bool.and_eq_true] at valid
      simp only [contextualConjunctionTerms, List.map, allBool, Bool.and_eq_true]
      exact ⟨valid.2.1, inductionHypothesis valid.2.2⟩

theorem successful_contextual_conjunction_is_nonempty
    (facts : List PureContextualBoolFact)
    (result : Term × List HeapFieldLocation)
    (success : lowerPureContextualConjunction facts = some result) :
    facts ≠ [] := by
  intro empty
  simp [empty, lowerPureContextualConjunction] at success

theorem successful_contextual_conjunction_has_bool_sort
    (facts : List PureContextualBoolFact)
    (result : Term × List HeapFieldLocation)
    (success : lowerPureContextualConjunction facts = some result) :
    inferSort result.1 = some .bool := by
  cases facts with
  | nil => simp [lowerPureContextualConjunction] at success
  | cons fact rest =>
      simp only [lowerPureContextualConjunction] at success
      by_cases valid : pureContextualBoolFactsValid (fact :: rest) = true
      · simp [valid] at success
        cases success
        simp [inferSort, valid_pure_contextual_facts_have_all_bool_terms, valid]
      · simp [valid] at success

theorem successful_contextual_conjunction_retains_operand_order
    (facts : List PureContextualBoolFact)
    (result : Term × List HeapFieldLocation)
    (success : lowerPureContextualConjunction facts = some result) :
    result.1 = .and (contextualConjunctionTerms facts) := by
  cases facts with
  | nil => simp [lowerPureContextualConjunction] at success
  | cons fact rest =>
      simp only [lowerPureContextualConjunction] at success
      by_cases valid : pureContextualBoolFactsValid (fact :: rest) = true
      · simp [valid] at success
        cases success
        rfl
      · simp [valid] at success

theorem valid_pure_contextual_fact_member_is_pure_bool
    (facts : List PureContextualBoolFact)
    (valid : pureContextualBoolFactsValid facts = true)
    (fact : PureContextualBoolFact)
    (member : fact ∈ facts) :
    fact.pureContractExpression = true ∧ inferSort fact.term = some .bool := by
  induction facts with
  | nil => simp at member
  | cons current rest inductionHypothesis =>
      simp only [pureContextualBoolFactsValid, Bool.and_eq_true] at valid
      simp at member
      cases member with
      | inl equal =>
          subst fact
          exact ⟨valid.1, (beq_some_bool_true_iff _).mp valid.2.1⟩
      | inr tailMember => exact inductionHypothesis valid.2.2 tailMember

theorem successful_contextual_conjunction_requires_pure_bool_operand
    (facts : List PureContextualBoolFact)
    (result : Term × List HeapFieldLocation)
    (fact : PureContextualBoolFact)
    (success : lowerPureContextualConjunction facts = some result)
    (member : fact ∈ facts) :
    fact.pureContractExpression = true ∧ inferSort fact.term = some .bool := by
  cases facts with
  | nil => simp [lowerPureContextualConjunction] at success
  | cons head rest =>
      simp only [lowerPureContextualConjunction] at success
      by_cases valid : pureContextualBoolFactsValid (head :: rest) = true
      · exact valid_pure_contextual_fact_member_is_pure_bool
          (head :: rest) valid fact member
      · simp [valid] at success

theorem contextual_conjunction_reads_retain_member
    (facts : List PureContextualBoolFact)
    (fact : PureContextualBoolFact)
    (location : HeapFieldLocation)
    (factMember : fact ∈ facts)
    (readMember : location ∈ fact.reads) :
    location ∈ contextualConjunctionReads facts := by
  simp only [contextualConjunctionReads, List.mem_flatMap]
  exact ⟨fact, factMember, readMember⟩

theorem successful_contextual_conjunction_retains_each_read
    (facts : List PureContextualBoolFact)
    (result : Term × List HeapFieldLocation)
    (fact : PureContextualBoolFact)
    (location : HeapFieldLocation)
    (success : lowerPureContextualConjunction facts = some result)
    (factMember : fact ∈ facts)
    (readMember : location ∈ fact.reads) :
    location ∈ result.2 := by
  cases facts with
  | nil => simp at factMember
  | cons head rest =>
      simp only [lowerPureContextualConjunction] at success
      by_cases valid : pureContextualBoolFactsValid (head :: rest) = true
      · simp [valid] at success
        cases success
        exact contextual_conjunction_reads_retain_member
          (head :: rest) fact location factMember readMember
      · simp [valid] at success

/-!
## Source-resolved nominal field returns

This is a narrow IR/premise model for returning a non-optional nominal value through a chain of
effective typed fields.  The class that owns each field layout is deliberately separate from the
nominal class of that field's value.  Source-to-IR correspondence, source subtype discovery,
nominal field-type resolution, and the classification of an access as an effective typed field are
frontend premises.  A direct verified source property on a named receiver is modeled separately
below; properties inside multi-hop chains, dynamic attribute lookup, unverified descriptors,
calls, optional dereferences, and arbitrary Python execution are outside this model.
-/

structure SourceNominalFieldStep where
  ownerClass : String
  fieldName : String
  valueClass : String
  nominalTypeResolved : Bool
  nonOptional : Bool
  effectiveTypedField : Bool

def sourceNominalFieldStepValid (step : SourceNominalFieldStep) : Bool :=
  (!step.ownerClass.isEmpty) &&
    ((!step.fieldName.isEmpty) &&
      ((!step.valueClass.isEmpty) &&
        (step.nominalTypeResolved && (step.nonOptional && step.effectiveTypedField))))

def sourceNominalFieldChainValidFrom : String → List SourceNominalFieldStep → Bool
  | _, [] => true
  | currentClass, step :: rest =>
      (step.ownerClass == currentClass) &&
        (sourceNominalFieldStepValid step &&
          sourceNominalFieldChainValidFrom step.valueClass rest)

def sourceNominalFieldChainResultClass :
    String → List SourceNominalFieldStep → String
  | currentClass, [] => currentClass
  | _, step :: rest => sourceNominalFieldChainResultClass step.valueClass rest

def sourceNominalFieldChainTerm
    (heap : Nat) : Term → List SourceNominalFieldStep → Term
  | root, [] => root
  | root, step :: rest =>
      sourceNominalFieldChainTerm heap
        (.fieldRead heap root step.fieldName .reference) rest

structure NominalFieldReturnRequest where
  heap : Nat
  root : Term
  rootClass : String
  steps : List SourceNominalFieldStep
  declaredReturnClass : String

def nominalFieldReturnRequestValid
    (sourceSubtypeCompatible : String → String → Bool)
    (request : NominalFieldReturnRequest) : Bool :=
  (inferSort request.root == some .reference) &&
    ((!request.rootClass.isEmpty) &&
      ((!request.declaredReturnClass.isEmpty) &&
        ((!request.steps.isEmpty) &&
          (sourceNominalFieldChainValidFrom request.rootClass request.steps &&
            sourceSubtypeCompatible
              (sourceNominalFieldChainResultClass request.rootClass request.steps)
              request.declaredReturnClass))))

def lowerNominalFieldReturn
    (sourceSubtypeCompatible : String → String → Bool)
    (request : NominalFieldReturnRequest) : Option Term :=
  if nominalFieldReturnRequestValid sourceSubtypeCompatible request then
    some (sourceNominalFieldChainTerm request.heap request.root request.steps)
  else
    none

theorem source_nominal_field_chain_result_uses_value_class_not_layout_owner
    (rootClass : String)
    (step : SourceNominalFieldStep) :
    sourceNominalFieldChainResultClass rootClass [step] = step.valueClass := by
  simp [sourceNominalFieldChainResultClass]

theorem valid_source_nominal_field_chain_member_is_verified_nonoptional
    (currentClass : String)
    (steps : List SourceNominalFieldStep)
    (valid : sourceNominalFieldChainValidFrom currentClass steps = true)
    (step : SourceNominalFieldStep)
    (member : step ∈ steps) :
    step.nominalTypeResolved = true ∧
      step.nonOptional = true ∧ step.effectiveTypedField = true := by
  induction steps generalizing currentClass with
  | nil => simp at member
  | cons current rest inductionHypothesis =>
      simp only [sourceNominalFieldChainValidFrom, Bool.and_eq_true] at valid
      simp at member
      cases member with
      | inl equal =>
          subst step
          simp only [sourceNominalFieldStepValid, Bool.and_eq_true] at valid
          exact ⟨valid.2.1.2.2.2.1, valid.2.1.2.2.2.2.1,
            valid.2.1.2.2.2.2.2⟩
      | inr tailMember =>
          exact inductionHypothesis current.valueClass valid.2.2 tailMember

theorem source_nominal_field_chain_term_has_reference_sort
    (heap : Nat)
    (root : Term)
    (steps : List SourceNominalFieldStep)
    (rootTyped : inferSort root = some .reference) :
    inferSort (sourceNominalFieldChainTerm heap root steps) = some .reference := by
  induction steps generalizing root with
  | nil => simpa [sourceNominalFieldChainTerm] using rootTyped
  | cons step rest inductionHypothesis =>
      apply inductionHypothesis
      simp [inferSort, rootTyped, isHeapFieldSort, instBEqValueSort, valueSortBeq]

theorem valid_nominal_field_return_has_compatible_declared_type
    (sourceSubtypeCompatible : String → String → Bool)
    (request : NominalFieldReturnRequest)
    (valid : nominalFieldReturnRequestValid sourceSubtypeCompatible request = true) :
    sourceSubtypeCompatible
        (sourceNominalFieldChainResultClass request.rootClass request.steps)
        request.declaredReturnClass = true := by
  simp only [nominalFieldReturnRequestValid, Bool.and_eq_true] at valid
  exact valid.2.2.2.2.2

theorem successful_nominal_field_return_has_reference_sort
    (sourceSubtypeCompatible : String → String → Bool)
    (request : NominalFieldReturnRequest)
    (result : Term)
    (success : lowerNominalFieldReturn sourceSubtypeCompatible request = some result) :
    inferSort result = some .reference := by
  unfold lowerNominalFieldReturn at success
  by_cases valid : nominalFieldReturnRequestValid sourceSubtypeCompatible request = true
  · simp [valid] at success
    cases success
    simp only [nominalFieldReturnRequestValid, Bool.and_eq_true] at valid
    exact source_nominal_field_chain_term_has_reference_sort
      request.heap request.root request.steps
      ((beq_some_reference_true_iff _).mp valid.1)
  · simp [valid] at success

theorem invalid_nominal_field_return_fails_closed
    (sourceSubtypeCompatible : String → String → Bool)
    (request : NominalFieldReturnRequest)
    (invalid : nominalFieldReturnRequestValid sourceSubtypeCompatible request = false) :
    lowerNominalFieldReturn sourceSubtypeCompatible request = none := by
  simp [lowerNominalFieldReturn, invalid]

theorem optional_single_field_return_is_invalid
    (sourceSubtypeCompatible : String → String → Bool)
    (request : NominalFieldReturnRequest)
    (step : SourceNominalFieldStep)
    (singleStep : request.steps = [step])
    (optional : step.nonOptional = false) :
    nominalFieldReturnRequestValid sourceSubtypeCompatible request = false := by
  simp [nominalFieldReturnRequestValid, singleStep,
    sourceNominalFieldChainValidFrom, sourceNominalFieldStepValid, optional]

theorem non_field_single_step_return_is_invalid
    (sourceSubtypeCompatible : String → String → Bool)
    (request : NominalFieldReturnRequest)
    (step : SourceNominalFieldStep)
    (singleStep : request.steps = [step])
    (notField : step.effectiveTypedField = false) :
    nominalFieldReturnRequestValid sourceSubtypeCompatible request = false := by
  simp [nominalFieldReturnRequestValid, singleStep,
    sourceNominalFieldChainValidFrom, sourceNominalFieldStepValid, notField]

structure DirectNominalPropertyReturnRequest where
  receiver : Term
  receiverClass : String
  propertyName : String
  propertyValue : Term
  valueClass : String
  declaredReturnClass : String
  directNamedReceiver : Bool
  verifiedSourceProperty : Bool
  nonOptional : Bool

def directNominalPropertyReturnValid
    (sourceSubtypeCompatible : String → String → Bool)
    (request : DirectNominalPropertyReturnRequest) : Bool :=
  (inferSort request.receiver == some .reference) &&
    ((inferSort request.propertyValue == some .reference) &&
      ((!request.receiverClass.isEmpty) &&
        ((!request.propertyName.isEmpty) &&
          ((!request.valueClass.isEmpty) &&
            ((!request.declaredReturnClass.isEmpty) &&
              (request.directNamedReceiver &&
                (request.verifiedSourceProperty &&
                  (request.nonOptional &&
                    sourceSubtypeCompatible request.valueClass
                      request.declaredReturnClass))))))))

theorem valid_direct_nominal_property_return_has_compatible_declared_type
    (sourceSubtypeCompatible : String → String → Bool)
    (request : DirectNominalPropertyReturnRequest)
    (valid : directNominalPropertyReturnValid sourceSubtypeCompatible request = true) :
    sourceSubtypeCompatible request.valueClass request.declaredReturnClass = true := by
  simp only [directNominalPropertyReturnValid, Bool.and_eq_true] at valid
  exact valid.2.2.2.2.2.2.2.2.2

theorem indirect_or_unverified_property_return_is_invalid
    (sourceSubtypeCompatible : String → String → Bool)
    (request : DirectNominalPropertyReturnRequest)
    (unsupported :
      request.directNamedReceiver = false ∨ request.verifiedSourceProperty = false) :
    directNominalPropertyReturnValid sourceSubtypeCompatible request = false := by
  cases unsupported with
  | inl indirect => simp [directNominalPropertyReturnValid, indirect]
  | inr unverified => simp [directNominalPropertyReturnValid, unverified]

/-!
## Direct reference-field `Old` identity

This is an IR/premise model for the narrow normal postcondition
`self.field is Old(self.field)`.  The old and current reads retain distinct method-entry and
method-exit heap versions, and their read permissions retain distinct entry and exit masks.  The
frontend must establish that this is a verified source-owned non-constructor instance method, a
normal `Ensures`, a direct non-optional effective typed reference field, and that the complete
direct-plus-transitive modification set excludes the field.  The definitions below construct the
typed obligations and preserve call-site rebinding; they do not prove Python/frontend
correspondence, permission truth, modification-set completeness, or semantic framing.

Nested fields, property/descriptor targets, dynamic attributes, calls inside `Old`, constructors,
exception postconditions, and external contract-only methods are outside this model.
-/

structure OldReferenceFieldRequest where
  entryHeap : Nat
  exitHeap : Nat
  entryMask : Nat
  exitMask : Nat
  receiver : Term
  ownerClass : String
  fieldName : String
  valueClass : String
  sourceOwnedVerifiedMethod : Bool
  instanceMethod : Bool
  notConstructor : Bool
  normalEnsures : Bool
  directSelfField : Bool
  nominalTypeResolved : Bool
  nonOptional : Bool
  effectiveTypedField : Bool
  entryReadPermissionContractProved : Bool
  exitReadPermissionContractProved : Bool
  completeModificationSetProved : Bool
  unmodifiedSameReceiverFrameProved : Bool
  completeModifiedFields : List String

def oldReferenceFieldValue (request : OldReferenceFieldRequest) : Term :=
  .fieldRead request.entryHeap request.receiver request.fieldName .reference

def currentReferenceFieldValue (request : OldReferenceFieldRequest) : Term :=
  .fieldRead request.exitHeap request.receiver request.fieldName .reference

def oldReferenceFieldIdentity (request : OldReferenceFieldRequest) : Term :=
  .equal (currentReferenceFieldValue request) (oldReferenceFieldValue request)

def oldReferenceFieldReadPermissions (request : OldReferenceFieldRequest) : List Term :=
  [
    .permissionPositive request.entryMask request.receiver request.fieldName,
    .permissionPositive request.exitMask request.receiver request.fieldName
  ]

def oldReferenceFieldRequestWellFormed (request : OldReferenceFieldRequest) : Bool :=
  (inferSort request.receiver == some .reference) &&
    ((!request.ownerClass.isEmpty) &&
      ((!request.fieldName.isEmpty) &&
        ((!request.valueClass.isEmpty) &&
          (request.sourceOwnedVerifiedMethod &&
            (request.instanceMethod &&
              (request.notConstructor &&
                (request.normalEnsures &&
                  (request.directSelfField &&
                    (request.nominalTypeResolved &&
                      (request.nonOptional &&
                        (request.effectiveTypedField &&
                          (request.entryReadPermissionContractProved &&
                            (request.exitReadPermissionContractProved &&
                              (request.completeModificationSetProved &&
                                request.unmodifiedSameReceiverFrameProved))))))))))))))

def frameOldReferenceFieldIfUnmodified
    (request : OldReferenceFieldRequest) : Option Term :=
  if request.completeModifiedFields.contains request.fieldName then none
  else some (oldReferenceFieldIdentity request)

structure OldReferenceFieldSummary where
  ownerClass : String
  fieldName : String
  valueClass : String
  completeModifiedFields : List String

def buildOldReferenceFieldSummary
    (request : OldReferenceFieldRequest) : Option OldReferenceFieldSummary :=
  if oldReferenceFieldRequestWellFormed request &&
      !request.completeModifiedFields.contains request.fieldName then
    some {
      ownerClass := request.ownerClass
      fieldName := request.fieldName
      valueClass := request.valueClass
      completeModifiedFields := request.completeModifiedFields
    }
  else
    none

def instantiateOldReferenceFieldSummary
    (summary : OldReferenceFieldSummary)
    (entryHeap exitHeap entryMask exitMask : Nat)
    (receiver : Term) : OldReferenceFieldRequest :=
  {
    entryHeap
    exitHeap
    entryMask
    exitMask
    receiver
    ownerClass := summary.ownerClass
    fieldName := summary.fieldName
    valueClass := summary.valueClass
    sourceOwnedVerifiedMethod := true
    instanceMethod := true
    notConstructor := true
    normalEnsures := true
    directSelfField := true
    nominalTypeResolved := true
    nonOptional := true
    effectiveTypedField := true
    entryReadPermissionContractProved := true
    exitReadPermissionContractProved := true
    completeModificationSetProved := true
    unmodifiedSameReceiverFrameProved := true
    completeModifiedFields := summary.completeModifiedFields
  }

theorem old_reference_field_value_uses_entry_heap
    (request : OldReferenceFieldRequest) :
    oldReferenceFieldValue request =
      .fieldRead request.entryHeap request.receiver request.fieldName .reference := by
  rfl

theorem current_reference_field_value_uses_exit_heap
    (request : OldReferenceFieldRequest) :
    currentReferenceFieldValue request =
      .fieldRead request.exitHeap request.receiver request.fieldName .reference := by
  rfl

theorem old_and_current_reads_have_reference_sort
    (request : OldReferenceFieldRequest)
    (receiverTyped : inferSort request.receiver = some .reference) :
    inferSort (oldReferenceFieldValue request) = some .reference ∧
      inferSort (currentReferenceFieldValue request) = some .reference := by
  simp [oldReferenceFieldValue, currentReferenceFieldValue, inferSort, receiverTyped,
    isHeapFieldSort, instBEqValueSort, valueSortBeq]

theorem old_identity_has_bool_sort
    (request : OldReferenceFieldRequest)
    (receiverTyped : inferSort request.receiver = some .reference) :
    inferSort (oldReferenceFieldIdentity request) = some .bool := by
  simp [oldReferenceFieldIdentity, oldReferenceFieldValue, currentReferenceFieldValue,
    inferSort, receiverTyped, isHeapFieldSort, instBEqValueSort, valueSortBeq]

theorem old_read_permissions_use_separate_entry_and_exit_masks
    (request : OldReferenceFieldRequest) :
    oldReferenceFieldReadPermissions request =
      [
        .permissionPositive request.entryMask request.receiver request.fieldName,
        .permissionPositive request.exitMask request.receiver request.fieldName
      ] := by
  rfl

theorem old_read_permissions_are_bool_typed
    (request : OldReferenceFieldRequest)
    (receiverTyped : inferSort request.receiver = some .reference) :
    allBool (oldReferenceFieldReadPermissions request) = true := by
  simp [oldReferenceFieldReadPermissions, allBool, inferSort, receiverTyped,
    instBEqValueSort, valueSortBeq]

theorem modified_old_reference_field_has_no_automatic_frame
    (request : OldReferenceFieldRequest)
    (modified : request.fieldName ∈ request.completeModifiedFields) :
    frameOldReferenceFieldIfUnmodified request = none := by
  simp [frameOldReferenceFieldIfUnmodified, modified]

theorem unmodified_old_reference_field_frames_entry_to_exit
    (request : OldReferenceFieldRequest)
    (unmodified : request.fieldName ∉ request.completeModifiedFields) :
    frameOldReferenceFieldIfUnmodified request =
      some (oldReferenceFieldIdentity request) := by
  simp [frameOldReferenceFieldIfUnmodified, unmodified]

theorem successful_old_reference_summary_requires_frontend_premises
    (request : OldReferenceFieldRequest)
    (summary : OldReferenceFieldSummary)
    (success : buildOldReferenceFieldSummary request = some summary) :
    oldReferenceFieldRequestWellFormed request = true ∧
      request.fieldName ∉ request.completeModifiedFields := by
  unfold buildOldReferenceFieldSummary at success
  split at success
  · rename_i accepted
    simp at accepted
    exact accepted
  · simp at success

theorem successful_old_reference_summary_excludes_complete_modifies
    (request : OldReferenceFieldRequest)
    (summary : OldReferenceFieldSummary)
    (success : buildOldReferenceFieldSummary request = some summary) :
    request.fieldName ∉ request.completeModifiedFields :=
  (successful_old_reference_summary_requires_frontend_premises
    request summary success).2

theorem instantiated_old_summary_rebinds_heaps_and_masks
    (summary : OldReferenceFieldSummary)
    (entryHeap exitHeap entryMask exitMask : Nat)
    (receiver : Term) :
    let request := instantiateOldReferenceFieldSummary summary
      entryHeap exitHeap entryMask exitMask receiver
    request.entryHeap = entryHeap ∧ request.exitHeap = exitHeap ∧
      request.entryMask = entryMask ∧ request.exitMask = exitMask := by
  simp [instantiateOldReferenceFieldSummary]

theorem instantiated_old_summary_uses_call_entry_and_exit_reads
    (summary : OldReferenceFieldSummary)
    (entryHeap exitHeap entryMask exitMask : Nat)
    (receiver : Term) :
    let request := instantiateOldReferenceFieldSummary summary
      entryHeap exitHeap entryMask exitMask receiver
    oldReferenceFieldIdentity request =
      .equal
        (.fieldRead exitHeap receiver summary.fieldName .reference)
        (.fieldRead entryHeap receiver summary.fieldName .reference) := by
  rfl

/-!
## Direct nominal reference result identity

This is an IR/premise model for the narrow normal postconditions `Result() is self.field` and
`Result() is not self.field`.  A successful summary needs more than equality of nominal type
labels: the frontend must prove the selected normal-return identity or nonidentity proposition
between the returned reference and the field read in the method's exit heap.  It must also prove
the exit read-permission contract and the direct field/type premises.  The definitions retain that
proposition when rebinding a proved summary to a caller result, receiver, exit heap, and exit mask.
The `nonOptional` premise covers the effective field and the frontend's accepted method-return type;
the production method-type constructor rejects `Optional[...]` before this rule.

This model does not prove Python/frontend correspondence, straight-line control-flow or normal-path
completeness, provenance, permission truth, or provider-summary validity.  The frontend premise
includes a unique terminal normal return with no executable successor: a later statement must not
overwrite the returned term used to prove provenance.  Constructors, exception postconditions,
property/descriptor targets, optional or scalar fields, nested/dynamic fields, calls in the field
position, and external contract-only methods are outside the model.
-/

structure ResultReferenceFieldRequest where
  exitHeap : Nat
  exitMask : Nat
  receiver : Term
  result : Term
  ownerClass : String
  fieldName : String
  fieldValueClass : String
  declaredReturnClass : String
  negated : Bool
  sourceOwnedVerifiedMethod : Bool
  instanceMethod : Bool
  notConstructor : Bool
  normalEnsures : Bool
  directSelfField : Bool
  nominalTypeResolved : Bool
  nonOptional : Bool
  effectiveTypedField : Bool
  exactNominalReturnType : Bool
  exitReadPermissionContractProved : Bool
  uniqueTerminalNormalReturn : Bool
  noExecutableSuccessorAfterReturn : Bool
  allNormalReturnPathsCovered : Bool
  resultFieldProvenanceProved : Bool

def currentResultReferenceFieldValue (request : ResultReferenceFieldRequest) : Term :=
  .fieldRead request.exitHeap request.receiver request.fieldName .reference

def resultReferenceFieldProvenanceFact (request : ResultReferenceFieldRequest) : Term :=
  let equality := .equal request.result (currentResultReferenceFieldValue request)
  if request.negated then .not equality else equality

def resultReferenceFieldReadPermission (request : ResultReferenceFieldRequest) : Term :=
  .permissionPositive request.exitMask request.receiver request.fieldName

def resultReferenceFieldRequestWellFormed (request : ResultReferenceFieldRequest) : Bool :=
  (inferSort request.receiver == some .reference) &&
    (inferSort request.result == some .reference) &&
    (!request.ownerClass.isEmpty) &&
    (!request.fieldName.isEmpty) &&
    (!request.fieldValueClass.isEmpty) &&
    (!request.declaredReturnClass.isEmpty) &&
    (request.fieldValueClass == request.declaredReturnClass) &&
    request.sourceOwnedVerifiedMethod &&
    request.instanceMethod &&
    request.notConstructor &&
    request.normalEnsures &&
    request.directSelfField &&
    request.nominalTypeResolved &&
    request.nonOptional &&
    request.effectiveTypedField &&
    request.exactNominalReturnType &&
    request.exitReadPermissionContractProved &&
    request.uniqueTerminalNormalReturn &&
    request.noExecutableSuccessorAfterReturn &&
    request.allNormalReturnPathsCovered &&
    request.resultFieldProvenanceProved

structure ResultReferenceFieldSummary where
  ownerClass : String
  fieldName : String
  fieldValueClass : String
  declaredReturnClass : String
  negated : Bool

def buildResultReferenceFieldSummary
    (request : ResultReferenceFieldRequest) : Option ResultReferenceFieldSummary :=
  if resultReferenceFieldRequestWellFormed request then
    some {
      ownerClass := request.ownerClass
      fieldName := request.fieldName
      fieldValueClass := request.fieldValueClass
      declaredReturnClass := request.declaredReturnClass
      negated := request.negated
    }
  else
    none

def instantiateResultReferenceFieldSummary
    (summary : ResultReferenceFieldSummary)
    (exitHeap exitMask : Nat)
    (receiver result : Term) : ResultReferenceFieldRequest :=
  {
    exitHeap
    exitMask
    receiver
    result
    ownerClass := summary.ownerClass
    fieldName := summary.fieldName
    fieldValueClass := summary.fieldValueClass
    declaredReturnClass := summary.declaredReturnClass
    negated := summary.negated
    sourceOwnedVerifiedMethod := true
    instanceMethod := true
    notConstructor := true
    normalEnsures := true
    directSelfField := true
    nominalTypeResolved := true
    nonOptional := true
    effectiveTypedField := true
    exactNominalReturnType := true
    exitReadPermissionContractProved := true
    uniqueTerminalNormalReturn := true
    noExecutableSuccessorAfterReturn := true
    allNormalReturnPathsCovered := true
    resultFieldProvenanceProved := true
  }

theorem current_result_reference_field_uses_exit_heap
    (request : ResultReferenceFieldRequest) :
    currentResultReferenceFieldValue request =
      .fieldRead request.exitHeap request.receiver request.fieldName .reference := by
  rfl

theorem result_reference_field_permission_uses_exit_mask
    (request : ResultReferenceFieldRequest) :
    resultReferenceFieldReadPermission request =
      .permissionPositive request.exitMask request.receiver request.fieldName := by
  rfl

theorem result_reference_field_provenance_is_bool_typed
    (request : ResultReferenceFieldRequest)
    (receiverTyped : inferSort request.receiver = some .reference)
    (resultTyped : inferSort request.result = some .reference) :
    inferSort (resultReferenceFieldProvenanceFact request) = some .bool := by
  cases negatedValue : request.negated <;>
    simp [resultReferenceFieldProvenanceFact, currentResultReferenceFieldValue,
      negatedValue, inferSort, receiverTyped, resultTyped, isHeapFieldSort,
      instBEqValueSort, valueSortBeq]

theorem positive_result_reference_field_claim_is_current_field_equality
    (request : ResultReferenceFieldRequest)
    (positive : request.negated = false) :
    resultReferenceFieldProvenanceFact request =
      .equal request.result (currentResultReferenceFieldValue request) := by
  simp [resultReferenceFieldProvenanceFact, positive]

theorem negative_result_reference_field_claim_is_negated_current_field_equality
    (request : ResultReferenceFieldRequest)
    (negative : request.negated = true) :
    resultReferenceFieldProvenanceFact request =
      .not (.equal request.result (currentResultReferenceFieldValue request)) := by
  simp [resultReferenceFieldProvenanceFact, negative]

theorem result_reference_field_permission_is_bool_typed
    (request : ResultReferenceFieldRequest)
    (receiverTyped : inferSort request.receiver = some .reference) :
    inferSort (resultReferenceFieldReadPermission request) = some .bool := by
  simp [resultReferenceFieldReadPermission, inferSort, receiverTyped,
    instBEqValueSort, valueSortBeq]

theorem equal_nominal_types_without_provenance_do_not_build_result_summary
    (request : ResultReferenceFieldRequest)
    (sameNominal : request.fieldValueClass = request.declaredReturnClass)
    (missingProvenance : request.resultFieldProvenanceProved = false) :
    buildResultReferenceFieldSummary request = none := by
  simp [buildResultReferenceFieldSummary, resultReferenceFieldRequestWellFormed,
    sameNominal, missingProvenance]

theorem result_reference_summary_refuses_missing_exit_permission
    (request : ResultReferenceFieldRequest)
    (missingPermission : request.exitReadPermissionContractProved = false) :
    buildResultReferenceFieldSummary request = none := by
  simp [buildResultReferenceFieldSummary, resultReferenceFieldRequestWellFormed,
    missingPermission]

theorem result_reference_summary_refuses_nonterminal_return
    (request : ResultReferenceFieldRequest)
    (hasSuccessor : request.noExecutableSuccessorAfterReturn = false) :
    buildResultReferenceFieldSummary request = none := by
  simp [buildResultReferenceFieldSummary, resultReferenceFieldRequestWellFormed,
    hasSuccessor]

theorem successful_result_reference_summary_is_well_formed
    (request : ResultReferenceFieldRequest)
    (summary : ResultReferenceFieldSummary)
    (success : buildResultReferenceFieldSummary request = some summary) :
    resultReferenceFieldRequestWellFormed request = true := by
  unfold buildResultReferenceFieldSummary at success
  split at success
  · assumption
  · simp at success

theorem successful_result_reference_summary_requires_provenance
    (request : ResultReferenceFieldRequest)
    (summary : ResultReferenceFieldSummary)
    (success : buildResultReferenceFieldSummary request = some summary) :
    request.uniqueTerminalNormalReturn = true ∧
      request.noExecutableSuccessorAfterReturn = true ∧
        request.allNormalReturnPathsCovered = true ∧
          request.resultFieldProvenanceProved = true := by
  unfold buildResultReferenceFieldSummary at success
  split at success
  · rename_i accepted
    have terminal : request.uniqueTerminalNormalReturn = true := by
      cases terminalValue : request.uniqueTerminalNormalReturn <;>
        simp_all [resultReferenceFieldRequestWellFormed]
    have noSuccessor : request.noExecutableSuccessorAfterReturn = true := by
      cases successorValue : request.noExecutableSuccessorAfterReturn <;>
        simp_all [resultReferenceFieldRequestWellFormed]
    have covered : request.allNormalReturnPathsCovered = true := by
      cases coveredValue : request.allNormalReturnPathsCovered <;>
        simp_all [resultReferenceFieldRequestWellFormed]
    have provenance : request.resultFieldProvenanceProved = true := by
      cases provenanceValue : request.resultFieldProvenanceProved <;>
        simp_all [resultReferenceFieldRequestWellFormed]
    exact ⟨terminal, noSuccessor, covered, provenance⟩
  · simp at success

theorem instantiated_result_summary_rebinds_exit_state_and_result
    (summary : ResultReferenceFieldSummary)
    (exitHeap exitMask : Nat)
    (receiver result : Term) :
    let request := instantiateResultReferenceFieldSummary summary
      exitHeap exitMask receiver result
    request.exitHeap = exitHeap ∧ request.exitMask = exitMask ∧
      request.receiver = receiver ∧ request.result = result := by
  simp [instantiateResultReferenceFieldSummary]

theorem instantiated_result_summary_uses_caller_result_and_exit_field
    (summary : ResultReferenceFieldSummary)
    (exitHeap exitMask : Nat)
    (receiver result : Term) :
    let request := instantiateResultReferenceFieldSummary summary
      exitHeap exitMask receiver result
    resultReferenceFieldProvenanceFact request =
      if summary.negated then
        .not (.equal result
          (.fieldRead exitHeap receiver summary.fieldName .reference))
      else
        .equal result
          (.fieldRead exitHeap receiver summary.fieldName .reference) := by
  simp [instantiateResultReferenceFieldSummary, resultReferenceFieldProvenanceFact,
    currentResultReferenceFieldValue]

/-!
## Late-bound source-class dependencies of methods

This is an IR/premise model for source class names used by supported method contracts and bodies.
Parsing a method declaration does not require those late-bound names in the class-definition
prefix.  Summary construction instead requires every source-resolved canonical dependency in the
sealed final module catalog.  Applying that summary is a separate operation: a dependency owned by
the current module must exist in the exact class prefix at the call statement, while a dependency
owned by an imported provider requires that provider's initialization to have completed.

The frontend must supply complete dependency collection, lexical/global classification, canonical
module-qualified identity, exact source-prefix state, and provider-initialization facts.  This model
does not prove those facts from Python.  Bases, decorators, class-body expressions, and bare method
annotations remain eager and use the separate definition-prefix check below; only the existing
quoted/deferred annotation path defers.  Dynamic lookup, reflection, local/parameter
shadowing, unchecked external providers, and unresolved or never-defined class names are outside
the successful rules.
-/

inductive LateBoundClassDependencyOrigin where
  | localModule
  | completedImportedProvider : String → LateBoundClassDependencyOrigin
  deriving DecidableEq

structure LateBoundClassDependency where
  sourceName : String
  canonicalName : String
  origin : LateBoundClassDependencyOrigin
  deriving DecidableEq

structure LateBoundMethodClassDeclaration where
  ownerCanonicalName : String
  methodName : String
  requiredClasses : List LateBoundClassDependency
  sourceOwnedVerified : Bool
  dependencyCollectionComplete : Bool
  lexicalShadowingExcluded : Bool
  canonicalResolutionStable : Bool

structure LateBoundMethodClassSummary where
  ownerCanonicalName : String
  methodName : String
  requiredClasses : List LateBoundClassDependency

def parseLateBoundMethodClassDeclaration
    (_definitionPrefix : List String)
    (declaration : LateBoundMethodClassDeclaration) : LateBoundMethodClassDeclaration :=
  declaration

def dependencyResolvedInFinalCatalog
    (finalCanonicalClasses : List String)
    (dependency : LateBoundClassDependency) : Bool :=
  (!dependency.sourceName.isEmpty) &&
    ((!dependency.canonicalName.isEmpty) &&
      decide (dependency.canonicalName ∈ finalCanonicalClasses))

def allDependenciesResolvedInFinalCatalog
    (finalCanonicalClasses : List String) :
    List LateBoundClassDependency → Bool
  | [] => true
  | dependency :: rest =>
      dependencyResolvedInFinalCatalog finalCanonicalClasses dependency &&
        allDependenciesResolvedInFinalCatalog finalCanonicalClasses rest

def buildLateBoundMethodClassSummary
    (finalCanonicalClasses : List String)
    (declaration : LateBoundMethodClassDeclaration) :
    Option LateBoundMethodClassSummary :=
  if (!declaration.ownerCanonicalName.isEmpty) &&
      ((!declaration.methodName.isEmpty) &&
        (declaration.sourceOwnedVerified &&
          (declaration.dependencyCollectionComplete &&
            (declaration.lexicalShadowingExcluded &&
              (declaration.canonicalResolutionStable &&
                allDependenciesResolvedInFinalCatalog
                  finalCanonicalClasses declaration.requiredClasses)))))
  then
    some {
      ownerCanonicalName := declaration.ownerCanonicalName
      methodName := declaration.methodName
      requiredClasses := declaration.requiredClasses
    }
  else
    none

structure CallTimeClassAvailability where
  localCanonicalPrefix : List String
  completedImportedProviders : List String

def lateBoundClassDependencyAvailable
    (availability : CallTimeClassAvailability)
    (dependency : LateBoundClassDependency) : Bool :=
  match dependency.origin with
  | .localModule => decide (dependency.canonicalName ∈ availability.localCanonicalPrefix)
  | .completedImportedProvider provider =>
      (!provider.isEmpty) && decide (provider ∈ availability.completedImportedProviders)

def firstUnavailableLateBoundClass
    (availability : CallTimeClassAvailability) :
    List LateBoundClassDependency → Option LateBoundClassDependency
  | [] => none
  | dependency :: rest =>
      if lateBoundClassDependencyAvailable availability dependency
      then firstUnavailableLateBoundClass availability rest
      else some dependency

inductive LateBoundMethodCallOutcome where
  | applied : LateBoundMethodCallOutcome
  | refused : LateBoundClassDependency → LateBoundMethodCallOutcome
  deriving DecidableEq

def applyLateBoundMethodClassSummary
    (availability : CallTimeClassAvailability)
    (summary : LateBoundMethodClassSummary) : LateBoundMethodCallOutcome :=
  match firstUnavailableLateBoundClass availability summary.requiredClasses with
  | none => .applied
  | some dependency => .refused dependency

def exportLateBoundClassDependency
    (provider : String)
    (dependency : LateBoundClassDependency) : LateBoundClassDependency :=
  match dependency.origin with
  | .localModule =>
      { dependency with origin := .completedImportedProvider provider }
  | .completedImportedProvider _ => dependency

def exportLateBoundMethodClassSummary
    (provider : String)
    (summary : LateBoundMethodClassSummary) : LateBoundMethodClassSummary :=
  { summary with
      requiredClasses := summary.requiredClasses.map
        (exportLateBoundClassDependency provider) }

inductive LateBoundClassCallStatement where
  | defineLocalClass : String → LateBoundClassCallStatement
  | completeImportedProvider : String → LateBoundClassCallStatement
  | callMethod : LateBoundMethodClassSummary → LateBoundClassCallStatement

inductive LateBoundClassCallProgress where
  | running : CallTimeClassAvailability → LateBoundClassCallProgress
  | halted : CallTimeClassAvailability → LateBoundClassDependency →
      LateBoundClassCallProgress

def advanceLateBoundClassCallProgress
    (progress : LateBoundClassCallProgress)
    (statement : LateBoundClassCallStatement) : LateBoundClassCallProgress :=
  match progress with
  | .halted availability dependency => .halted availability dependency
  | .running availability =>
      match statement with
      | .defineLocalClass canonicalName =>
          if canonicalName.isEmpty || canonicalName ∈ availability.localCanonicalPrefix
          then .running availability
          else .running {
            availability with
            localCanonicalPrefix := availability.localCanonicalPrefix ++ [canonicalName]
          }
      | .completeImportedProvider provider =>
          if provider.isEmpty || provider ∈ availability.completedImportedProviders
          then .running availability
          else .running {
            availability with
            completedImportedProviders :=
              availability.completedImportedProviders ++ [provider]
          }
      | .callMethod summary =>
          match applyLateBoundMethodClassSummary availability summary with
          | .applied => .running availability
          | .refused dependency => .halted availability dependency

def executeLateBoundClassCallStatements :
    LateBoundClassCallProgress → List LateBoundClassCallStatement →
      LateBoundClassCallProgress
  | progress, [] => progress
  | progress, statement :: rest =>
      executeLateBoundClassCallStatements
        (advanceLateBoundClassCallProgress progress statement) rest

structure EagerClassDefinitionDependencies where
  requiredBases : List String
  requiredDecorators : List String
  requiredClassBodyNames : List String
  requiredBareMethodAnnotations : List String

def eagerClassDefinitionDependencyNames
    (dependencies : EagerClassDefinitionDependencies) : List String :=
  dependencies.requiredBases ++ dependencies.requiredDecorators ++
    dependencies.requiredClassBodyNames ++ dependencies.requiredBareMethodAnnotations

def firstUnavailableEagerClassDefinitionName
    (definitionPrefix : List String)
    (dependencies : EagerClassDefinitionDependencies) : Option String :=
  (eagerClassDefinitionDependencyNames dependencies).find?
    (fun name => decide (name ∉ definitionPrefix))

theorem late_bound_method_build_does_not_consult_definition_prefix
    (firstDefinitionPrefix secondDefinitionPrefix finalCanonicalClasses : List String)
    (declaration : LateBoundMethodClassDeclaration) :
    buildLateBoundMethodClassSummary finalCanonicalClasses
        (parseLateBoundMethodClassDeclaration firstDefinitionPrefix declaration) =
      buildLateBoundMethodClassSummary finalCanonicalClasses
        (parseLateBoundMethodClassDeclaration secondDefinitionPrefix declaration) := by
  rfl

theorem never_defined_class_refuses_late_bound_summary
    (finalCanonicalClasses : List String)
    (declaration : LateBoundMethodClassDeclaration)
    (missing : allDependenciesResolvedInFinalCatalog
      finalCanonicalClasses declaration.requiredClasses = false) :
    buildLateBoundMethodClassSummary finalCanonicalClasses declaration = none := by
  simp [buildLateBoundMethodClassSummary, missing]

theorem successful_late_bound_summary_preserves_complete_dependency_list
    (finalCanonicalClasses : List String)
    (declaration : LateBoundMethodClassDeclaration)
    (summary : LateBoundMethodClassSummary)
    (success : buildLateBoundMethodClassSummary
      finalCanonicalClasses declaration = some summary) :
    summary.requiredClasses = declaration.requiredClasses := by
  unfold buildLateBoundMethodClassSummary at success
  split at success
  · simpa using congrArg LateBoundMethodClassSummary.requiredClasses
      (Option.some.inj success.symm)
  · simp at success

theorem missing_local_class_at_call_refuses_summary
    (availability : CallTimeClassAvailability)
    (summary : LateBoundMethodClassSummary)
    (dependency : LateBoundClassDependency)
    (missing : firstUnavailableLateBoundClass
      availability summary.requiredClasses = some dependency) :
    applyLateBoundMethodClassSummary availability summary = .refused dependency := by
  simp [applyLateBoundMethodClassSummary, missing]

theorem complete_call_time_class_availability_applies_summary
    (availability : CallTimeClassAvailability)
    (summary : LateBoundMethodClassSummary)
    (complete : firstUnavailableLateBoundClass
      availability summary.requiredClasses = none) :
    applyLateBoundMethodClassSummary availability summary = .applied := by
  simp [applyLateBoundMethodClassSummary, complete]

theorem later_local_class_cannot_repair_earlier_method_call
    (callTimeAvailability laterAvailability : CallTimeClassAvailability)
    (summary : LateBoundMethodClassSummary)
    (dependency : LateBoundClassDependency)
    (missingAtCall : firstUnavailableLateBoundClass
      callTimeAvailability summary.requiredClasses = some dependency)
    (_availableLater : lateBoundClassDependencyAvailable
      laterAvailability dependency = true) :
    applyLateBoundMethodClassSummary callTimeAvailability summary = .refused dependency := by
  exact missing_local_class_at_call_refuses_summary
    callTimeAvailability summary dependency missingAtCall

theorem completed_imported_provider_satisfies_its_class_dependency
    (localPrefix providers : List String)
    (sourceName canonicalName provider : String)
    (providerNonempty : provider.isEmpty = false)
    (completed : provider ∈ providers) :
    lateBoundClassDependencyAvailable
      {
        localCanonicalPrefix := localPrefix
        completedImportedProviders := providers
      }
      {
        sourceName
        canonicalName
        origin := .completedImportedProvider provider
      } = true := by
  simp [lateBoundClassDependencyAvailable, providerNonempty, completed]

theorem same_spelled_noncanonical_local_does_not_satisfy_dependency
    (localPrefix providers : List String)
    (sourceName canonicalName : String)
    (canonicalMissing : canonicalName ∉ localPrefix) :
    lateBoundClassDependencyAvailable
      {
        localCanonicalPrefix := localPrefix
        completedImportedProviders := providers
      }
      {
        sourceName
        canonicalName
        origin := .localModule
      } = false := by
  simp [lateBoundClassDependencyAvailable, canonicalMissing]

theorem exported_late_bound_summary_preserves_canonical_dependencies
    (provider : String)
    (summary : LateBoundMethodClassSummary) :
    (exportLateBoundMethodClassSummary provider summary).requiredClasses.map
        (fun dependency => dependency.canonicalName) =
      summary.requiredClasses.map (fun dependency => dependency.canonicalName) := by
  cases summary with
  | mk owner method requiredClasses =>
      simp only [exportLateBoundMethodClassSummary]
      induction requiredClasses with
      | nil => rfl
      | cons dependency rest inductionHypothesis =>
          cases dependency with
          | mk sourceName canonicalName origin =>
              cases origin <;>
                simp [exportLateBoundClassDependency, inductionHypothesis]

theorem exported_late_bound_summary_preserves_foreign_provider_origin
    (provider foreignProvider sourceName canonicalName : String) :
    exportLateBoundClassDependency provider {
      sourceName
      canonicalName
      origin := .completedImportedProvider foreignProvider
    } = {
      sourceName
      canonicalName
      origin := .completedImportedProvider foreignProvider
    } := by
  rfl

theorem exported_late_bound_summary_seals_only_local_dependency_origin
    (provider sourceName canonicalName : String) :
    exportLateBoundClassDependency provider {
      sourceName
      canonicalName
      origin := .localModule
    } = {
      sourceName
      canonicalName
      origin := .completedImportedProvider provider
    } := by
  rfl

/- A source provider exposes only its own public class names, but consumers of one of those
   summaries may still need provider-qualified foreign layouts referenced by fields, signatures,
   bases, or constructor edges.  Those shapes remain a private canonical dependency closure; they
   are not relabeled or made importable as if the intermediate provider owned them. -/
structure CanonicalProviderShapeCatalog where
  publicOwnedCanonicalNames : List String
  privateDependencyCanonicalNames : List String

def canonicalProviderShapeAvailable
    (catalog : CanonicalProviderShapeCatalog) (canonicalName : String) : Bool :=
  decide (canonicalName ∈ catalog.publicOwnedCanonicalNames) ||
    decide (canonicalName ∈ catalog.privateDependencyCanonicalNames)

def retainPrivateCanonicalProviderShapes
    (publicOwnedCanonicalNames privateDependencyCanonicalNames : List String) :
    CanonicalProviderShapeCatalog :=
  { publicOwnedCanonicalNames, privateDependencyCanonicalNames }

theorem retained_foreign_shape_is_available_without_becoming_public
    (publicOwned foreignCanonicalNames : List String)
    (foreignCanonicalName : String)
    (foreign : foreignCanonicalName ∈ foreignCanonicalNames)
    (notPublic : foreignCanonicalName ∉ publicOwned) :
    let catalog := retainPrivateCanonicalProviderShapes
      publicOwned foreignCanonicalNames
    canonicalProviderShapeAvailable catalog foreignCanonicalName = true ∧
      foreignCanonicalName ∉ catalog.publicOwnedCanonicalNames := by
  simp [retainPrivateCanonicalProviderShapes, canonicalProviderShapeAvailable,
    foreign, notPublic]

theorem halted_late_bound_call_progress_is_absorbing
    (availability : CallTimeClassAvailability)
    (dependency : LateBoundClassDependency)
    (statements : List LateBoundClassCallStatement) :
    executeLateBoundClassCallStatements
      (.halted availability dependency) statements = .halted availability dependency := by
  induction statements with
  | nil => rfl
  | cons statement rest inductionHypothesis =>
      simp [executeLateBoundClassCallStatements,
        advanceLateBoundClassCallProgress, inductionHypothesis]

theorem later_definition_does_not_extend_namespace_after_failed_method_call
    (availability : CallTimeClassAvailability)
    (summary : LateBoundMethodClassSummary)
    (dependency : LateBoundClassDependency)
    (laterClass : String)
    (missing : applyLateBoundMethodClassSummary availability summary =
      .refused dependency) :
    executeLateBoundClassCallStatements
      (.running availability)
      [.callMethod summary, .defineLocalClass laterClass] =
        .halted availability dependency := by
  simp [executeLateBoundClassCallStatements, advanceLateBoundClassCallProgress, missing]

theorem eager_class_definition_uses_definition_prefix
    (definitionPrefix : List String)
    (dependencies : EagerClassDefinitionDependencies)
    (missingName : String)
    (missing : firstUnavailableEagerClassDefinitionName
      definitionPrefix dependencies = some missingName) :
    firstUnavailableEagerClassDefinitionName definitionPrefix dependencies =
      some missingName := by
  exact missing

theorem later_class_cannot_repair_eager_definition_failure
    (definitionPrefix laterClasses : List String)
    (dependencies : EagerClassDefinitionDependencies)
    (missingName : String)
    (missing : firstUnavailableEagerClassDefinitionName
      definitionPrefix dependencies = some missingName)
    (_definedLater : missingName ∈ laterClasses) :
    firstUnavailableEagerClassDefinitionName definitionPrefix dependencies =
      some missingName := by
  exact missing

/-!
## Reference-valued method calls inside field chains

This is a narrow IR/premise model for chains such as `receiver.get_ref().field.get_ref()`, where
each method call has zero explicit arguments.
Each accepted field selection consumes the immediately preceding reference and records a positive
read-permission obligation in that state's mask.  Each accepted method call consumes the current
reference, records its direct returned-field permission precondition, advances to the call's exit
heap and mask, and introduces only the exit permission and returned-reference provenance that a
verified source summary proved.  The resulting reference and nominal class become the input to the
next source-ordered step.  State-preserving summaries retain the entry heap/mask; this includes
verified no-write, net-permission-neutral ordinary methods as well as applicable `@Pure` methods.
State-changing summaries advance exactly the affected version: heap writes require a distinct heap
and a complete heap-transition/frame premise, while non-neutral permission effects require a
distinct mask and a complete permission-transition premise.

The frontend remains responsible for resolving effective fields and methods, exact non-optional
nominal types, virtual dispatch, complete permission effects and modification sets, normal-only
control flow, and source-summary provenance.  This section constructs and typechecks the resulting
IR trace from those premises.  It does not prove Python/frontend correspondence, permission truth,
semantic heap framing, alias facts, or that an arbitrary frontend summary satisfies the premises.
Optional/scalar/unresolved results, method arguments, properties/descriptors, dynamic or reflective
calls, external contract-only summaries or inherited fields, source methods whose returned field is
external-inherited, and exceptional results remain outside the successful rule. The chain rule
consumes already verified modular summaries and does not recursively expand method bodies.
-/

structure ReferenceChainState where
  heap : Nat
  mask : Nat
  value : Term
  nominalClass : String

structure ReferenceChainTrace where
  state : ReferenceChainState
  obligations : List Term
  assumptions : List Term

inductive ReferenceChainMemberOrigin where
  | verifiedSource (provider : String)
  | checkedExternal (provider contractHash : String)

def referenceChainMemberOriginIsVerifiedSource
    (origin : ReferenceChainMemberOrigin) : Bool :=
  match origin with
  | .verifiedSource provider => !provider.isEmpty
  | .checkedExternal _ _ => false

theorem checked_external_reference_chain_member_is_not_verified_source
    (provider contractHash : String) :
    referenceChainMemberOriginIsVerifiedSource
      (.checkedExternal provider contractHash) = false := by
  rfl

theorem nonempty_verified_source_reference_chain_member_is_accepted
    (provider : String) (nonempty : provider.isEmpty = false) :
    referenceChainMemberOriginIsVerifiedSource (.verifiedSource provider) = true := by
  simp [referenceChainMemberOriginIsVerifiedSource, nonempty]

structure ReferenceFieldChainStep where
  ownerClass : String
  fieldName : String
  resultClass : String
  effectiveFieldResolved : Bool
  exactNominalReference : Bool
  nonOptional : Bool
  fieldOrigin : ReferenceChainMemberOrigin

structure ReferenceMethodChainSummary where
  ownerClass : String
  methodName : String
  returnedField : String
  resultClass : String
  summaryOrigin : ReferenceChainMemberOrigin
  instanceMethod : Bool
  zeroArguments : Bool
  normalOnly : Bool
  exactNominalReferenceResult : Bool
  nonOptionalResult : Bool
  directReturnedField : Bool
  returnedFieldOrigin : ReferenceChainMemberOrigin
  directReadPermissionPrecondition : Bool
  exitReadPermissionPreserved : Bool
  resultFieldProvenanceProved : Bool
  completePermissionEffects : Bool
  completeModificationSet : Bool
  noHeapWrites : Bool
  netPermissionNeutral : Bool
  virtualDispatchResolved : Bool

structure ReferenceMethodChainStep where
  summary : ReferenceMethodChainSummary
  exitHeap : Nat
  exitMask : Nat
  result : Term
  heapTransitionAndFrameProved : Bool
  permissionTransitionProved : Bool

inductive ReferenceChainStep where
  | field : ReferenceFieldChainStep -> ReferenceChainStep
  | call : ReferenceMethodChainStep -> ReferenceChainStep

def referenceMethodChainStatePreserving
    (summary : ReferenceMethodChainSummary) : Bool :=
  summary.noHeapWrites && summary.netPermissionNeutral

theorem reference_method_chain_state_preserving_iff
    (summary : ReferenceMethodChainSummary) :
    referenceMethodChainStatePreserving summary = true ↔
      summary.noHeapWrites = true /\ summary.netPermissionNeutral = true := by
  simp [referenceMethodChainStatePreserving]

def referenceFieldChainStepWellFormed
    (state : ReferenceChainState) (step : ReferenceFieldChainStep) : Bool :=
  (inferSort state.value == some .reference) &&
    (!state.nominalClass.isEmpty) &&
    (state.nominalClass == step.ownerClass) &&
    (!step.fieldName.isEmpty) &&
    (!step.resultClass.isEmpty) &&
    step.effectiveFieldResolved &&
    step.exactNominalReference &&
    step.nonOptional &&
    referenceChainMemberOriginIsVerifiedSource step.fieldOrigin

def referenceMethodChainSummaryWellFormed
    (summary : ReferenceMethodChainSummary) : Bool :=
  (!summary.ownerClass.isEmpty) &&
    (!summary.methodName.isEmpty) &&
    (!summary.returnedField.isEmpty) &&
    (!summary.resultClass.isEmpty) &&
    referenceChainMemberOriginIsVerifiedSource summary.summaryOrigin &&
    summary.instanceMethod &&
    summary.zeroArguments &&
    summary.normalOnly &&
    summary.exactNominalReferenceResult &&
    summary.nonOptionalResult &&
    summary.directReturnedField &&
    referenceChainMemberOriginIsVerifiedSource summary.returnedFieldOrigin &&
    summary.directReadPermissionPrecondition &&
    summary.exitReadPermissionPreserved &&
    summary.resultFieldProvenanceProved &&
    summary.completePermissionEffects &&
    summary.completeModificationSet &&
    summary.virtualDispatchResolved

def referenceMethodChainStepWellFormed
    (state : ReferenceChainState) (step : ReferenceMethodChainStep) : Bool :=
  (inferSort state.value == some .reference) &&
    (inferSort step.result == some .reference) &&
    (state.nominalClass == step.summary.ownerClass) &&
    referenceMethodChainSummaryWellFormed step.summary &&
    (if step.summary.noHeapWrites then
      step.exitHeap == state.heap
    else
      (step.exitHeap != state.heap) &&
        step.heapTransitionAndFrameProved) &&
    (if step.summary.netPermissionNeutral then
      step.exitMask == state.mask
    else
      (step.exitMask != state.mask) &&
        step.permissionTransitionProved)

def referenceChainFieldRead
    (state : ReferenceChainState) (step : ReferenceFieldChainStep) : Term :=
  .fieldRead state.heap state.value step.fieldName .reference

def referenceChainFieldPermission
    (state : ReferenceChainState) (fieldName : String) : Term :=
  .permissionPositive state.mask state.value fieldName

def referenceChainCallResultProvenance
    (state : ReferenceChainState) (step : ReferenceMethodChainStep) : Term :=
  .equal step.result
    (.fieldRead step.exitHeap state.value step.summary.returnedField .reference)

def referenceChainCallExitPermission
    (state : ReferenceChainState) (step : ReferenceMethodChainStep) : Term :=
  .permissionPositive step.exitMask state.value step.summary.returnedField

def referenceChainCallPermissionTransition
    (state : ReferenceChainState) (step : ReferenceMethodChainStep) : Term :=
  if step.summary.netPermissionNeutral then
    .boolLiteral true
  else
    .permissionMaskTransition state.mask step.exitMask step.summary.returnedField
      [(state.value, 1, 1)] [(state.value, 1, 1)]

theorem reference_chain_field_read_has_reference_sort
    (state : ReferenceChainState) (step : ReferenceFieldChainStep)
    (receiverTyped : inferSort state.value = some .reference) :
    inferSort (referenceChainFieldRead state step) = some .reference := by
  simp [referenceChainFieldRead, inferSort, receiverTyped, isHeapFieldSort,
    instBEqValueSort, valueSortBeq]

theorem reference_chain_field_permission_has_bool_sort
    (state : ReferenceChainState) (fieldName : String)
    (receiverTyped : inferSort state.value = some .reference) :
    inferSort (referenceChainFieldPermission state fieldName) = some .bool := by
  simp [referenceChainFieldPermission, inferSort, receiverTyped,
    instBEqValueSort, valueSortBeq]

theorem reference_chain_call_provenance_has_bool_sort
    (state : ReferenceChainState) (step : ReferenceMethodChainStep)
    (receiverTyped : inferSort state.value = some .reference)
    (resultTyped : inferSort step.result = some .reference) :
    inferSort (referenceChainCallResultProvenance state step) = some .bool := by
  simp [referenceChainCallResultProvenance, inferSort, receiverTyped, resultTyped,
    isHeapFieldSort, instBEqValueSort, valueSortBeq]

theorem reference_chain_call_exit_permission_has_bool_sort
    (state : ReferenceChainState) (step : ReferenceMethodChainStep)
    (receiverTyped : inferSort state.value = some .reference) :
    inferSort (referenceChainCallExitPermission state step) = some .bool := by
  simp [referenceChainCallExitPermission, inferSort, receiverTyped,
    instBEqValueSort, valueSortBeq]

theorem state_changing_reference_chain_permission_transition_has_bool_sort
    (state : ReferenceChainState) (step : ReferenceMethodChainStep)
    (permissionChanging : step.summary.netPermissionNeutral = false)
    (distinctMasks : state.mask ≠ step.exitMask)
    (receiverTyped : inferSort state.value = some .reference)
    (fieldNonempty : step.summary.returnedField.isEmpty = false) :
    inferSort (referenceChainCallPermissionTransition state step) = some .bool := by
  simp [referenceChainCallPermissionTransition, permissionChanging, inferSort, distinctMasks,
    receiverTyped, fieldNonempty, allPermissionTransferAmounts,
    instBEqValueSort, valueSortBeq]

def applyReferenceFieldChainStep
    (trace : ReferenceChainTrace) (step : ReferenceFieldChainStep) :
    Option ReferenceChainTrace :=
  if referenceFieldChainStepWellFormed trace.state step then
    some {
      state := {
        heap := trace.state.heap
        mask := trace.state.mask
        value := referenceChainFieldRead trace.state step
        nominalClass := step.resultClass
      }
      obligations := trace.obligations ++
        [referenceChainFieldPermission trace.state step.fieldName]
      assumptions := trace.assumptions
    }
  else
    none

def applyReferenceMethodChainStep
    (trace : ReferenceChainTrace) (step : ReferenceMethodChainStep) :
    Option ReferenceChainTrace :=
  if referenceMethodChainStepWellFormed trace.state step then
    some {
      state := {
        heap := step.exitHeap
        mask := step.exitMask
        value := step.result
        nominalClass := step.summary.resultClass
      }
      obligations := trace.obligations ++
        [referenceChainFieldPermission trace.state step.summary.returnedField]
      assumptions := trace.assumptions ++ [
        referenceChainCallPermissionTransition trace.state step,
        referenceChainCallExitPermission trace.state step,
        referenceChainCallResultProvenance trace.state step
      ]
    }
  else
    none

def applyReferenceChainStep
    (trace : ReferenceChainTrace) (step : ReferenceChainStep) :
    Option ReferenceChainTrace :=
  match step with
  | .field fieldStep => applyReferenceFieldChainStep trace fieldStep
  | .call callStep => applyReferenceMethodChainStep trace callStep

inductive ReferenceChainProgress where
  | running : ReferenceChainTrace -> ReferenceChainProgress
  | halted : ReferenceChainTrace -> ReferenceChainProgress

def advanceReferenceChainProgress
    (progress : ReferenceChainProgress) (step : ReferenceChainStep) :
    ReferenceChainProgress :=
  match progress with
  | .halted trace => .halted trace
  | .running trace =>
      match applyReferenceChainStep trace step with
      | none => .halted trace
      | some nextTrace => .running nextTrace

def executeReferenceChain :
    ReferenceChainProgress -> List ReferenceChainStep -> ReferenceChainProgress
  | progress, [] => progress
  | progress, step :: rest =>
      executeReferenceChain (advanceReferenceChainProgress progress step) rest

theorem successful_field_chain_step_preserves_heap_and_mask
    (trace next : ReferenceChainTrace)
    (step : ReferenceFieldChainStep)
    (success : applyReferenceFieldChainStep trace step = some next) :
    next.state.heap = trace.state.heap /\ next.state.mask = trace.state.mask := by
  unfold applyReferenceFieldChainStep at success
  split at success
  · simpa using congrArg (fun value => (value.state.heap, value.state.mask))
      (Option.some.inj success.symm)
  · simp at success

theorem successful_field_chain_step_uses_current_state_permission
    (trace next : ReferenceChainTrace)
    (step : ReferenceFieldChainStep)
    (success : applyReferenceFieldChainStep trace step = some next) :
    next.obligations = trace.obligations ++
      [.permissionPositive trace.state.mask trace.state.value step.fieldName] := by
  unfold applyReferenceFieldChainStep at success
  split at success
  · simpa [referenceChainFieldPermission] using
      congrArg ReferenceChainTrace.obligations (Option.some.inj success.symm)
  · simp at success

theorem successful_field_chain_step_threads_reference_and_nominal_class
    (trace next : ReferenceChainTrace)
    (step : ReferenceFieldChainStep)
    (success : applyReferenceFieldChainStep trace step = some next) :
    next.state.value =
        .fieldRead trace.state.heap trace.state.value step.fieldName .reference /\
      next.state.nominalClass = step.resultClass := by
  unfold applyReferenceFieldChainStep at success
  split at success
  · simpa [referenceChainFieldRead] using congrArg (fun value =>
      (value.state.value, value.state.nominalClass)) (Option.some.inj success.symm)
  · simp at success

theorem successful_method_chain_step_threads_exit_state_and_result
    (trace next : ReferenceChainTrace)
    (step : ReferenceMethodChainStep)
    (success : applyReferenceMethodChainStep trace step = some next) :
    next.state.heap = step.exitHeap /\
      next.state.mask = step.exitMask /\
      next.state.value = step.result /\
      next.state.nominalClass = step.summary.resultClass := by
  unfold applyReferenceMethodChainStep at success
  split at success
  · simpa using congrArg (fun value =>
      (value.state.heap, value.state.mask, value.state.value, value.state.nominalClass))
      (Option.some.inj success.symm)
  · simp at success

theorem successful_method_chain_step_records_entry_permission_and_exit_provenance
    (trace next : ReferenceChainTrace)
    (step : ReferenceMethodChainStep)
    (success : applyReferenceMethodChainStep trace step = some next) :
    next.obligations = trace.obligations ++ [
        .permissionPositive trace.state.mask trace.state.value step.summary.returnedField
      ] /\
      next.assumptions = trace.assumptions ++ [
        referenceChainCallPermissionTransition trace.state step,
        .permissionPositive step.exitMask trace.state.value step.summary.returnedField,
        .equal step.result
          (.fieldRead step.exitHeap trace.state.value step.summary.returnedField .reference)
      ] := by
  unfold applyReferenceMethodChainStep at success
  split at success
  · simpa [referenceChainFieldPermission, referenceChainCallExitPermission,
      referenceChainCallResultProvenance] using congrArg (fun value =>
        (value.obligations, value.assumptions)) (Option.some.inj success.symm)
  · simp at success

theorem state_preserving_reference_method_chain_step_keeps_entry_versions
    (state : ReferenceChainState) (step : ReferenceMethodChainStep)
    (statePreserving : referenceMethodChainStatePreserving step.summary = true)
    (accepted : referenceMethodChainStepWellFormed state step = true) :
    step.exitHeap = state.heap /\ step.exitMask = state.mask := by
  have preservation :=
    (reference_method_chain_state_preserving_iff step.summary).mp statePreserving
  simp [referenceMethodChainStepWellFormed, preservation.1, preservation.2] at accepted
  exact ⟨accepted.1.2, accepted.2⟩

theorem heap_writing_reference_method_chain_step_advances_heap
    (state : ReferenceChainState) (step : ReferenceMethodChainStep)
    (heapWriting : step.summary.noHeapWrites = false)
    (accepted : referenceMethodChainStepWellFormed state step = true) :
    step.exitHeap ≠ state.heap := by
  simp [referenceMethodChainStepWellFormed, heapWriting] at accepted
  exact accepted.1.2.1

theorem permission_changing_reference_method_chain_step_advances_mask
    (state : ReferenceChainState) (step : ReferenceMethodChainStep)
    (permissionChanging : step.summary.netPermissionNeutral = false)
    (accepted : referenceMethodChainStepWellFormed state step = true) :
    step.exitMask ≠ state.mask := by
  simp [referenceMethodChainStepWellFormed, permissionChanging] at accepted
  exact accepted.2.1

theorem successful_call_then_field_reads_call_result_in_call_exit_heap
    (trace afterCall afterField : ReferenceChainTrace)
    (callStep : ReferenceMethodChainStep)
    (fieldStep : ReferenceFieldChainStep)
    (callSuccess : applyReferenceMethodChainStep trace callStep = some afterCall)
    (fieldSuccess : applyReferenceFieldChainStep afterCall fieldStep = some afterField) :
    afterField.state.value =
      .fieldRead callStep.exitHeap callStep.result fieldStep.fieldName .reference := by
  have callState := successful_method_chain_step_threads_exit_state_and_result
    trace afterCall callStep callSuccess
  have fieldState := successful_field_chain_step_threads_reference_and_nominal_class
    afterCall afterField fieldStep fieldSuccess
  calc
    afterField.state.value =
        .fieldRead afterCall.state.heap afterCall.state.value fieldStep.fieldName .reference :=
      fieldState.1
    _ = .fieldRead callStep.exitHeap callStep.result fieldStep.fieldName .reference := by
      rw [callState.1, callState.2.2.1]

theorem successful_call_then_field_checks_call_exit_permission
    (trace afterCall afterField : ReferenceChainTrace)
    (callStep : ReferenceMethodChainStep)
    (fieldStep : ReferenceFieldChainStep)
    (callSuccess : applyReferenceMethodChainStep trace callStep = some afterCall)
    (fieldSuccess : applyReferenceFieldChainStep afterCall fieldStep = some afterField) :
    afterField.obligations = afterCall.obligations ++ [
      .permissionPositive callStep.exitMask callStep.result fieldStep.fieldName
    ] := by
  have callState := successful_method_chain_step_threads_exit_state_and_result
    trace afterCall callStep callSuccess
  have fieldPermission := successful_field_chain_step_uses_current_state_permission
    afterCall afterField fieldStep fieldSuccess
  rw [fieldPermission, callState.2.1, callState.2.2.1]

theorem rejected_reference_chain_step_halts_without_extending_trace
    (trace : ReferenceChainTrace) (step : ReferenceChainStep)
    (rejected : applyReferenceChainStep trace step = none) :
    advanceReferenceChainProgress (.running trace) step = .halted trace := by
  simp [advanceReferenceChainProgress, rejected]

theorem halted_reference_chain_is_absorbing
    (trace : ReferenceChainTrace) (steps : List ReferenceChainStep) :
    executeReferenceChain (.halted trace) steps = .halted trace := by
  induction steps with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      simp [executeReferenceChain, advanceReferenceChainProgress, inductionHypothesis]

/-!
## Identity-sufficient positive reference equality assertions

This is the narrow premise model for upstream `test_method_calls.py` lines 59 and 61.  It does not
equate Python `==` with identity in general.  A positive `Assert(left == right)` may generate the
identity equality as a sufficient obligation only when `left` is an exact, normally completed,
source-allocated local whose complete source MRO ends at `object` without a `__eq__` override.
The frontend may lower the assertion only after the current assumptions already prove identity;
that proof also recovers the right operand's exact runtime class.  Distinct or unknown identity is
unresolved rather than a Python-equality refutation.  The rule never substitutes a nominal class
for runtime dispatch and never assumes anything about reverse dispatch.

`Assert` is ghost/specification syntax.  The right operand is therefore only a source name or a
raw, permission-checked field chain read from the current heap/mask.  It cannot contain an
ordinary method call or execute the v34 state-transition chain.  Other contexts/operators,
custom/external/dynamic MRO entries, arbitrary operands, and non-exact left origins remain outside
the successful rule.  These are explicit frontend premises, not a Python-semantics theorem.
-/

inductive NarrowReferenceEqualityContext where
  | positiveAssert
  | requiresClause
  | ensuresClause
  | negatedAssert

inductive NarrowReferenceEqualityOperator where
  | equal
  | notEqual

inductive ReferenceEqualityMroEntry where
  | sourceWithoutEqOrInitSubclassBinding (className : String)
  | sourceWithEqOverride (className : String)
  | sourceWithInitSubclassBinding (className : String)
  | objectDefault
  | checkedExternal (className : String)
  | dynamicUnknown

def completeSourceMroUsesObjectEquality : List ReferenceEqualityMroEntry → Bool
  | [.objectDefault] => true
  | .sourceWithoutEqOrInitSubclassBinding className :: rest =>
      !className.isEmpty && completeSourceMroUsesObjectEquality rest
  | _ => false

def completeSourceMroForExactClass
    (className : String) (mro : List ReferenceEqualityMroEntry) : Bool :=
  match mro with
  | .sourceWithoutEqOrInitSubclassBinding headClass :: _ =>
      !className.isEmpty && (className == headClass) && completeSourceMroUsesObjectEquality mro
  | _ => false

structure ExactSourceConstructedReferenceLocal where
  localName : String
  className : String
  value : Term
  sourceAllocatorVerified : Bool
  constructionCompletedNormally : Bool
  runtimeClassExact : Bool

inductive NarrowReferenceEqualityLeftOrigin where
  | exactSourceConstruction (constructed : ExactSourceConstructedReferenceLocal)
  | sourceParameter (value : Term)
  | checkedExternalConstruction (value : Term)
  | dynamicValue (value : Term)

-- A heap-modeled class needs both stable ordinary attribute dispatch and stable class creation.
-- `checkedExternalHookFree` is a hash-bound provider assumption covering the same two properties;
-- it is deliberately distinct from a source proof.
inductive RawFieldReceiverMroEntry where
  | sourceWithoutHeapMutationHooks (className : String)
  | sourceWithDynamicAttributeHook (className : String)
  | sourceWithInitSubclassHook (className : String)
  | objectDefault
  | checkedExternalHookFree (className contractHash : String)
  | checkedExternalDynamicOrUnknown (className : String)
  | dynamicUnknown

def completeSourceMroUsesOrdinaryAttributeResolution :
    List RawFieldReceiverMroEntry → Bool
  | [.objectDefault] => true
  | .sourceWithoutHeapMutationHooks className :: rest =>
      !className.isEmpty && completeSourceMroUsesOrdinaryAttributeResolution rest
  | .checkedExternalHookFree className contractHash :: rest =>
      !className.isEmpty && !contractHash.isEmpty &&
        completeSourceMroUsesOrdinaryAttributeResolution rest
  | _ => false

def completeSourceMroUsesOrdinaryAttributeResolutionForClass
    (className : String) (mro : List RawFieldReceiverMroEntry) : Bool :=
  match mro with
  | .sourceWithoutHeapMutationHooks headClass :: _ =>
      !className.isEmpty && (className == headClass) &&
        completeSourceMroUsesOrdinaryAttributeResolution mro
  | .checkedExternalHookFree headClass _ :: _ =>
      !className.isEmpty && (className == headClass) &&
        completeSourceMroUsesOrdinaryAttributeResolution mro
  | _ => false

structure HeapModeledClassHookGate where
  className : String
  fieldsOrEffectsModeledOrExported : Bool
  completeMro : List RawFieldReceiverMroEntry

def heapModeledClassHookGateAccepted
    (gate : HeapModeledClassHookGate) : Bool :=
  if gate.fieldsOrEffectsModeledOrExported then
    completeSourceMroUsesOrdinaryAttributeResolutionForClass gate.className gate.completeMro
  else
    true

theorem heap_modeled_class_with_dynamic_attribute_hook_refuses
    (gate : HeapModeledClassHookGate) (hookClass : String)
    (modeled : gate.fieldsOrEffectsModeledOrExported = true)
    (mro : gate.completeMro =
      [.sourceWithDynamicAttributeHook hookClass, .objectDefault]) :
    heapModeledClassHookGateAccepted gate = false := by
  simp [heapModeledClassHookGateAccepted, modeled, mro,
    completeSourceMroUsesOrdinaryAttributeResolutionForClass]

theorem heap_modeled_class_with_inherited_dynamic_attribute_hook_refuses
    (gate : HeapModeledClassHookGate) (className baseName : String)
    (modeled : gate.fieldsOrEffectsModeledOrExported = true)
    (mro : gate.completeMro = [.sourceWithoutHeapMutationHooks className,
      .sourceWithDynamicAttributeHook baseName, .objectDefault]) :
    heapModeledClassHookGateAccepted gate = false := by
  simp [heapModeledClassHookGateAccepted, modeled, mro,
    completeSourceMroUsesOrdinaryAttributeResolutionForClass,
    completeSourceMroUsesOrdinaryAttributeResolution]

theorem heap_modeled_class_with_inherited_init_subclass_hook_refuses
    (gate : HeapModeledClassHookGate) (className baseName : String)
    (modeled : gate.fieldsOrEffectsModeledOrExported = true)
    (mro : gate.completeMro = [.sourceWithoutHeapMutationHooks className,
      .sourceWithInitSubclassHook baseName, .objectDefault]) :
    heapModeledClassHookGateAccepted gate = false := by
  simp [heapModeledClassHookGateAccepted, modeled, mro,
    completeSourceMroUsesOrdinaryAttributeResolutionForClass,
    completeSourceMroUsesOrdinaryAttributeResolution]

theorem heap_modeled_class_with_unchecked_external_mro_entry_refuses
    (gate : HeapModeledClassHookGate) (className externalBase : String)
    (modeled : gate.fieldsOrEffectsModeledOrExported = true)
    (mro : gate.completeMro = [.sourceWithoutHeapMutationHooks className,
      .checkedExternalDynamicOrUnknown externalBase]) :
    heapModeledClassHookGateAccepted gate = false := by
  simp [heapModeledClassHookGateAccepted, modeled, mro,
    completeSourceMroUsesOrdinaryAttributeResolutionForClass,
    completeSourceMroUsesOrdinaryAttributeResolution]

theorem hash_bound_checked_external_hook_free_mro_is_distinctly_accepted
    (gate : HeapModeledClassHookGate)
    (className externalBase contractHash : String)
    (modeled : gate.fieldsOrEffectsModeledOrExported = true)
    (gateClass : gate.className = className)
    (classNonempty : className.isEmpty = false)
    (externalNonempty : externalBase.isEmpty = false)
    (hashNonempty : contractHash.isEmpty = false)
    (mro : gate.completeMro = [.sourceWithoutHeapMutationHooks className,
      .checkedExternalHookFree externalBase contractHash, .objectDefault]) :
    heapModeledClassHookGateAccepted gate = true := by
  simp [heapModeledClassHookGateAccepted, modeled, gateClass, mro,
    completeSourceMroUsesOrdinaryAttributeResolutionForClass,
    completeSourceMroUsesOrdinaryAttributeResolution, classNonempty, externalNonempty,
    hashNonempty]

theorem hash_bound_checked_external_heap_class_gate_is_assumption_backed
    (gate : HeapModeledClassHookGate) (className contractHash : String)
    (modeled : gate.fieldsOrEffectsModeledOrExported = true)
    (gateClass : gate.className = className)
    (classNonempty : className.isEmpty = false)
    (hashNonempty : contractHash.isEmpty = false)
    (mro : gate.completeMro =
      [.checkedExternalHookFree className contractHash, .objectDefault]) :
    heapModeledClassHookGateAccepted gate = true := by
  simp [heapModeledClassHookGateAccepted, modeled, gateClass, mro,
    completeSourceMroUsesOrdinaryAttributeResolutionForClass,
    completeSourceMroUsesOrdinaryAttributeResolution, classNonempty, hashNonempty]

theorem heap_modeled_class_with_incomplete_or_external_mro_refuses
    (gate : HeapModeledClassHookGate)
    (modeled : gate.fieldsOrEffectsModeledOrExported = true)
    (invalid : completeSourceMroUsesOrdinaryAttributeResolutionForClass
      gate.className gate.completeMro = false) :
    heapModeledClassHookGateAccepted gate = false := by
  simp [heapModeledClassHookGateAccepted, modeled, invalid]

theorem scalar_only_class_is_not_rejected_by_heap_dynamic_attribute_gate
    (gate : HeapModeledClassHookGate)
    (scalarOnly : gate.fieldsOrEffectsModeledOrExported = false) :
    heapModeledClassHookGateAccepted gate = true := by
  simp [heapModeledClassHookGateAccepted, scalarOnly]

structure ExactRawFieldReceiverResolution where
  receiverValue : Term
  exactClassName : String
  sourceAllocatorVerified : Bool
  normalOnlyConstructorProved : Bool
  runtimeClassExactProved : Bool
  completeMro : List RawFieldReceiverMroEntry

def exactRawFieldReceiverResolutionAccepted
    (receiver : ExactRawFieldReceiverResolution) : Bool :=
  receiver.sourceAllocatorVerified &&
    receiver.normalOnlyConstructorProved &&
    receiver.runtimeClassExactProved &&
    (inferSort receiver.receiverValue == some .reference) &&
    (match receiver.completeMro with
      | .sourceWithoutHeapMutationHooks headClass :: _ =>
          (receiver.exactClassName == headClass) &&
            completeSourceMroUsesOrdinaryAttributeResolution receiver.completeMro
      | _ => false)

structure CurrentReferenceFieldChainRead where
  value : Term
  nominalClassName : String
  heapVersion : Nat
  maskVersion : Nat
  readPermissionProved : Bool
  receivers : List ExactRawFieldReceiverResolution

inductive NarrowReferenceEqualityRightOrigin where
  | sourceName (value : Term) (nominalClassName : String)
  | currentSourceFieldChain (read : CurrentReferenceFieldChainRead)
  | ordinaryCall (value : Term)
  | arbitraryExpression (value : Term)

structure NarrowReferenceEqualityRequest where
  context : NarrowReferenceEqualityContext
  operator : NarrowReferenceEqualityOperator
  leftOrigin : NarrowReferenceEqualityLeftOrigin
  rightOrigin : NarrowReferenceEqualityRightOrigin
  completeLeftMro : List ReferenceEqualityMroEntry
  currentHeapVersion : Nat
  currentMaskVersion : Nat
  allPriorObligationsProved : Bool
  identityAlreadyProvedFromCurrentAssumptions : Bool

def narrowReferenceEqualityLeftValue : NarrowReferenceEqualityLeftOrigin → Term
  | .exactSourceConstruction constructed => constructed.value
  | .sourceParameter value | .checkedExternalConstruction value | .dynamicValue value => value

def narrowReferenceEqualityLeftClass :
    NarrowReferenceEqualityLeftOrigin → Option String
  | .exactSourceConstruction constructed => some constructed.className
  | _ => none

def narrowReferenceEqualityLeftOriginAccepted
    (origin : NarrowReferenceEqualityLeftOrigin)
    (mro : List ReferenceEqualityMroEntry) : Bool :=
  match origin with
  | .exactSourceConstruction constructed =>
      !constructed.localName.isEmpty &&
        constructed.sourceAllocatorVerified &&
        constructed.constructionCompletedNormally &&
        constructed.runtimeClassExact &&
        (inferSort constructed.value == some .reference) &&
        completeSourceMroForExactClass constructed.className mro
  | _ => false

def narrowReferenceEqualityRightValue : NarrowReferenceEqualityRightOrigin → Term
  | .sourceName value _ | .ordinaryCall value | .arbitraryExpression value => value
  | .currentSourceFieldChain read => read.value

def narrowReferenceEqualityRightNominalClass :
    NarrowReferenceEqualityRightOrigin → Option String
  | .sourceName _ className => some className
  | .currentSourceFieldChain read => some read.nominalClassName
  | .ordinaryCall _ | .arbitraryExpression _ => none

def narrowReferenceEqualityRightOriginAccepted
    (origin : NarrowReferenceEqualityRightOrigin)
    (currentHeapVersion currentMaskVersion : Nat) : Bool :=
  match origin with
  | .sourceName value className =>
      !className.isEmpty && (inferSort value == some .reference)
  | .currentSourceFieldChain read =>
      read.readPermissionProved &&
        !read.receivers.isEmpty &&
        read.receivers.all exactRawFieldReceiverResolutionAccepted &&
        (read.heapVersion == currentHeapVersion) &&
        (read.maskVersion == currentMaskVersion) &&
        !read.nominalClassName.isEmpty &&
        (inferSort read.value == some .reference)
  | .ordinaryCall _ | .arbitraryExpression _ => false

def narrowReferenceEqualityRequestStructurallySupported
    (request : NarrowReferenceEqualityRequest) : Bool :=
  (match request.context with | .positiveAssert => true | _ => false) &&
    (match request.operator with | .equal => true | .notEqual => false) &&
    request.allPriorObligationsProved &&
    narrowReferenceEqualityLeftOriginAccepted request.leftOrigin request.completeLeftMro &&
    narrowReferenceEqualityRightOriginAccepted request.rightOrigin
      request.currentHeapVersion request.currentMaskVersion

def narrowReferenceEqualityRequestWellFormed
    (request : NarrowReferenceEqualityRequest) : Bool :=
  narrowReferenceEqualityRequestStructurallySupported request &&
    request.identityAlreadyProvedFromCurrentAssumptions

def lowerNarrowReferenceEquality
  (request : NarrowReferenceEqualityRequest) : Option Term :=
  if narrowReferenceEqualityRequestWellFormed request then
    some (.equal (narrowReferenceEqualityLeftValue request.leftOrigin)
      (narrowReferenceEqualityRightValue request.rightOrigin))
  else
    none

inductive NarrowReferenceEqualityDisposition where
  | proved
  | unresolved
  | refused

def classifyNarrowReferenceEquality
    (request : NarrowReferenceEqualityRequest) : NarrowReferenceEqualityDisposition :=
  if !narrowReferenceEqualityRequestStructurallySupported request then .refused
  else if request.identityAlreadyProvedFromCurrentAssumptions then .proved
  else .unresolved

theorem accepted_narrow_reference_equality_lowers_only_identity
    (request : NarrowReferenceEqualityRequest)
    (accepted : narrowReferenceEqualityRequestWellFormed request = true) :
    lowerNarrowReferenceEquality request = some (.equal
      (narrowReferenceEqualityLeftValue request.leftOrigin)
      (narrowReferenceEqualityRightValue request.rightOrigin)) := by
  simp [lowerNarrowReferenceEquality, accepted]

theorem accepted_narrow_reference_equality_is_bool_typed
    (left right : Term)
    (leftTyped : inferSort left = some .reference)
    (rightTyped : inferSort right = some .reference) :
    inferSort (.equal left right) = some .bool := by
  simp [inferSort, leftTyped, rightTyped, instBEqValueSort, valueSortBeq]

theorem upstream_line59_identity_evidence_proves_equality_assertion
    (request : NarrowReferenceEqualityRequest)
    (accepted : narrowReferenceEqualityRequestWellFormed request = true) :
    classifyNarrowReferenceEquality request = .proved := by
  have structural : narrowReferenceEqualityRequestStructurallySupported request = true := by
    have parts : narrowReferenceEqualityRequestStructurallySupported request = true ∧
        request.identityAlreadyProvedFromCurrentAssumptions = true := by
      simpa [narrowReferenceEqualityRequestWellFormed] using accepted
    exact parts.1
  have identity : request.identityAlreadyProvedFromCurrentAssumptions = true := by
    have parts : narrowReferenceEqualityRequestStructurallySupported request = true ∧
        request.identityAlreadyProvedFromCurrentAssumptions = true := by
      simpa [narrowReferenceEqualityRequestWellFormed] using accepted
    exact parts.2
  simp [classifyNarrowReferenceEquality, structural, identity]

theorem upstream_line61_without_identity_proof_remains_unresolved
    (request : NarrowReferenceEqualityRequest)
    (structural : narrowReferenceEqualityRequestStructurallySupported request = true)
    (noIdentity : request.identityAlreadyProvedFromCurrentAssumptions = false) :
    classifyNarrowReferenceEquality request = .unresolved := by
  simp [classifyNarrowReferenceEquality, structural, noIdentity]

theorem custom_eq_override_refuses_narrow_reference_equality
    (request : NarrowReferenceEqualityRequest) (className leftClass localName : String)
    (leftValue : Term)
    (leftOrigin : request.leftOrigin = .exactSourceConstruction {
      localName := localName, className := leftClass, value := leftValue,
      sourceAllocatorVerified := true, constructionCompletedNormally := true,
      runtimeClassExact := true })
    (mro : request.completeLeftMro = [.sourceWithEqOverride className, .objectDefault]) :
    lowerNarrowReferenceEquality request = none := by
  simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
    narrowReferenceEqualityRequestStructurallySupported,
    leftOrigin, mro, narrowReferenceEqualityLeftOriginAccepted,
    completeSourceMroForExactClass]

theorem inherited_init_subclass_refuses_narrow_reference_equality
    (request : NarrowReferenceEqualityRequest) (leftClass baseClass localName : String)
    (leftValue : Term)
    (leftOrigin : request.leftOrigin = .exactSourceConstruction {
      localName := localName, className := leftClass, value := leftValue,
      sourceAllocatorVerified := true, constructionCompletedNormally := true,
      runtimeClassExact := true })
    (mro : request.completeLeftMro =
      [.sourceWithoutEqOrInitSubclassBinding leftClass,
        .sourceWithInitSubclassBinding baseClass, .objectDefault]) :
    lowerNarrowReferenceEquality request = none := by
  simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
    narrowReferenceEqualityRequestStructurallySupported,
    leftOrigin, mro, narrowReferenceEqualityLeftOriginAccepted,
    completeSourceMroForExactClass, completeSourceMroUsesObjectEquality]

theorem incomplete_external_or_dynamic_mro_refuses_narrow_reference_equality
    (request : NarrowReferenceEqualityRequest)
    (constructed : ExactSourceConstructedReferenceLocal)
    (leftOrigin : request.leftOrigin = .exactSourceConstruction constructed)
    (rejectedMro : completeSourceMroForExactClass
      constructed.className request.completeLeftMro = false) :
    lowerNarrowReferenceEquality request = none := by
  simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
    narrowReferenceEqualityRequestStructurallySupported,
    leftOrigin, narrowReferenceEqualityLeftOriginAccepted, rejectedMro]

theorem ordinary_call_refuses_ghost_reference_equality_operand
    (request : NarrowReferenceEqualityRequest) (value : Term)
    (rightOrigin : request.rightOrigin = .ordinaryCall value) :
    lowerNarrowReferenceEquality request = none := by
  simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
    narrowReferenceEqualityRequestStructurallySupported,
    rightOrigin, narrowReferenceEqualityRightOriginAccepted]

theorem stale_or_unpermitted_field_chain_refuses_reference_equality
    (request : NarrowReferenceEqualityRequest) (read : CurrentReferenceFieldChainRead)
    (rightOrigin : request.rightOrigin = .currentSourceFieldChain read)
    (invalidRead : read.readPermissionProved = false ∨
      read.heapVersion ≠ request.currentHeapVersion ∨
      read.maskVersion ≠ request.currentMaskVersion) :
    lowerNarrowReferenceEquality request = none := by
  rcases invalidRead with unpermitted | staleHeap | staleMask
  · simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
      narrowReferenceEqualityRequestStructurallySupported,
      rightOrigin, narrowReferenceEqualityRightOriginAccepted, unpermitted]
  · simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
      narrowReferenceEqualityRequestStructurallySupported,
      rightOrigin, narrowReferenceEqualityRightOriginAccepted, staleHeap]
  · simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
      narrowReferenceEqualityRequestStructurallySupported,
      rightOrigin, narrowReferenceEqualityRightOriginAccepted, staleMask]

theorem dynamic_attribute_hook_refuses_reference_equality_field_chain
    (request : NarrowReferenceEqualityRequest) (read : CurrentReferenceFieldChainRead)
    (rightOrigin : request.rightOrigin = .currentSourceFieldChain read)
    (dynamicHook : read.receivers.all exactRawFieldReceiverResolutionAccepted = false) :
    lowerNarrowReferenceEquality request = none := by
  simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
    narrowReferenceEqualityRequestStructurallySupported, rightOrigin,
    narrowReferenceEqualityRightOriginAccepted, dynamicHook]

theorem field_chain_without_exact_receiver_provenance_refuses_reference_equality
    (request : NarrowReferenceEqualityRequest) (read : CurrentReferenceFieldChainRead)
    (rightOrigin : request.rightOrigin = .currentSourceFieldChain read)
    (noReceivers : read.receivers = []) :
    lowerNarrowReferenceEquality request = none := by
  simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
    narrowReferenceEqualityRequestStructurallySupported, rightOrigin,
    narrowReferenceEqualityRightOriginAccepted, noReceivers]

theorem not_equal_operator_refuses_narrow_reference_equality
    (request : NarrowReferenceEqualityRequest)
    (notEqual : request.operator = .notEqual) :
    lowerNarrowReferenceEquality request = none := by
  simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
    narrowReferenceEqualityRequestStructurallySupported, notEqual]

theorem unproved_prior_obligation_refuses_narrow_reference_equality
    (request : NarrowReferenceEqualityRequest)
    (unproved : request.allPriorObligationsProved = false) :
    lowerNarrowReferenceEquality request = none := by
  simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
    narrowReferenceEqualityRequestStructurallySupported, unproved]

theorem non_assert_context_refuses_narrow_reference_equality
    (request : NarrowReferenceEqualityRequest)
    (requiresContext : request.context = .requiresClause) :
    lowerNarrowReferenceEquality request = none := by
  simp [lowerNarrowReferenceEquality, narrowReferenceEqualityRequestWellFormed,
    narrowReferenceEqualityRequestStructurallySupported,
    requiresContext]

/-!
## Exact bilateral source/object reference equality

This is the v36 branch.  Its syntax deliberately preserves v35's asymmetry: the left operand is a
named exact source construction, while only the right operand may be a name or raw field chain.
Both operands nevertheless carry independent frontend evidence of an exact runtime source class.
Each complete source MRO ends at `object` and contains no class-scope `__eq__` or
`__init_subclass__` binding of any kind.  The latter is a frontend premise that class creation could
not inject equality or attribute hooks.  Under those premises Python's
two dispatch attempts both use `object.__eq__`, so the IR identity term is exact for the supported
slice: same identity proves, distinct identity refutes, and unknown identity remains unresolved.

A raw field-chain operand separately retains the current heap/mask read, permission, exact
receiver, normal source allocation, and hook-free MRO premises above.  Calls, properties,
external/dynamic classes, incomplete MROs, optional/scalar values, and other contexts/operators
remain outside this rule.  This is an IR/frontend-premise model, not Python correspondence.
General left field-chain equality is a future slice.
-/

inductive BilateralEqualityMroEntry where
  | sourceClassWithoutEqOrInitSubclassBinding (className : String)
  | sourceClassWithEqBinding (className : String)
  | sourceClassWithInitSubclassBinding (className : String)
  | objectDefault
  | checkedExternal (className contractHash : String)
  | dynamicUnknown

def completeSourceMroUsesOnlyObjectEquality : List BilateralEqualityMroEntry → Bool
  | [.objectDefault] => true
  | .sourceClassWithoutEqOrInitSubclassBinding className :: rest =>
      !className.isEmpty && completeSourceMroUsesOnlyObjectEquality rest
  | _ => false

def completeSourceEqualityMroForExactClass
    (className : String) (mro : List BilateralEqualityMroEntry) : Bool :=
  match mro with
  | .sourceClassWithoutEqOrInitSubclassBinding headClass :: _ =>
      !className.isEmpty && (className == headClass) &&
        completeSourceMroUsesOnlyObjectEquality mro
  | _ => false

structure ExactSourceReferenceName where
  value : Term
  exactClassName : String
  runtimeClassExactSourceProved : Bool
  completeMro : List BilateralEqualityMroEntry

structure ExactConstructedLeftReferenceName where
  localName : String
  value : Term
  exactClassName : String
  namedSourceConstructionProved : Bool
  -- This is normal completion on the reached path, not a claim that the constructor has no
  -- exceptional outcome on every path.
  constructionCompletedNormallyOnReachedPath : Bool
  runtimeClassExactSourceProved : Bool
  completeMro : List BilateralEqualityMroEntry

structure ExactSourceReferenceFieldChain where
  read : CurrentReferenceFieldChainRead
  exactResultClassName : String
  runtimeResultClassExactSourceProved : Bool
  completeResultMro : List BilateralEqualityMroEntry

inductive ExactBilateralReferenceOperand where
  | sourceName (operand : ExactSourceReferenceName)
  | currentRawFieldChain (operand : ExactSourceReferenceFieldChain)
  | propertyOrCall (value : Term)
  | externalOrDynamic (value : Term)

def exactBilateralReferenceOperandValue : ExactBilateralReferenceOperand → Term
  | .sourceName operand => operand.value
  | .currentRawFieldChain operand => operand.read.value
  | .propertyOrCall value | .externalOrDynamic value => value

def exactSourceReferenceNameAccepted (operand : ExactSourceReferenceName) : Bool :=
  operand.runtimeClassExactSourceProved &&
    (inferSort operand.value == some .reference) &&
    completeSourceEqualityMroForExactClass operand.exactClassName operand.completeMro

def exactConstructedLeftReferenceNameAccepted
    (operand : ExactConstructedLeftReferenceName) : Bool :=
  !operand.localName.isEmpty &&
    operand.namedSourceConstructionProved &&
    operand.constructionCompletedNormallyOnReachedPath &&
    operand.runtimeClassExactSourceProved &&
    (inferSort operand.value == some .reference) &&
    completeSourceEqualityMroForExactClass operand.exactClassName operand.completeMro

def exactSourceReferenceFieldChainAccepted
    (operand : ExactSourceReferenceFieldChain)
    (currentHeapVersion currentMaskVersion : Nat) : Bool :=
  narrowReferenceEqualityRightOriginAccepted (.currentSourceFieldChain operand.read)
      currentHeapVersion currentMaskVersion &&
    operand.runtimeResultClassExactSourceProved &&
    completeSourceEqualityMroForExactClass operand.exactResultClassName operand.completeResultMro

def exactBilateralReferenceOperandAccepted
    (operand : ExactBilateralReferenceOperand)
    (currentHeapVersion currentMaskVersion : Nat) : Bool :=
  match operand with
  | .sourceName name => exactSourceReferenceNameAccepted name
  | .currentRawFieldChain field =>
      exactSourceReferenceFieldChainAccepted field currentHeapVersion currentMaskVersion
  | .propertyOrCall _ | .externalOrDynamic _ => false

structure ExactBilateralReferenceEqualityRequest where
  context : NarrowReferenceEqualityContext
  operator : NarrowReferenceEqualityOperator
  left : ExactConstructedLeftReferenceName
  right : ExactBilateralReferenceOperand
  currentHeapVersion : Nat
  currentMaskVersion : Nat
  allPriorObligationsProved : Bool

def exactBilateralReferenceEqualityRequestWellFormed
    (request : ExactBilateralReferenceEqualityRequest) : Bool :=
  (match request.context with | .positiveAssert => true | _ => false) &&
    (match request.operator with | .equal => true | .notEqual => false) &&
    request.allPriorObligationsProved &&
    exactConstructedLeftReferenceNameAccepted request.left &&
    exactBilateralReferenceOperandAccepted request.right request.currentHeapVersion
      request.currentMaskVersion

def lowerExactBilateralReferenceEquality
    (request : ExactBilateralReferenceEqualityRequest) : Option Term :=
  if exactBilateralReferenceEqualityRequestWellFormed request then
    some (.equal request.left.value
      (exactBilateralReferenceOperandValue request.right))
  else
    none

inductive BilateralIdentityEvidence where
  | provedSame
  | provedDistinct
  | unknown

inductive ExactBilateralReferenceEqualityDisposition where
  | proved
  | refuted
  | unresolved
  | refused

def classifyExactBilateralReferenceEquality
    (request : ExactBilateralReferenceEqualityRequest)
    (identity : BilateralIdentityEvidence) : ExactBilateralReferenceEqualityDisposition :=
  match lowerExactBilateralReferenceEquality request with
  | none => .refused
  | some _ => match identity with
    | .provedSame => .proved
    | .provedDistinct => .refuted
    | .unknown => .unresolved

theorem accepted_exact_bilateral_equality_lowers_to_identity
    (request : ExactBilateralReferenceEqualityRequest)
    (accepted : exactBilateralReferenceEqualityRequestWellFormed request = true) :
    lowerExactBilateralReferenceEquality request = some (.equal
      request.left.value
      (exactBilateralReferenceOperandValue request.right)) := by
  simp [lowerExactBilateralReferenceEquality, accepted]

theorem exact_bilateral_same_identity_proves
    (request : ExactBilateralReferenceEqualityRequest)
    (accepted : exactBilateralReferenceEqualityRequestWellFormed request = true) :
    classifyExactBilateralReferenceEquality request .provedSame = .proved := by
  simp [classifyExactBilateralReferenceEquality,
    accepted_exact_bilateral_equality_lowers_to_identity request accepted]

theorem exact_bilateral_distinct_identity_refutes
    (request : ExactBilateralReferenceEqualityRequest)
    (accepted : exactBilateralReferenceEqualityRequestWellFormed request = true) :
    classifyExactBilateralReferenceEquality request .provedDistinct = .refuted := by
  simp [classifyExactBilateralReferenceEquality,
    accepted_exact_bilateral_equality_lowers_to_identity request accepted]

theorem exact_bilateral_unknown_identity_is_unresolved
    (request : ExactBilateralReferenceEqualityRequest)
    (accepted : exactBilateralReferenceEqualityRequestWellFormed request = true) :
    classifyExactBilateralReferenceEquality request .unknown = .unresolved := by
  simp [classifyExactBilateralReferenceEquality,
    accepted_exact_bilateral_equality_lowers_to_identity request accepted]

theorem any_class_scope_eq_binding_refuses_exact_bilateral_equality
    (request : ExactBilateralReferenceEqualityRequest)
    (className : String)
    (mro : request.left.completeMro =
      [.sourceClassWithEqBinding className, .objectDefault]) :
    lowerExactBilateralReferenceEquality request = none := by
  simp [lowerExactBilateralReferenceEquality,
    exactBilateralReferenceEqualityRequestWellFormed,
    exactConstructedLeftReferenceNameAccepted, mro,
    completeSourceEqualityMroForExactClass]

theorem right_class_scope_eq_binding_refuses_exact_bilateral_equality
    (request : ExactBilateralReferenceEqualityRequest)
    (right : ExactSourceReferenceName) (className : String)
    (rightOperand : request.right = .sourceName right)
    (mro : right.completeMro =
      [.sourceClassWithEqBinding className, .objectDefault]) :
    lowerExactBilateralReferenceEquality request = none := by
  simp [lowerExactBilateralReferenceEquality,
    exactBilateralReferenceEqualityRequestWellFormed, rightOperand,
    exactBilateralReferenceOperandAccepted, exactSourceReferenceNameAccepted,
    mro, completeSourceEqualityMroForExactClass]

theorem inherited_init_subclass_binding_refuses_exact_bilateral_equality
    (request : ExactBilateralReferenceEqualityRequest)
    (leftClass baseClass : String)
    (mro : request.left.completeMro =
      [.sourceClassWithoutEqOrInitSubclassBinding leftClass,
        .sourceClassWithInitSubclassBinding baseClass, .objectDefault]) :
    lowerExactBilateralReferenceEquality request = none := by
  simp [lowerExactBilateralReferenceEquality,
    exactBilateralReferenceEqualityRequestWellFormed,
    exactConstructedLeftReferenceNameAccepted, mro,
    completeSourceEqualityMroForExactClass,
    completeSourceMroUsesOnlyObjectEquality]

theorem checked_external_right_mro_refuses_exact_bilateral_equality
    (request : ExactBilateralReferenceEqualityRequest)
    (right : ExactSourceReferenceName) (className contractHash : String)
    (rightOperand : request.right = .sourceName right)
    (mro : right.completeMro =
      [.checkedExternal className contractHash, .objectDefault]) :
    lowerExactBilateralReferenceEquality request = none := by
  simp [lowerExactBilateralReferenceEquality,
    exactBilateralReferenceEqualityRequestWellFormed, rightOperand,
    exactBilateralReferenceOperandAccepted, exactSourceReferenceNameAccepted,
    mro, completeSourceEqualityMroForExactClass]

theorem external_or_dynamic_operand_refuses_exact_bilateral_equality
    (request : ExactBilateralReferenceEqualityRequest) (value : Term)
    (right : request.right = .externalOrDynamic value) :
    lowerExactBilateralReferenceEquality request = none := by
  simp [lowerExactBilateralReferenceEquality,
    exactBilateralReferenceEqualityRequestWellFormed, right,
    exactBilateralReferenceOperandAccepted]

theorem nonexact_left_runtime_class_refuses_exact_bilateral_equality
    (request : ExactBilateralReferenceEqualityRequest)
    (nonexact : request.left.runtimeClassExactSourceProved = false) :
    lowerExactBilateralReferenceEquality request = none := by
  simp [lowerExactBilateralReferenceEquality,
    exactBilateralReferenceEqualityRequestWellFormed,
    exactConstructedLeftReferenceNameAccepted, nonexact]

/-!
## Standalone nested one-argument source calls

This is the v37 state-ordering model for a standalone expression statement such as
`root.receiver().set_value(argument.impure().field)`.  The receiver reference expression is
evaluated first, the one positional nominal-reference argument is evaluated from the receiver's
exit heap and mask, and only then is the terminal Unit-returning source method applied to the two
saved reference values.  Receiver and argument evaluation reuse the v34 source field/zero-argument
call chain above.  They may advance heap and mask independently.

The terminal application does not assume that receiver and argument are distinct.  Its frontend
premise says that summary rebinding, preconditions, permission effects, complete modifications,
and frames were instantiated for the actual saved terms under their real alias relation.  Every
accepted call is source-owned, normal-only, instance-dispatched, has exactly one non-optional
nominal-reference parameter without a default, and returns Unit.  Keywords, properties, optional
or scalar arguments, external/dynamic or exceptional calls, and ghost-expression use are refused
by frontend premises.  This section proves only the finite IR transition/evaluation-order algebra;
it does not prove Python evaluation correspondence, alias analysis, summary truth, or exception
freedom from source.
-/

structure StandaloneReferenceExpressionRoot where
  value : Term
  nominalClass : String
  exactNonOptionalNominalReference : Bool
  origin : ReferenceChainMemberOrigin

def standaloneReferenceExpressionRootWellFormed
    (root : StandaloneReferenceExpressionRoot) : Bool :=
  (inferSort root.value == some .reference) &&
    !root.nominalClass.isEmpty &&
    root.exactNonOptionalNominalReference &&
    referenceChainMemberOriginIsVerifiedSource root.origin

structure StandaloneNestedCallSeed where
  heap : Nat
  mask : Nat
  obligations : List Term
  assumptions : List Term

def startStandaloneReferenceExpression
    (seed : StandaloneNestedCallSeed)
    (root : StandaloneReferenceExpressionRoot) : ReferenceChainTrace :=
  {
    state := {
      heap := seed.heap
      mask := seed.mask
      value := root.value
      nominalClass := root.nominalClass
    }
    obligations := seed.obligations
    assumptions := seed.assumptions
  }

def continueStandaloneReferenceExpression
    (previous : ReferenceChainTrace)
    (root : StandaloneReferenceExpressionRoot) : ReferenceChainTrace :=
  {
    state := {
      heap := previous.state.heap
      mask := previous.state.mask
      value := root.value
      nominalClass := root.nominalClass
    }
    obligations := previous.obligations
    assumptions := previous.assumptions
  }

inductive StandaloneNestedCallAliasRelation where
  | sameReference
  | distinctReferences
  | unknown

structure StandaloneUnitReferenceMethodSummary where
  ownerClass : String
  methodName : String
  parameterClass : String
  summaryOrigin : ReferenceChainMemberOrigin
  sourceInstanceMethod : Bool
  exactlyOnePositionalNominalReferenceParameter : Bool
  parameterNonOptional : Bool
  parameterHasNoDefault : Bool
  unitNormalReturn : Bool
  noExceptionalOutcome : Bool
  virtualDispatchResolved : Bool
  completePermissionEffects : Bool
  completeModificationSetAndFrames : Bool
  noHeapWrites : Bool
  netPermissionNeutral : Bool

structure StandaloneUnitReferenceMethodApplication where
  summary : StandaloneUnitReferenceMethodSummary
  exitHeap : Nat
  exitMask : Nat
  preconditionObligations : Term → Term → List Term
  transitionAndPostconditionAssumptions : Term → Term → Nat → Nat → List Term
  argumentNominalCompatibilityProved : Bool
  actualAliasingAccountedFor : Bool
  aliasRelation : StandaloneNestedCallAliasRelation
  heapTransitionAndFramesProved : Bool
  permissionTransitionProved : Bool

structure StandaloneNestedCallSyntax where
  standaloneExpressionStatement : Bool
  moduleHeapFunctionContext : Bool
  positiveRuntimeContext : Bool
  exactlyOnePositionalArgument : Bool
  noKeywords : Bool
  noPropertyOrDynamicDispatch : Bool

def standaloneUnitReferenceMethodSummaryWellFormed
    (summary : StandaloneUnitReferenceMethodSummary) : Bool :=
  !summary.ownerClass.isEmpty &&
    !summary.methodName.isEmpty &&
    !summary.parameterClass.isEmpty &&
    referenceChainMemberOriginIsVerifiedSource summary.summaryOrigin &&
    summary.sourceInstanceMethod &&
    summary.exactlyOnePositionalNominalReferenceParameter &&
    summary.parameterNonOptional &&
    summary.parameterHasNoDefault &&
    summary.unitNormalReturn &&
    summary.noExceptionalOutcome &&
    summary.virtualDispatchResolved &&
    summary.completePermissionEffects &&
    summary.completeModificationSetAndFrames

def standaloneNestedCallSyntaxAccepted (callSyntax : StandaloneNestedCallSyntax) : Bool :=
  callSyntax.standaloneExpressionStatement &&
    callSyntax.moduleHeapFunctionContext &&
    callSyntax.positiveRuntimeContext &&
    callSyntax.exactlyOnePositionalArgument &&
    callSyntax.noKeywords &&
    callSyntax.noPropertyOrDynamicDispatch

structure StandaloneStatementTrace where
  heap : Nat
  mask : Nat
  obligations : List Term
  assumptions : List Term

def standaloneUnitReferenceMethodApplicationWellFormed
    (receiver argument : ReferenceChainTrace)
    (application : StandaloneUnitReferenceMethodApplication) : Bool :=
  (inferSort receiver.state.value == some .reference) &&
    (inferSort argument.state.value == some .reference) &&
    (receiver.state.nominalClass == application.summary.ownerClass) &&
    standaloneUnitReferenceMethodSummaryWellFormed application.summary &&
    application.argumentNominalCompatibilityProved &&
    application.actualAliasingAccountedFor &&
    allBool (application.preconditionObligations
      receiver.state.value argument.state.value) &&
    allBool (application.transitionAndPostconditionAssumptions
      receiver.state.value argument.state.value argument.state.heap argument.state.mask) &&
    (if application.summary.noHeapWrites then
      application.exitHeap == argument.state.heap
    else
      (application.exitHeap != argument.state.heap) &&
        application.heapTransitionAndFramesProved) &&
    (if application.summary.netPermissionNeutral then
      application.exitMask == argument.state.mask
    else
      (application.exitMask != argument.state.mask) &&
        application.permissionTransitionProved)

def applyStandaloneUnitReferenceMethod
    (receiver argument : ReferenceChainTrace)
    (application : StandaloneUnitReferenceMethodApplication) :
    Option StandaloneStatementTrace :=
  if standaloneUnitReferenceMethodApplicationWellFormed receiver argument application then
    some {
      heap := application.exitHeap
      mask := application.exitMask
      obligations := argument.obligations ++ application.preconditionObligations
        receiver.state.value argument.state.value
      assumptions := argument.assumptions ++
        application.transitionAndPostconditionAssumptions
          receiver.state.value argument.state.value argument.state.heap argument.state.mask
    }
  else
    none

inductive StandaloneNestedCallFailurePhase where
  | syntaxOrRoot
  | receiver
  | argument
  | terminalStaticValidation
  | terminalTransition

inductive StandaloneNestedCallResult where
  | completed (trace : StandaloneStatementTrace)
  | refused (phase : StandaloneNestedCallFailurePhase) (trace : ReferenceChainTrace)

structure StandaloneNestedCallRequest where
  callSyntax : StandaloneNestedCallSyntax
  seed : StandaloneNestedCallSeed
  receiverRoot : StandaloneReferenceExpressionRoot
  receiverSteps : List ReferenceChainStep
  argumentRoot : StandaloneReferenceExpressionRoot
  argumentSteps : List ReferenceChainStep
  terminal : StandaloneUnitReferenceMethodApplication

def executeStandaloneNestedCall
    (request : StandaloneNestedCallRequest) : StandaloneNestedCallResult :=
  let initialReceiver := startStandaloneReferenceExpression request.seed request.receiverRoot
  if !standaloneNestedCallSyntaxAccepted request.callSyntax ||
      !standaloneReferenceExpressionRootWellFormed request.receiverRoot ||
      !standaloneReferenceExpressionRootWellFormed request.argumentRoot then
    .refused .syntaxOrRoot initialReceiver
  else
    match executeReferenceChain (.running initialReceiver) request.receiverSteps with
    | .halted stopped => .refused .receiver stopped
    | .running receiver =>
        if !standaloneUnitReferenceMethodSummaryWellFormed request.terminal.summary then
          .refused .terminalStaticValidation receiver
        else
          let initialArgument :=
            continueStandaloneReferenceExpression receiver request.argumentRoot
          match executeReferenceChain (.running initialArgument) request.argumentSteps with
          | .halted stopped => .refused .argument stopped
          | .running argument =>
              match applyStandaloneUnitReferenceMethod receiver argument request.terminal with
              | none => .refused .terminalTransition argument
              | some completed => .completed completed

theorem receiver_failure_prevents_argument_and_terminal_evaluation
    (request : StandaloneNestedCallRequest)
    (syntaxProof : standaloneNestedCallSyntaxAccepted request.callSyntax = true)
    (receiverRoot : standaloneReferenceExpressionRootWellFormed request.receiverRoot = true)
    (argumentRoot : standaloneReferenceExpressionRootWellFormed request.argumentRoot = true)
    (stopped : ReferenceChainTrace)
    (receiverFailure : executeReferenceChain
      (.running (startStandaloneReferenceExpression request.seed request.receiverRoot))
      request.receiverSteps = .halted stopped) :
    executeStandaloneNestedCall request = .refused .receiver stopped := by
  simp [executeStandaloneNestedCall, syntaxProof, receiverRoot, argumentRoot, receiverFailure]

theorem argument_failure_occurs_after_receiver_exit
    (request : StandaloneNestedCallRequest)
    (syntaxProof : standaloneNestedCallSyntaxAccepted request.callSyntax = true)
    (receiverRoot : standaloneReferenceExpressionRootWellFormed request.receiverRoot = true)
    (argumentRoot : standaloneReferenceExpressionRootWellFormed request.argumentRoot = true)
    (receiver stopped : ReferenceChainTrace)
    (receiverSuccess : executeReferenceChain
      (.running (startStandaloneReferenceExpression request.seed request.receiverRoot))
      request.receiverSteps = .running receiver)
    (terminalStatic : standaloneUnitReferenceMethodSummaryWellFormed
      request.terminal.summary = true)
    (argumentFailure : executeReferenceChain
      (.running (continueStandaloneReferenceExpression receiver request.argumentRoot))
      request.argumentSteps = .halted stopped) :
    executeStandaloneNestedCall request = .refused .argument stopped := by
  simp [executeStandaloneNestedCall, syntaxProof, receiverRoot, argumentRoot,
    receiverSuccess, terminalStatic, argumentFailure]

theorem terminal_application_uses_post_argument_versions_and_saved_receiver
    (receiver argument : ReferenceChainTrace)
    (application : StandaloneUnitReferenceMethodApplication)
    (accepted : standaloneUnitReferenceMethodApplicationWellFormed
      receiver argument application = true) :
    applyStandaloneUnitReferenceMethod receiver argument application = some {
      heap := application.exitHeap
      mask := application.exitMask
      obligations := argument.obligations ++ application.preconditionObligations
        receiver.state.value argument.state.value
      assumptions := argument.assumptions ++
        application.transitionAndPostconditionAssumptions
          receiver.state.value argument.state.value argument.state.heap argument.state.mask
    } := by
  simp [applyStandaloneUnitReferenceMethod, accepted]

theorem unknown_aliasing_is_not_replaced_by_a_distinctness_assumption
    (receiver argument : ReferenceChainTrace)
    (application : StandaloneUnitReferenceMethodApplication)
    (unknownAlias : application.aliasRelation = .unknown) :
    standaloneUnitReferenceMethodApplicationWellFormed receiver argument application =
      standaloneUnitReferenceMethodApplicationWellFormed receiver argument
        { application with aliasRelation := .unknown } := by
  cases application
  simp_all [standaloneUnitReferenceMethodApplicationWellFormed]

theorem exceptional_terminal_application_is_not_well_formed
    (receiver argument : ReferenceChainTrace)
    (application : StandaloneUnitReferenceMethodApplication)
    (exceptional : application.summary.noExceptionalOutcome = false) :
    applyStandaloneUnitReferenceMethod receiver argument application = none := by
  simp [applyStandaloneUnitReferenceMethod,
    standaloneUnitReferenceMethodApplicationWellFormed,
    standaloneUnitReferenceMethodSummaryWellFormed, exceptional]

theorem exceptional_terminal_is_statically_refused_after_receiver_before_argument
    (request : StandaloneNestedCallRequest)
    (syntaxProof : standaloneNestedCallSyntaxAccepted request.callSyntax = true)
    (receiverRoot : standaloneReferenceExpressionRootWellFormed request.receiverRoot = true)
    (argumentRoot : standaloneReferenceExpressionRootWellFormed request.argumentRoot = true)
    (receiver : ReferenceChainTrace)
    (receiverSuccess : executeReferenceChain
      (.running (startStandaloneReferenceExpression request.seed request.receiverRoot))
      request.receiverSteps = .running receiver)
    (exceptional : request.terminal.summary.noExceptionalOutcome = false) :
    executeStandaloneNestedCall request =
      .refused .terminalStaticValidation receiver := by
  simp [executeStandaloneNestedCall, syntaxProof, receiverRoot, argumentRoot,
    receiverSuccess, standaloneUnitReferenceMethodSummaryWellFormed, exceptional]

theorem ghost_nested_call_refuses_before_receiver_evaluation
    (request : StandaloneNestedCallRequest)
    (ghost : request.callSyntax.positiveRuntimeContext = false) :
    executeStandaloneNestedCall request = .refused .syntaxOrRoot
      (startStandaloneReferenceExpression request.seed request.receiverRoot) := by
  simp [executeStandaloneNestedCall, standaloneNestedCallSyntaxAccepted, ghost]

theorem keyword_nested_call_refuses_before_receiver_evaluation
    (request : StandaloneNestedCallRequest)
    (keyword : request.callSyntax.noKeywords = false) :
    executeStandaloneNestedCall request = .refused .syntaxOrRoot
      (startStandaloneReferenceExpression request.seed request.receiverRoot) := by
  simp [executeStandaloneNestedCall, standaloneNestedCallSyntaxAccepted, keyword]

theorem method_body_nested_call_is_outside_v37
    (request : StandaloneNestedCallRequest)
    (notModuleHeapFunction : request.callSyntax.moduleHeapFunctionContext = false) :
    executeStandaloneNestedCall request = .refused .syntaxOrRoot
      (startStandaloneReferenceExpression request.seed request.receiverRoot) := by
  simp [executeStandaloneNestedCall, standaloneNestedCallSyntaxAccepted, notModuleHeapFunction]

/-!
## Finite caller-root frame instantiation

This is the first v38 rule.  A normal source call may instantiate frame equalities only for the
finite typed source roots and effective fields supplied by the caller frontend.  The source summary
must have one complete normal outcome and a proved complete direct-plus-transitive modification
set.  A field is framed only when its name is absent from that set.  The conservative name test is
sound even when the caller root aliases the call receiver: a possibly modified field name never
receives a frame.  Checked-external or dynamic roots, members, and summaries are structurally
ineligible rather than being converted into source facts.

The model constructs typed pre/post heap equalities and proves refusal non-extension.  It does not
prove frontend root enumeration, Python execution correspondence, summary/modification
completeness, alias analysis, or semantic framing.
-/

inductive CallerRootFrameOrigin where
  | verifiedSource (provider : String)
  | checkedExternal (provider contractHash : String)
  | dynamicUnknown

def callerRootFrameOriginIsVerifiedSource : CallerRootFrameOrigin → Bool
  | .verifiedSource provider => !provider.isEmpty
  | .checkedExternal _ _ | .dynamicUnknown => false

structure CallerRootFrameSummary where
  methodName : String
  origin : CallerRootFrameOrigin
  completeNormalOutcome : Bool
  noExceptionalOutcome : Bool
  completeTransitiveModificationSetProved : Bool
  completeTransitiveModifiedFields : List String

def callerRootFrameSummaryWellFormed (summary : CallerRootFrameSummary) : Bool :=
  !summary.methodName.isEmpty &&
    callerRootFrameOriginIsVerifiedSource summary.origin &&
    summary.completeNormalOutcome &&
    summary.noExceptionalOutcome &&
    summary.completeTransitiveModificationSetProved

structure CallerRootFieldFrameRequest where
  preHeap : Nat
  postHeap : Nat
  rootName : String
  rootValue : Term
  ownerClass : String
  fieldName : String
  fieldSort : ValueSort
  rootOrigin : CallerRootFrameOrigin
  fieldOrigin : CallerRootFrameOrigin
  rootPresentInFiniteCallerEnvironment : Bool
  nominalRootTypeResolved : Bool
  effectiveTypedSourceFieldResolved : Bool
  ordinarySourceAttributeResolutionProved : Bool

def callerRootFieldFrameRequestWellFormed
    (request : CallerRootFieldFrameRequest) : Bool :=
  !request.rootName.isEmpty &&
    !request.ownerClass.isEmpty &&
    !request.fieldName.isEmpty &&
    (inferSort request.rootValue == some .reference) &&
    isHeapFieldSort request.fieldSort &&
    callerRootFrameOriginIsVerifiedSource request.rootOrigin &&
    callerRootFrameOriginIsVerifiedSource request.fieldOrigin &&
    request.rootPresentInFiniteCallerEnvironment &&
    request.nominalRootTypeResolved &&
    request.effectiveTypedSourceFieldResolved &&
    request.ordinarySourceAttributeResolutionProved

def callerRootFieldFrameFact (request : CallerRootFieldFrameRequest) : Term :=
  .equal
    (.fieldRead request.postHeap request.rootValue request.fieldName request.fieldSort)
    (.fieldRead request.preHeap request.rootValue request.fieldName request.fieldSort)

def instantiateCallerRootFieldFrame
    (summary : CallerRootFrameSummary)
    (request : CallerRootFieldFrameRequest) : Option Term :=
  if callerRootFrameSummaryWellFormed summary &&
      callerRootFieldFrameRequestWellFormed request &&
      !summary.completeTransitiveModifiedFields.contains request.fieldName then
    some (callerRootFieldFrameFact request)
  else
    none

structure CallerRootFrameTrace where
  facts : List Term

inductive CallerRootFrameProgress where
  | running (trace : CallerRootFrameTrace)
  | refused (trace : CallerRootFrameTrace)

def advanceCallerRootFrameProgress
    (summary : CallerRootFrameSummary)
    (progress : CallerRootFrameProgress)
    (request : CallerRootFieldFrameRequest) : CallerRootFrameProgress :=
  match progress with
  | .refused trace => .refused trace
  | .running trace =>
      match instantiateCallerRootFieldFrame summary request with
      | none => .refused trace
      | some fact => .running { facts := trace.facts ++ [fact] }

def instantiateFiniteCallerRootFrames
    (summary : CallerRootFrameSummary) :
    CallerRootFrameProgress → List CallerRootFieldFrameRequest → CallerRootFrameProgress
  | progress, [] => progress
  | progress, request :: rest =>
      instantiateFiniteCallerRootFrames summary
        (advanceCallerRootFrameProgress summary progress request) rest

theorem caller_root_frame_fact_has_bool_sort
    (request : CallerRootFieldFrameRequest)
    (rootTyped : inferSort request.rootValue = some .reference)
    (fieldTyped : isHeapFieldSort request.fieldSort = true)
    (sortReflexive : valueSortBeq request.fieldSort request.fieldSort = true) :
    inferSort (callerRootFieldFrameFact request) = some .bool := by
  simp [callerRootFieldFrameFact, inferSort, rootTyped, fieldTyped,
    sortReflexive, instBEqValueSort, valueSortBeq]

theorem modified_caller_root_field_has_no_frame
    (summary : CallerRootFrameSummary)
    (request : CallerRootFieldFrameRequest)
    (modified : request.fieldName ∈ summary.completeTransitiveModifiedFields) :
    instantiateCallerRootFieldFrame summary request = none := by
  simp [instantiateCallerRootFieldFrame, modified]

theorem checked_external_caller_root_has_no_source_frame
    (summary : CallerRootFrameSummary)
    (request : CallerRootFieldFrameRequest)
    (provider contractHash : String)
    (externalRoot : request.rootOrigin = .checkedExternal provider contractHash) :
    instantiateCallerRootFieldFrame summary request = none := by
  simp [instantiateCallerRootFieldFrame, callerRootFieldFrameRequestWellFormed,
    externalRoot, callerRootFrameOriginIsVerifiedSource]

theorem incomplete_or_exceptional_summary_has_no_caller_root_frame
    (summary : CallerRootFrameSummary)
    (request : CallerRootFieldFrameRequest)
    (invalid : summary.completeNormalOutcome = false ∨
      summary.noExceptionalOutcome = false ∨
      summary.completeTransitiveModificationSetProved = false) :
    instantiateCallerRootFieldFrame summary request = none := by
  rcases invalid with incomplete | exceptional | incompleteModifies
  · simp [instantiateCallerRootFieldFrame, callerRootFrameSummaryWellFormed, incomplete]
  · simp [instantiateCallerRootFieldFrame, callerRootFrameSummaryWellFormed, exceptional]
  · simp [instantiateCallerRootFieldFrame, callerRootFrameSummaryWellFormed,
      incompleteModifies]

theorem refused_caller_root_frame_does_not_extend_trace
    (summary : CallerRootFrameSummary)
    (trace : CallerRootFrameTrace)
    (request : CallerRootFieldFrameRequest)
    (refused : instantiateCallerRootFieldFrame summary request = none) :
    advanceCallerRootFrameProgress summary (.running trace) request = .refused trace := by
  simp [advanceCallerRootFrameProgress, refused]

theorem refused_caller_root_frame_progress_is_absorbing
    (summary : CallerRootFrameSummary)
    (trace : CallerRootFrameTrace)
    (requests : List CallerRootFieldFrameRequest) :
    instantiateFiniteCallerRootFrames summary (.refused trace) requests = .refused trace := by
  induction requests with
  | nil => rfl
  | cons request rest inductionHypothesis =>
      simp [instantiateFiniteCallerRootFrames, advanceCallerRootFrameProgress,
        inductionHypothesis]

/-!
## Raw-field-left / exact-name-right identity-sufficient equality

This is the second v38 rule and intentionally has only one orientation.  The left operand is a
nonempty raw source-field chain read in the current heap/mask; every receiver hop has exact source
runtime-class, normal-allocation, permission, and complete hook-free MRO premises.  The right
operand is a named exact source construction with a complete source/object MRO containing neither
`__eq__` nor `__init_subclass__`.  The current assumptions must already prove that the two terms are
the same reference before the positive `Assert(left == right)` is emitted.  That identity also
recovers the left result's exact clean runtime class, so custom/reverse dispatch cannot intervene.

This rule is not symmetric syntax and provides no nonidentity/refutation rule.  Exact-name-left /
raw-field-right remains the separate v35 rule; arbitrary swapped expressions, calls, properties,
external/dynamic values, `!=`, negation, and contract clauses do not enter this definition.  The
model checks IR/premise algebra only, not Python equality or frontend correspondence.
-/

structure RawLeftExactRightReferenceEqualityRequest where
  context : NarrowReferenceEqualityContext
  operator : NarrowReferenceEqualityOperator
  left : CurrentReferenceFieldChainRead
  right : ExactSourceConstructedReferenceLocal
  completeRightMro : List ReferenceEqualityMroEntry
  currentHeapVersion : Nat
  currentMaskVersion : Nat
  allPriorObligationsProved : Bool
  identityAlreadyProvedFromCurrentAssumptions : Bool

def rawLeftExactRightReferenceEqualityStructurallySupported
    (request : RawLeftExactRightReferenceEqualityRequest) : Bool :=
  (match request.context with | .positiveAssert => true | _ => false) &&
    (match request.operator with | .equal => true | .notEqual => false) &&
    request.allPriorObligationsProved &&
    narrowReferenceEqualityRightOriginAccepted (.currentSourceFieldChain request.left)
      request.currentHeapVersion request.currentMaskVersion &&
    narrowReferenceEqualityLeftOriginAccepted (.exactSourceConstruction request.right)
      request.completeRightMro

def rawLeftExactRightReferenceEqualityWellFormed
    (request : RawLeftExactRightReferenceEqualityRequest) : Bool :=
  rawLeftExactRightReferenceEqualityStructurallySupported request &&
    request.identityAlreadyProvedFromCurrentAssumptions

def lowerRawLeftExactRightReferenceEquality
    (request : RawLeftExactRightReferenceEqualityRequest) : Option Term :=
  if rawLeftExactRightReferenceEqualityWellFormed request then
    some (.equal request.left.value request.right.value)
  else
    none

def classifyRawLeftExactRightReferenceEquality
    (request : RawLeftExactRightReferenceEqualityRequest) :
    NarrowReferenceEqualityDisposition :=
  if !rawLeftExactRightReferenceEqualityStructurallySupported request then .refused
  else if request.identityAlreadyProvedFromCurrentAssumptions then .proved
  else .unresolved

theorem accepted_raw_left_exact_right_equality_lowers_identity_only
    (request : RawLeftExactRightReferenceEqualityRequest)
    (accepted : rawLeftExactRightReferenceEqualityWellFormed request = true) :
    lowerRawLeftExactRightReferenceEquality request =
      some (.equal request.left.value request.right.value) := by
  simp [lowerRawLeftExactRightReferenceEquality, accepted]

theorem raw_left_exact_right_without_identity_proof_is_unresolved
    (request : RawLeftExactRightReferenceEqualityRequest)
    (structural : rawLeftExactRightReferenceEqualityStructurallySupported request = true)
    (unknown : request.identityAlreadyProvedFromCurrentAssumptions = false) :
    classifyRawLeftExactRightReferenceEquality request = .unresolved := by
  simp [classifyRawLeftExactRightReferenceEquality, structural, unknown]

theorem stale_or_unpermitted_raw_left_chain_refuses
    (request : RawLeftExactRightReferenceEqualityRequest)
    (invalid : request.left.readPermissionProved = false ∨
      request.left.heapVersion ≠ request.currentHeapVersion ∨
      request.left.maskVersion ≠ request.currentMaskVersion) :
    lowerRawLeftExactRightReferenceEquality request = none := by
  rcases invalid with noPermission | staleHeap | staleMask
  · simp [lowerRawLeftExactRightReferenceEquality,
      rawLeftExactRightReferenceEqualityWellFormed,
      rawLeftExactRightReferenceEqualityStructurallySupported,
      narrowReferenceEqualityRightOriginAccepted, noPermission]
  · simp [lowerRawLeftExactRightReferenceEquality,
      rawLeftExactRightReferenceEqualityWellFormed,
      rawLeftExactRightReferenceEqualityStructurallySupported,
      narrowReferenceEqualityRightOriginAccepted, staleHeap]
  · simp [lowerRawLeftExactRightReferenceEquality,
      rawLeftExactRightReferenceEqualityWellFormed,
      rawLeftExactRightReferenceEqualityStructurallySupported,
      narrowReferenceEqualityRightOriginAccepted, staleMask]

theorem custom_eq_on_exact_right_refuses_raw_left_equality
    (request : RawLeftExactRightReferenceEqualityRequest)
    (className : String)
    (mro : request.completeRightMro =
      [.sourceWithEqOverride className, .objectDefault]) :
    lowerRawLeftExactRightReferenceEquality request = none := by
  simp [lowerRawLeftExactRightReferenceEquality,
    rawLeftExactRightReferenceEqualityWellFormed,
    rawLeftExactRightReferenceEqualityStructurallySupported,
    narrowReferenceEqualityLeftOriginAccepted, completeSourceMroForExactClass, mro]

theorem nonexact_or_external_raw_left_receiver_refuses
    (request : RawLeftExactRightReferenceEqualityRequest)
    (receiver : ExactRawFieldReceiverResolution)
    (onlyReceiver : request.left.receivers = [receiver])
    (invalid : receiver.runtimeClassExactProved = false ∨
      receiver.sourceAllocatorVerified = false) :
    lowerRawLeftExactRightReferenceEquality request = none := by
  rcases invalid with nonexact | external
  · simp [lowerRawLeftExactRightReferenceEquality,
      rawLeftExactRightReferenceEqualityWellFormed,
      rawLeftExactRightReferenceEqualityStructurallySupported,
      narrowReferenceEqualityRightOriginAccepted, onlyReceiver,
      exactRawFieldReceiverResolutionAccepted, nonexact]
  · simp [lowerRawLeftExactRightReferenceEquality,
      rawLeftExactRightReferenceEqualityWellFormed,
      rawLeftExactRightReferenceEqualityStructurallySupported,
      narrowReferenceEqualityRightOriginAccepted, onlyReceiver,
      exactRawFieldReceiverResolutionAccepted, external]

/-!
## Source reference-identity summaries

This is the narrow v39 model for a source function such as
`@Pure def identity(value : T) -> T: return value` when its call occurs directly around the one
reference argument of the v37 terminal nested-call rule.  The frontend supplies a sealed summary
only after proving the exact decorator, signature, canonical nominal identity, body, totality, and
source binding.  A local summary must be present in the exact callable prefix at the call; an
imported source summary requires its provider to have completed initialization.  Its canonical
nominal dependency uses the v33 call-time class-availability rule.

Application begins only after the wrapped source reference chain has been evaluated.  It returns
that exact trace, including the actual nominal provenance, heap, mask, assumptions, and obligations.
No fresh result term or annotation-only provenance is manufactured.  Bad summaries, bindings,
providers, argument proofs, and nested/ghost uses refuse with the post-argument trace unchanged and
therefore cannot reach the outer call.

This is finite IR/premise algebra.  It does not prove Python/frontend correspondence, decorator or
lexical resolution, source totality, provider initialization, canonicalization, argument-chain
correctness, or summary truth.  It is not a rule for arbitrary pure/reference-returning functions,
external contracts, defaults, optional values, keywords, or nested identity calls.
-/

inductive ReferenceIdentitySummaryOrigin where
  | localVerifiedSource
  | completedImportedSource (provider : String)
  | checkedExternal (provider contractHash : String)
  | dynamicUnknown
  deriving DecidableEq

def referenceIdentitySummaryOriginIsSource : ReferenceIdentitySummaryOrigin → Bool
  | .localVerifiedSource => true
  | .completedImportedSource provider => !provider.isEmpty
  | .checkedExternal _ _ | .dynamicUnknown => false

structure SourceReferenceIdentitySummary where
  sourceName : String
  canonicalName : String
  parameterName : String
  canonicalParameterClass : String
  canonicalReturnClass : String
  nominalDependency : LateBoundClassDependency
  origin : ReferenceIdentitySummaryOrigin
  sourceOwnedVerified : Bool
  pureDecoratorExactlyResolved : Bool
  exactlyOnePositionalParameter : Bool
  parameterHasNoDefault : Bool
  parameterNonOptional : Bool
  returnNonOptional : Bool
  bodyIsExactReturnParameter : Bool
  totalNormalOutcomeProved : Bool
  heapAndMaskNeutralProved : Bool
  lexicalBindingUnique : Bool
  canonicalResolutionStable : Bool
  nominalDependencyResolvedInSealedCatalog : Bool

def sourceReferenceIdentitySummaryWellFormed
    (summary : SourceReferenceIdentitySummary) : Bool :=
  !summary.sourceName.isEmpty &&
    !summary.canonicalName.isEmpty &&
    !summary.parameterName.isEmpty &&
    !summary.canonicalParameterClass.isEmpty &&
    (summary.canonicalParameterClass == summary.canonicalReturnClass) &&
    (summary.canonicalParameterClass == summary.nominalDependency.canonicalName) &&
    referenceIdentitySummaryOriginIsSource summary.origin &&
    summary.sourceOwnedVerified &&
    summary.pureDecoratorExactlyResolved &&
    summary.exactlyOnePositionalParameter &&
    summary.parameterHasNoDefault &&
    summary.parameterNonOptional &&
    summary.returnNonOptional &&
    summary.bodyIsExactReturnParameter &&
    summary.totalNormalOutcomeProved &&
    summary.heapAndMaskNeutralProved &&
    summary.lexicalBindingUnique &&
    summary.canonicalResolutionStable &&
    summary.nominalDependencyResolvedInSealedCatalog

structure ReferenceIdentityCallAvailability where
  classes : CallTimeClassAvailability
  localCanonicalCallablePrefix : List String
  completedImportedProviders : List String

def sourceReferenceIdentityBindingAvailable
    (availability : ReferenceIdentityCallAvailability)
    (summary : SourceReferenceIdentitySummary) : Bool :=
  lateBoundClassDependencyAvailable availability.classes summary.nominalDependency &&
    match summary.origin with
    | .localVerifiedSource =>
        decide (summary.canonicalName ∈ availability.localCanonicalCallablePrefix)
    | .completedImportedSource provider =>
        (!provider.isEmpty) && decide (provider ∈ availability.completedImportedProviders)
    | .checkedExternal _ _ | .dynamicUnknown => false

structure ReferenceIdentityArgumentSyntax where
  directNameCall : Bool
  exactlyOnePositionalArgument : Bool
  noKeywords : Bool
  directTerminalOuterCallArgument : Bool
  moduleHeapFunctionRuntimeContext : Bool
  notNestedInAnotherReferenceExpression : Bool

def referenceIdentityArgumentSyntaxAccepted
    (callSyntax : ReferenceIdentityArgumentSyntax) : Bool :=
  callSyntax.directNameCall &&
    callSyntax.exactlyOnePositionalArgument &&
    callSyntax.noKeywords &&
    callSyntax.directTerminalOuterCallArgument &&
    callSyntax.moduleHeapFunctionRuntimeContext &&
    callSyntax.notNestedInAnotherReferenceExpression

structure SourceReferenceIdentityApplication where
  summary : SourceReferenceIdentitySummary
  availability : ReferenceIdentityCallAvailability
  callSyntax : ReferenceIdentityArgumentSyntax
  argumentAfterEvaluation : ReferenceChainTrace
  bindingResolvesToThisSummary : Bool
  argumentSourceReferenceChainAccepted : Bool
  argumentNonOptional : Bool
  argumentNominalCompatibilityProved : Bool
  allArgumentObligationsProved : Bool

def sourceReferenceIdentityApplicationWellFormed
    (application : SourceReferenceIdentityApplication) : Bool :=
  sourceReferenceIdentitySummaryWellFormed application.summary &&
    sourceReferenceIdentityBindingAvailable application.availability application.summary &&
    referenceIdentityArgumentSyntaxAccepted application.callSyntax &&
    application.bindingResolvesToThisSummary &&
    application.argumentSourceReferenceChainAccepted &&
    application.argumentNonOptional &&
    application.argumentNominalCompatibilityProved &&
    application.allArgumentObligationsProved &&
    (inferSort application.argumentAfterEvaluation.state.value == some .reference) &&
    !application.argumentAfterEvaluation.state.nominalClass.isEmpty

inductive SourceReferenceIdentityApplicationResult where
  | returned (trace : ReferenceChainTrace)
  | refused (trace : ReferenceChainTrace)

def applySourceReferenceIdentity
    (application : SourceReferenceIdentityApplication) :
    SourceReferenceIdentityApplicationResult :=
  if sourceReferenceIdentityApplicationWellFormed application then
    .returned application.argumentAfterEvaluation
  else
    .refused application.argumentAfterEvaluation

def applySourceReferenceIdentityThenOuter
    (receiver : ReferenceChainTrace)
    (identity : SourceReferenceIdentityApplication)
    (outer : StandaloneUnitReferenceMethodApplication) :
    Option StandaloneStatementTrace :=
  match applySourceReferenceIdentity identity with
  | .refused _ => none
  | .returned argument => applyStandaloneUnitReferenceMethod receiver argument outer

theorem accepted_source_reference_identity_returns_exact_argument_trace
    (application : SourceReferenceIdentityApplication)
    (accepted : sourceReferenceIdentityApplicationWellFormed application = true) :
    applySourceReferenceIdentity application =
      .returned application.argumentAfterEvaluation := by
  simp [applySourceReferenceIdentity, accepted]

theorem source_reference_identity_preserves_actual_nominal_and_versions
    (application : SourceReferenceIdentityApplication)
    (accepted : sourceReferenceIdentityApplicationWellFormed application = true) :
    match applySourceReferenceIdentity application with
    | .returned trace =>
        trace.state.value = application.argumentAfterEvaluation.state.value ∧
          trace.state.nominalClass = application.argumentAfterEvaluation.state.nominalClass ∧
          trace.state.heap = application.argumentAfterEvaluation.state.heap ∧
          trace.state.mask = application.argumentAfterEvaluation.state.mask
    | .refused _ => False := by
  simp [applySourceReferenceIdentity, accepted]

theorem source_reference_identity_preserves_argument_evidence
    (application : SourceReferenceIdentityApplication)
    (accepted : sourceReferenceIdentityApplicationWellFormed application = true) :
    match applySourceReferenceIdentity application with
    | .returned trace =>
        trace.assumptions = application.argumentAfterEvaluation.assumptions ∧
          trace.obligations = application.argumentAfterEvaluation.obligations
    | .refused _ => False := by
  simp [applySourceReferenceIdentity, accepted]

theorem canonical_parameter_return_mismatch_refuses_identity_summary
    (application : SourceReferenceIdentityApplication)
    (mismatch : application.summary.canonicalParameterClass ≠
      application.summary.canonicalReturnClass) :
    applySourceReferenceIdentity application =
      .refused application.argumentAfterEvaluation := by
  simp [applySourceReferenceIdentity, sourceReferenceIdentityApplicationWellFormed,
    sourceReferenceIdentitySummaryWellFormed, mismatch]

theorem noncanonical_pure_decorator_binding_refuses_identity_summary
    (application : SourceReferenceIdentityApplication)
    (shadowed : application.summary.pureDecoratorExactlyResolved = false) :
    applySourceReferenceIdentity application =
      .refused application.argumentAfterEvaluation := by
  simp [applySourceReferenceIdentity, sourceReferenceIdentityApplicationWellFormed,
    sourceReferenceIdentitySummaryWellFormed, shadowed]

theorem nonidentity_body_or_exceptional_summary_refuses
    (application : SourceReferenceIdentityApplication)
    (invalid : application.summary.bodyIsExactReturnParameter = false ∨
      application.summary.totalNormalOutcomeProved = false) :
    applySourceReferenceIdentity application =
      .refused application.argumentAfterEvaluation := by
  rcases invalid with wrongBody | exceptional
  · simp [applySourceReferenceIdentity, sourceReferenceIdentityApplicationWellFormed,
      sourceReferenceIdentitySummaryWellFormed, wrongBody]
  · simp [applySourceReferenceIdentity, sourceReferenceIdentityApplicationWellFormed,
      sourceReferenceIdentitySummaryWellFormed, exceptional]

theorem unchecked_external_identity_summary_refuses
    (application : SourceReferenceIdentityApplication)
    (provider contractHash : String)
    (external : application.summary.origin = .checkedExternal provider contractHash) :
    applySourceReferenceIdentity application =
      .refused application.argumentAfterEvaluation := by
  simp [applySourceReferenceIdentity, sourceReferenceIdentityApplicationWellFormed,
    sourceReferenceIdentitySummaryWellFormed, referenceIdentitySummaryOriginIsSource, external]

theorem incomplete_imported_provider_refuses_identity_application
    (application : SourceReferenceIdentityApplication)
    (provider : String)
    (imported : application.summary.origin = .completedImportedSource provider)
    (missing : provider ∉ application.availability.completedImportedProviders) :
    applySourceReferenceIdentity application =
      .refused application.argumentAfterEvaluation := by
  simp [applySourceReferenceIdentity, sourceReferenceIdentityApplicationWellFormed,
    sourceReferenceIdentityBindingAvailable, imported, missing]

theorem unresolved_or_shadowed_identity_binding_refuses
    (application : SourceReferenceIdentityApplication)
    (unresolved : application.bindingResolvesToThisSummary = false) :
    applySourceReferenceIdentity application =
      .refused application.argumentAfterEvaluation := by
  simp [applySourceReferenceIdentity, sourceReferenceIdentityApplicationWellFormed, unresolved]

theorem local_identity_absent_from_call_prefix_refuses
    (application : SourceReferenceIdentityApplication)
    (localOrigin : application.summary.origin = .localVerifiedSource)
    (missing : application.summary.canonicalName ∉
      application.availability.localCanonicalCallablePrefix) :
    applySourceReferenceIdentity application =
      .refused application.argumentAfterEvaluation := by
  simp [applySourceReferenceIdentity, sourceReferenceIdentityApplicationWellFormed,
    sourceReferenceIdentityBindingAvailable, localOrigin, missing]

theorem nested_identity_use_refuses_without_extending_argument_trace
    (application : SourceReferenceIdentityApplication)
    (nested : application.callSyntax.notNestedInAnotherReferenceExpression = false) :
    applySourceReferenceIdentity application =
      .refused application.argumentAfterEvaluation := by
  simp [applySourceReferenceIdentity, sourceReferenceIdentityApplicationWellFormed,
    referenceIdentityArgumentSyntaxAccepted, nested]

theorem refused_identity_application_prevents_outer_call
    (receiver : ReferenceChainTrace)
    (identity : SourceReferenceIdentityApplication)
    (outer : StandaloneUnitReferenceMethodApplication)
    (refused : applySourceReferenceIdentity identity =
      .refused identity.argumentAfterEvaluation) :
    applySourceReferenceIdentityThenOuter receiver identity outer = none := by
  unfold applySourceReferenceIdentityThenOuter
  rw [refused]

theorem accepted_identity_then_outer_uses_the_saved_argument_trace
    (receiver : ReferenceChainTrace)
    (identity : SourceReferenceIdentityApplication)
    (outer : StandaloneUnitReferenceMethodApplication)
    (identityAccepted : sourceReferenceIdentityApplicationWellFormed identity = true)
    (outerAccepted : standaloneUnitReferenceMethodApplicationWellFormed
      receiver identity.argumentAfterEvaluation outer = true) :
    applySourceReferenceIdentityThenOuter receiver identity outer = some {
      heap := outer.exitHeap
      mask := outer.exitMask
      obligations := identity.argumentAfterEvaluation.obligations ++
        outer.preconditionObligations receiver.state.value
          identity.argumentAfterEvaluation.state.value
      assumptions := identity.argumentAfterEvaluation.assumptions ++
        outer.transitionAndPostconditionAssumptions receiver.state.value
          identity.argumentAfterEvaluation.state.value
          identity.argumentAfterEvaluation.state.heap
          identity.argumentAfterEvaluation.state.mask
    } := by
  unfold applySourceReferenceIdentityThenOuter
  rw [accepted_source_reference_identity_returns_exact_argument_trace identity identityAccepted]
  exact terminal_application_uses_post_argument_versions_and_saved_receiver
    receiver identity.argumentAfterEvaluation outer outerAccepted

/-!
## Exact non-alias caller-object frames

This is the object-sensitive frame extension used by v39 after a normal source instance method has
advanced the heap.  It is deliberately separate from v38's name-based caller-root frames.  The
frontend supplies a complete receiver-local effect premise: every executable write in the method
and its supported transitive direct-`self` calls is a direct field write on the same instantiated
receiver.  Therefore a source object proved distinct from that receiver is unchanged even when it
has a field whose name also occurs in the method's modification set.

The finite candidates are only one-hop reference fields of typed caller-local roots.  Both the
root and candidate have independently supplied exact runtime source-class facts and complete plain,
hook-free source MROs.  The one-hop edge must be a non-optional source field whose exact class comes
from a verified, normally completing source constructor.  A candidate field must itself be an
effective source-owned field.  Its frame relates reads through the saved pre-heap candidate term in
the pre- and post-heaps; it neither frames the root edge nor grants read permission.

`sameReceiver` and `unknown` alias dispositions add no fact.  Checked-external, dynamic, optional,
inexact, exceptional, or incomplete-effect candidates likewise add no fact.  This is finite IR
construction from frontend premises, not a proof of Python/frontend correspondence, source
freshness, exact-class inference, MRO completeness, alias analysis, transitive-effect closure, or
semantic framing.
-/

inductive ExactReceiverAliasDisposition where
  | provedDistinct
  | sameReceiver
  | unknown
  deriving DecidableEq

structure ExactNonAliasFrameSummary where
  methodName : String
  origin : CallerRootFrameOrigin
  completeReceiverModifiedFields : List String
  instanceMethod : Bool
  completeNormalOutcome : Bool
  noExceptionalOutcome : Bool
  heapAdvanced : Bool
  directSelfFieldWritesOnly : Bool
  supportedDirectSelfCallClosureComplete : Bool
  allExecutableWritesConfinedToReceiver : Bool

def exactNonAliasFrameSummaryWellFormed
    (summary : ExactNonAliasFrameSummary) : Bool :=
  !summary.methodName.isEmpty &&
    callerRootFrameOriginIsVerifiedSource summary.origin &&
    summary.instanceMethod &&
    summary.completeNormalOutcome &&
    summary.noExceptionalOutcome &&
    summary.heapAdvanced &&
    summary.directSelfFieldWritesOnly &&
    summary.supportedDirectSelfCallClosureComplete &&
    summary.allExecutableWritesConfinedToReceiver

structure ExactNonAliasCallerObjectFrameRequest where
  preHeap : Nat
  postHeap : Nat
  modifiedReceiver : Term
  localRootName : String
  localRootValue : Term
  localRootClass : String
  oneHopFieldName : String
  oneHopExactClass : String
  candidateValue : Term
  candidateFieldName : String
  candidateFieldSort : ValueSort
  rootOrigin : CallerRootFrameOrigin
  oneHopFieldOrigin : CallerRootFrameOrigin
  candidateOrigin : CallerRootFrameOrigin
  candidateFieldOrigin : CallerRootFrameOrigin
  rootPresentInFiniteCallerEnvironment : Bool
  rootRuntimeSourceClassExactProved : Bool
  rootCompletePlainHookFreeSourceMroProved : Bool
  oneHopFieldFromVerifiedNormalSourceConstructor : Bool
  oneHopFieldNonOptionalReference : Bool
  oneHopFieldSourceOwned : Bool
  candidateIsPreHeapOneHopFieldRead : Bool
  candidateRuntimeSourceClassExactProved : Bool
  candidateCompletePlainHookFreeSourceMroProved : Bool
  candidateFieldEffectiveAndSourceOwned : Bool
  aliasDisposition : ExactReceiverAliasDisposition

def exactNonAliasCallerObjectFrameRequestWellFormed
    (request : ExactNonAliasCallerObjectFrameRequest) : Bool :=
  !request.localRootName.isEmpty &&
    !request.localRootClass.isEmpty &&
    !request.oneHopFieldName.isEmpty &&
    !request.oneHopExactClass.isEmpty &&
    !request.candidateFieldName.isEmpty &&
    (inferSort request.modifiedReceiver == some .reference) &&
    (inferSort request.localRootValue == some .reference) &&
    (inferSort request.candidateValue == some .reference) &&
    isHeapFieldSort request.candidateFieldSort &&
    callerRootFrameOriginIsVerifiedSource request.rootOrigin &&
    callerRootFrameOriginIsVerifiedSource request.oneHopFieldOrigin &&
    callerRootFrameOriginIsVerifiedSource request.candidateOrigin &&
    callerRootFrameOriginIsVerifiedSource request.candidateFieldOrigin &&
    request.rootPresentInFiniteCallerEnvironment &&
    request.rootRuntimeSourceClassExactProved &&
    request.rootCompletePlainHookFreeSourceMroProved &&
    request.oneHopFieldFromVerifiedNormalSourceConstructor &&
    request.oneHopFieldNonOptionalReference &&
    request.oneHopFieldSourceOwned &&
    request.candidateIsPreHeapOneHopFieldRead &&
    request.candidateRuntimeSourceClassExactProved &&
    request.candidateCompletePlainHookFreeSourceMroProved &&
    request.candidateFieldEffectiveAndSourceOwned &&
    request.aliasDisposition == .provedDistinct

def exactNonAliasCallerObjectFrameFact
    (request : ExactNonAliasCallerObjectFrameRequest) : Term :=
  .equal
    (.fieldRead request.postHeap request.candidateValue request.candidateFieldName
      request.candidateFieldSort)
    (.fieldRead request.preHeap request.candidateValue request.candidateFieldName
      request.candidateFieldSort)

def instantiateExactNonAliasCallerObjectFrame
    (summary : ExactNonAliasFrameSummary)
    (request : ExactNonAliasCallerObjectFrameRequest) : Option Term :=
  if exactNonAliasFrameSummaryWellFormed summary &&
      exactNonAliasCallerObjectFrameRequestWellFormed request then
    some (exactNonAliasCallerObjectFrameFact request)
  else
    none

theorem accepted_exact_non_alias_frame_uses_saved_candidate_and_both_heaps
    (summary : ExactNonAliasFrameSummary)
    (request : ExactNonAliasCallerObjectFrameRequest)
    (accepted : exactNonAliasFrameSummaryWellFormed summary = true)
    (candidateAccepted : exactNonAliasCallerObjectFrameRequestWellFormed request = true) :
    instantiateExactNonAliasCallerObjectFrame summary request =
      some (.equal
        (.fieldRead request.postHeap request.candidateValue request.candidateFieldName
          request.candidateFieldSort)
        (.fieldRead request.preHeap request.candidateValue request.candidateFieldName
          request.candidateFieldSort)) := by
  simp [instantiateExactNonAliasCallerObjectFrame, exactNonAliasCallerObjectFrameFact,
    accepted, candidateAccepted]

theorem exact_non_alias_frame_does_not_exclude_modified_field_names
    (summary : ExactNonAliasFrameSummary)
    (request : ExactNonAliasCallerObjectFrameRequest)
    (accepted : exactNonAliasFrameSummaryWellFormed summary = true)
    (candidateAccepted : exactNonAliasCallerObjectFrameRequestWellFormed request = true)
    (_sameName : request.candidateFieldName ∈ summary.completeReceiverModifiedFields) :
    instantiateExactNonAliasCallerObjectFrame summary request =
      some (exactNonAliasCallerObjectFrameFact request) := by
  simp [instantiateExactNonAliasCallerObjectFrame, accepted, candidateAccepted]

theorem same_receiver_adds_no_exact_non_alias_frame
    (summary : ExactNonAliasFrameSummary)
    (request : ExactNonAliasCallerObjectFrameRequest)
    (aliases : request.aliasDisposition = .sameReceiver) :
    instantiateExactNonAliasCallerObjectFrame summary request = none := by
  simp [instantiateExactNonAliasCallerObjectFrame,
    exactNonAliasCallerObjectFrameRequestWellFormed, aliases]

theorem unknown_alias_adds_no_exact_non_alias_frame
    (summary : ExactNonAliasFrameSummary)
    (request : ExactNonAliasCallerObjectFrameRequest)
    (unknown : request.aliasDisposition = .unknown) :
    instantiateExactNonAliasCallerObjectFrame summary request = none := by
  simp [instantiateExactNonAliasCallerObjectFrame,
    exactNonAliasCallerObjectFrameRequestWellFormed, unknown]

theorem external_or_inexact_candidate_adds_no_exact_non_alias_frame
    (summary : ExactNonAliasFrameSummary)
    (request : ExactNonAliasCallerObjectFrameRequest)
    (unsupported : request.oneHopFieldSourceOwned = false ∨
      request.candidateRuntimeSourceClassExactProved = false ∨
      request.candidateFieldEffectiveAndSourceOwned = false) :
    instantiateExactNonAliasCallerObjectFrame summary request = none := by
  rcases unsupported with externalEdge | inexactCandidate | externalField
  · simp [instantiateExactNonAliasCallerObjectFrame,
      exactNonAliasCallerObjectFrameRequestWellFormed, externalEdge]
  · simp [instantiateExactNonAliasCallerObjectFrame,
      exactNonAliasCallerObjectFrameRequestWellFormed, inexactCandidate]
  · simp [instantiateExactNonAliasCallerObjectFrame,
      exactNonAliasCallerObjectFrameRequestWellFormed, externalField]

theorem checked_external_origin_adds_no_exact_non_alias_frame
    (summary : ExactNonAliasFrameSummary)
    (request : ExactNonAliasCallerObjectFrameRequest)
    (provider contractHash : String)
    (external : request.candidateOrigin = .checkedExternal provider contractHash) :
    instantiateExactNonAliasCallerObjectFrame summary request = none := by
  simp [instantiateExactNonAliasCallerObjectFrame,
    exactNonAliasCallerObjectFrameRequestWellFormed,
    callerRootFrameOriginIsVerifiedSource, external]

theorem incomplete_receiver_local_effect_summary_adds_no_exact_non_alias_frame
    (summary : ExactNonAliasFrameSummary)
    (request : ExactNonAliasCallerObjectFrameRequest)
    (incomplete : summary.supportedDirectSelfCallClosureComplete = false ∨
      summary.allExecutableWritesConfinedToReceiver = false ∨
      summary.noExceptionalOutcome = false) :
    instantiateExactNonAliasCallerObjectFrame summary request = none := by
  rcases incomplete with incompleteClosure | unconfined | exceptional
  · simp [instantiateExactNonAliasCallerObjectFrame,
      exactNonAliasFrameSummaryWellFormed, incompleteClosure]
  · simp [instantiateExactNonAliasCallerObjectFrame,
      exactNonAliasFrameSummaryWellFormed, unconfined]
  · simp [instantiateExactNonAliasCallerObjectFrame,
      exactNonAliasFrameSummaryWellFormed, exceptional]

/-!
## Exact raw-left / constructed-name-right equality

This is v40's narrow reverse-orientation companion to the v36 bilateral rule.  The Python syntax
remains exactly a positive `Assert(rawSourceFieldChain == exactConstructedName)`.  The left chain
keeps its current heap/mask, positive read-permission, exact receiver, normal allocator, and plain
hook-free source-MRO premises.  In addition, its *final value* independently needs an exact runtime
source class, a verified source allocator, a normal-only constructor, and a complete source MRO
ending at `object` without `__eq__` or `__init_subclass__`.  A nominal field annotation is not that
evidence.  The right name is the existing exact, normally completed source construction with the
same clean-MRO gate.

Under those bilateral premises both Python equality dispatch attempts use `object.__eq__`; equality
therefore reduces to reference identity.  Solver-proved identity proves the assertion, proved
nonidentity refutes it, and unknown identity remains unresolved.  The lowering retains source
operand orientation and does not manufacture distinctness.  If final-left exactness is unavailable,
this branch refuses; the older v38 identity-sufficient branch remains a separate fallback because
proved identity to the exact clean right object recovers its runtime class.

This is IR/premise algebra only.  It does not prove Python/frontend correspondence, permission or
exact-class facts, allocator/constructor truth, MRO extraction, solver evidence, or the target
program's heap equations.  Properties, calls, optional/scalar values, external/dynamic classes,
custom equality, other operators/contexts, and general operand symmetry remain outside the rule.
-/

structure RawLeftExactRightBilateralEqualityRequest where
  context : NarrowReferenceEqualityContext
  operator : NarrowReferenceEqualityOperator
  left : ExactSourceReferenceFieldChain
  leftResultSourceAllocatorVerified : Bool
  leftResultNormalOnlyConstructorProved : Bool
  right : ExactConstructedLeftReferenceName
  rightSourceAllocatorVerified : Bool
  rightNormalOnlyConstructorProved : Bool
  currentHeapVersion : Nat
  currentMaskVersion : Nat
  allPriorObligationsProved : Bool

def rawLeftExactRightBilateralEqualityRequestWellFormed
    (request : RawLeftExactRightBilateralEqualityRequest) : Bool :=
  (match request.context with | .positiveAssert => true | _ => false) &&
    (match request.operator with | .equal => true | .notEqual => false) &&
    request.allPriorObligationsProved &&
    request.leftResultSourceAllocatorVerified &&
    request.leftResultNormalOnlyConstructorProved &&
    request.rightSourceAllocatorVerified &&
    request.rightNormalOnlyConstructorProved &&
    exactSourceReferenceFieldChainAccepted request.left
      request.currentHeapVersion request.currentMaskVersion &&
    exactConstructedLeftReferenceNameAccepted request.right

def lowerRawLeftExactRightBilateralEquality
    (request : RawLeftExactRightBilateralEqualityRequest) : Option Term :=
  if rawLeftExactRightBilateralEqualityRequestWellFormed request then
    some (.equal request.left.read.value request.right.value)
  else
    none

def classifyRawLeftExactRightBilateralEquality
    (request : RawLeftExactRightBilateralEqualityRequest)
    (identity : BilateralIdentityEvidence) : ExactBilateralReferenceEqualityDisposition :=
  match lowerRawLeftExactRightBilateralEquality request with
  | none => .refused
  | some _ => match identity with
    | .provedSame => .proved
    | .provedDistinct => .refuted
    | .unknown => .unresolved

theorem accepted_raw_left_exact_right_bilateral_lowers_in_source_orientation
    (request : RawLeftExactRightBilateralEqualityRequest)
    (accepted : rawLeftExactRightBilateralEqualityRequestWellFormed request = true) :
    lowerRawLeftExactRightBilateralEquality request =
      some (.equal request.left.read.value request.right.value) := by
  simp [lowerRawLeftExactRightBilateralEquality, accepted]

theorem exact_raw_left_same_identity_proves
    (request : RawLeftExactRightBilateralEqualityRequest)
    (accepted : rawLeftExactRightBilateralEqualityRequestWellFormed request = true) :
    classifyRawLeftExactRightBilateralEquality request .provedSame = .proved := by
  simp [classifyRawLeftExactRightBilateralEquality,
    accepted_raw_left_exact_right_bilateral_lowers_in_source_orientation request accepted]

theorem exact_raw_left_distinct_identity_refutes
    (request : RawLeftExactRightBilateralEqualityRequest)
    (accepted : rawLeftExactRightBilateralEqualityRequestWellFormed request = true) :
    classifyRawLeftExactRightBilateralEquality request .provedDistinct = .refuted := by
  simp [classifyRawLeftExactRightBilateralEquality,
    accepted_raw_left_exact_right_bilateral_lowers_in_source_orientation request accepted]

theorem exact_raw_left_unknown_identity_is_unresolved
    (request : RawLeftExactRightBilateralEqualityRequest)
    (accepted : rawLeftExactRightBilateralEqualityRequestWellFormed request = true) :
    classifyRawLeftExactRightBilateralEquality request .unknown = .unresolved := by
  simp [classifyRawLeftExactRightBilateralEquality,
    accepted_raw_left_exact_right_bilateral_lowers_in_source_orientation request accepted]

theorem upstream_final_expected_false_uses_refuted_identity
    (request : RawLeftExactRightBilateralEqualityRequest)
    (accepted : rawLeftExactRightBilateralEqualityRequestWellFormed request = true)
    (identity : BilateralIdentityEvidence)
    (setterAndFreshnessFactsProveDistinct : identity = .provedDistinct) :
    classifyRawLeftExactRightBilateralEquality request identity = .refuted := by
  subst identity
  exact exact_raw_left_distinct_identity_refutes request accepted

theorem nonexact_final_left_result_refuses_bilateral_branch
    (request : RawLeftExactRightBilateralEqualityRequest)
    (nonexact : request.left.runtimeResultClassExactSourceProved = false) :
    lowerRawLeftExactRightBilateralEquality request = none := by
  simp [lowerRawLeftExactRightBilateralEquality,
    rawLeftExactRightBilateralEqualityRequestWellFormed,
    exactSourceReferenceFieldChainAccepted, nonexact]

theorem unverified_or_exceptional_final_left_allocator_refuses_bilateral_branch
    (request : RawLeftExactRightBilateralEqualityRequest)
    (invalid : request.leftResultSourceAllocatorVerified = false ∨
      request.leftResultNormalOnlyConstructorProved = false) :
    lowerRawLeftExactRightBilateralEquality request = none := by
  rcases invalid with unverified | exceptional
  · simp [lowerRawLeftExactRightBilateralEquality,
      rawLeftExactRightBilateralEqualityRequestWellFormed, unverified]
  · simp [lowerRawLeftExactRightBilateralEquality,
      rawLeftExactRightBilateralEqualityRequestWellFormed, exceptional]

theorem unverified_or_exceptional_exact_right_allocator_refuses_bilateral_branch
    (request : RawLeftExactRightBilateralEqualityRequest)
    (invalid : request.rightSourceAllocatorVerified = false ∨
      request.rightNormalOnlyConstructorProved = false) :
    lowerRawLeftExactRightBilateralEquality request = none := by
  rcases invalid with unverified | exceptional
  · simp [lowerRawLeftExactRightBilateralEquality,
      rawLeftExactRightBilateralEqualityRequestWellFormed, unverified]
  · simp [lowerRawLeftExactRightBilateralEquality,
      rawLeftExactRightBilateralEqualityRequestWellFormed, exceptional]

theorem stale_or_unpermitted_raw_left_refuses_bilateral_branch
    (request : RawLeftExactRightBilateralEqualityRequest)
    (invalid : request.left.read.readPermissionProved = false ∨
      request.left.read.heapVersion ≠ request.currentHeapVersion ∨
      request.left.read.maskVersion ≠ request.currentMaskVersion) :
    lowerRawLeftExactRightBilateralEquality request = none := by
  rcases invalid with unpermitted | staleHeap | staleMask
  · simp [lowerRawLeftExactRightBilateralEquality,
      rawLeftExactRightBilateralEqualityRequestWellFormed,
      exactSourceReferenceFieldChainAccepted,
      narrowReferenceEqualityRightOriginAccepted, unpermitted]
  · simp [lowerRawLeftExactRightBilateralEquality,
      rawLeftExactRightBilateralEqualityRequestWellFormed,
      exactSourceReferenceFieldChainAccepted,
      narrowReferenceEqualityRightOriginAccepted, staleHeap]
  · simp [lowerRawLeftExactRightBilateralEquality,
      rawLeftExactRightBilateralEqualityRequestWellFormed,
      exactSourceReferenceFieldChainAccepted,
      narrowReferenceEqualityRightOriginAccepted, staleMask]

theorem custom_eq_on_final_left_refuses_bilateral_branch
    (request : RawLeftExactRightBilateralEqualityRequest)
    (className : String)
    (mro : request.left.completeResultMro =
      [.sourceClassWithEqBinding className, .objectDefault]) :
    lowerRawLeftExactRightBilateralEquality request = none := by
  simp [lowerRawLeftExactRightBilateralEquality,
    rawLeftExactRightBilateralEqualityRequestWellFormed,
    exactSourceReferenceFieldChainAccepted,
    completeSourceEqualityMroForExactClass, mro]

theorem custom_eq_on_exact_right_refuses_bilateral_branch
    (request : RawLeftExactRightBilateralEqualityRequest)
    (className : String)
    (mro : request.right.completeMro =
      [.sourceClassWithEqBinding className, .objectDefault]) :
    lowerRawLeftExactRightBilateralEquality request = none := by
  simp [lowerRawLeftExactRightBilateralEquality,
    rawLeftExactRightBilateralEqualityRequestWellFormed,
    exactConstructedLeftReferenceNameAccepted,
    completeSourceEqualityMroForExactClass, mro]

theorem external_final_left_mro_refuses_bilateral_branch
    (request : RawLeftExactRightBilateralEqualityRequest)
    (className contractHash : String)
    (mro : request.left.completeResultMro =
      [.checkedExternal className contractHash, .objectDefault]) :
    lowerRawLeftExactRightBilateralEquality request = none := by
  simp [lowerRawLeftExactRightBilateralEquality,
    rawLeftExactRightBilateralEqualityRequestWellFormed,
    exactSourceReferenceFieldChainAccepted,
    completeSourceEqualityMroForExactClass, mro]

theorem not_equal_or_nonassert_refuses_raw_left_bilateral_branch
    (request : RawLeftExactRightBilateralEqualityRequest)
    (invalid : request.operator = .notEqual ∨ request.context = .requiresClause) :
    lowerRawLeftExactRightBilateralEquality request = none := by
  rcases invalid with notEqual | requiresContext
  · simp [lowerRawLeftExactRightBilateralEquality,
      rawLeftExactRightBilateralEqualityRequestWellFormed, notEqual]
  · simp [lowerRawLeftExactRightBilateralEquality,
      rawLeftExactRightBilateralEqualityRequestWellFormed, requiresContext]

/-!
## Typed effect-free heap conditional expressions and optional receivers

V41 adds a first-class, expression-level `thenValue if condition else elseValue` model to the heap
frontend.  The condition is evaluated first and must be Boolean.  Both branches must be total and
effect-free.  In the shipped slice they are also heap-read-free: calls, constructors, raw heap reads,
writes, permission transfers, exceptions, and heap/mask transitions all refuse.  The result is the VC
`ite`, and any condition-read obligations are unconditional.  This is not a model of Python
statement-level `if` control flow.

Scalar branches require the same supported scalar sort, except that a mixed Boolean/integer pair
uses Python's localized Boolean-to-integer coercion (`False`/`True` become `0`/`1`) and joins as an
integer.  Nominal branches retain one canonical catalog class when they are identical or when a
supplied catalog-subtype fact selects one branch's class as the common supertype.  Catalog evidence
may be verified source or a nonempty hash-bound checked-external contract because no provider
behavior executes.  Joining a nominal reference with literal `None` produces that
nominal type with `optional = true`.  The join creates neither non-nullness nor permission.  An
unrelated nominal pair, scalar/reference mixture, `None`/`None` without contextual nominal type,
dynamic/unchecked type, or effectful branch refuses.

A direct source instance call on the resulting value has a separate receiver-nonnull gate.  The
receiver is evaluated first; only a proved `receiver != null` may expose method permission
preconditions or proceed to the method transition.  A refuted or unresolved receiver leaves heap,
mask, assumptions, and method permission obligations unextended.  The same logical obligation maps
to Nagini's `call.precondition` for an ordinary method and `application.precondition` for a pure
method.  The exact `null_test` fixtures are instances of this algebra, not its definition.

These definitions prove only finite IR construction and ordering from frontend-supplied type,
subtype, effect, permission, and solver premises.  They do not prove Python/frontend
correspondence, truthiness, subtype extraction, solver validity, or method-summary correctness.
-/

def heapIfExpScalarSortSupported : ValueSort → Bool
  | .bool | .int => true
  | _ => false

structure ConditionalNominalType where
  canonicalClass : String
  optional : Bool
  sourceOwned : Bool
  checkedExternalContractHash : String
  deriving DecidableEq

def conditionalNominalTypeValidated (type : ConditionalNominalType) : Bool :=
  !type.canonicalClass.isEmpty &&
    (type.sourceOwned || !type.checkedExternalContractHash.isEmpty)

def conditionalNominalOriginsAgree
    (left right : ConditionalNominalType) : Bool :=
  (left.sourceOwned && right.sourceOwned) ||
    (!left.sourceOwned && !right.sourceOwned &&
      left.checkedExternalContractHash == right.checkedExternalContractHash)

inductive HeapConditionalType where
  | scalar (sort : ValueSort)
  | nominal (type : ConditionalNominalType)
  | nullOnly

inductive ConditionalNominalJoinEvidence where
  | sameCanonical
  | thenSubtypeOfElse
  | elseSubtypeOfThen
  | unavailable
  deriving DecidableEq

def joinHeapConditionalTypes
    (thenType elseType : HeapConditionalType)
    (nominalEvidence : ConditionalNominalJoinEvidence) : Option HeapConditionalType :=
  match thenType, elseType with
  | .scalar thenSort, .scalar elseSort =>
      if (thenSort == .bool && elseSort == .int) ||
          (thenSort == .int && elseSort == .bool) then
        some (.scalar .int)
      else if heapIfExpScalarSortSupported thenSort && thenSort == elseSort then
        some (.scalar thenSort)
      else none
  | .nominal thenNominal, .nominal elseNominal =>
      if !conditionalNominalTypeValidated thenNominal ||
          !conditionalNominalTypeValidated elseNominal then
        none
      else
        let optional := thenNominal.optional || elseNominal.optional
        match nominalEvidence with
        | .sameCanonical =>
            if thenNominal.canonicalClass == elseNominal.canonicalClass &&
                conditionalNominalOriginsAgree thenNominal elseNominal then
              some (.nominal { thenNominal with optional })
            else none
        | .thenSubtypeOfElse => some (.nominal { elseNominal with optional })
        | .elseSubtypeOfThen => some (.nominal { thenNominal with optional })
        | .unavailable => none
  | .nominal nominal, .nullOnly | .nullOnly, .nominal nominal =>
      if conditionalNominalTypeValidated nominal then
        some (.nominal { nominal with optional := true })
      else none
  | _, _ => none

def promoteHeapConditionalBoolToInt (value : Term) : Term :=
  .ite value (.intLiteral 1) (.intLiteral 0)

structure EffectFreeHeapIfExpBranch where
  value : Term
  valueType : HeapConditionalType
  literalNullReferenceProved : Bool
  heap : Nat
  mask : Nat
  valueTypeChecked : Bool
  totalProved : Bool
  noCallsOrConstructors : Bool
  noHeapWrites : Bool
  noPermissionTransfers : Bool
  noExceptionalOutcome : Bool

def heapConditionalBranchValueAtJoinedType
    (branch : EffectFreeHeapIfExpBranch) (joinedType : HeapConditionalType) : Term :=
  match branch.valueType, joinedType with
  | .scalar .bool, .scalar .int => promoteHeapConditionalBoolToInt branch.value
  | _, _ => branch.value

def effectFreeHeapIfExpBranchAccepted
    (branch : EffectFreeHeapIfExpBranch) : Bool :=
  branch.valueTypeChecked &&
    branch.totalProved &&
    branch.noCallsOrConstructors &&
    branch.noHeapWrites &&
    branch.noPermissionTransfers &&
    branch.noExceptionalOutcome &&
    match branch.valueType with
    | .scalar sort =>
        !branch.literalNullReferenceProved &&
          heapIfExpScalarSortSupported sort && inferSort branch.value == some sort
    | .nominal nominal =>
        !branch.literalNullReferenceProved && conditionalNominalTypeValidated nominal &&
          inferSort branch.value == some .reference
    | .nullOnly => branch.literalNullReferenceProved &&
        inferSort branch.value == some .reference

structure HeapIfExpRequest where
  condition : Term
  conditionHeap : Nat
  conditionMask : Nat
  conditionReadObligations : List Term
  conditionTotalAndEffectFree : Bool
  thenBranch : EffectFreeHeapIfExpBranch
  elseBranch : EffectFreeHeapIfExpBranch
  nominalJoinEvidence : ConditionalNominalJoinEvidence
  currentHeap : Nat
  currentMask : Nat

structure HeapIfExpTrace where
  value : Term
  valueType : HeapConditionalType
  heap : Nat
  mask : Nat
  obligations : List Term

def lowerHeapIfExp (request : HeapIfExpRequest) : Option HeapIfExpTrace :=
  if inferSort request.condition != some .bool ||
      !request.conditionTotalAndEffectFree ||
      request.conditionHeap != request.currentHeap ||
      request.conditionMask != request.currentMask ||
      request.thenBranch.heap != request.currentHeap ||
      request.thenBranch.mask != request.currentMask ||
      request.elseBranch.heap != request.currentHeap ||
      request.elseBranch.mask != request.currentMask ||
      !effectFreeHeapIfExpBranchAccepted request.thenBranch ||
      !effectFreeHeapIfExpBranchAccepted request.elseBranch then
    none
  else
    match joinHeapConditionalTypes request.thenBranch.valueType request.elseBranch.valueType
        request.nominalJoinEvidence with
    | none => none
    | some joinedType => some {
        value := .ite request.condition
          (heapConditionalBranchValueAtJoinedType request.thenBranch joinedType)
          (heapConditionalBranchValueAtJoinedType request.elseBranch joinedType)
        valueType := joinedType
        heap := request.currentHeap
        mask := request.currentMask
        obligations := request.conditionReadObligations
      }

theorem accepted_heap_ifexp_preserves_heap_and_mask
    (request : HeapIfExpRequest)
    (trace : HeapIfExpTrace)
    (accepted : lowerHeapIfExp request = some trace) :
    trace.heap = request.currentHeap ∧ trace.mask = request.currentMask := by
  unfold lowerHeapIfExp at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · cases accepted
      simp

theorem accepted_heap_ifexp_has_only_unconditional_condition_obligations
    (request : HeapIfExpRequest)
    (trace : HeapIfExpTrace)
    (accepted : lowerHeapIfExp request = some trace) :
    trace.obligations = request.conditionReadObligations := by
  unfold lowerHeapIfExp at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · cases accepted
      simp

theorem accepted_heap_ifexp_value_is_branch_selecting_ite
    (request : HeapIfExpRequest)
    (trace : HeapIfExpTrace)
    (accepted : lowerHeapIfExp request = some trace) :
    trace.value = .ite request.condition
      (heapConditionalBranchValueAtJoinedType request.thenBranch trace.valueType)
      (heapConditionalBranchValueAtJoinedType request.elseBranch trace.valueType) := by
  unfold lowerHeapIfExp at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · cases accepted
      simp

theorem typed_heap_ifexp_ite_preserves_common_branch_sort
    (condition thenValue elseValue : Term)
    (sort : ValueSort)
    (conditionTyped : inferSort condition = some .bool)
    (thenTyped : inferSort thenValue = some sort)
    (elseTyped : inferSort elseValue = some sort)
    (sortReflexive : valueSortBeq sort sort = true) :
    inferSort (.ite condition thenValue elseValue) = some sort := by
  simp [inferSort, conditionTyped, thenTyped, elseTyped, sortReflexive,
    instBEqValueSort, valueSortBeq]

theorem nominal_then_none_join_is_optional_without_nonnull_fact
    (nominal : ConditionalNominalType)
    (source : nominal.sourceOwned = true)
    (named : nominal.canonicalClass.isEmpty = false) :
    joinHeapConditionalTypes (.nominal nominal) .nullOnly .unavailable =
      some (.nominal { nominal with optional := true }) := by
  simp [joinHeapConditionalTypes, conditionalNominalTypeValidated, source, named]

theorem none_then_nominal_join_is_optional
    (nominal : ConditionalNominalType)
    (source : nominal.sourceOwned = true)
    (named : nominal.canonicalClass.isEmpty = false) :
    joinHeapConditionalTypes .nullOnly (.nominal nominal) .unavailable =
      some (.nominal { nominal with optional := true }) := by
  simp [joinHeapConditionalTypes, conditionalNominalTypeValidated, source, named]

theorem equal_scalar_heap_ifexp_types_join
    (sort : ValueSort)
    (supported : heapIfExpScalarSortSupported sort = true) :
    joinHeapConditionalTypes (.scalar sort) (.scalar sort) .unavailable =
      some (.scalar sort) := by
  cases sort <;> simp_all [heapIfExpScalarSortSupported, joinHeapConditionalTypes,
    instBEqValueSort, valueSortBeq]

theorem bool_int_heap_ifexp_types_join_as_int :
    joinHeapConditionalTypes (.scalar .bool) (.scalar .int) .unavailable =
      some (.scalar .int) := by
  simp [joinHeapConditionalTypes, instBEqValueSort, valueSortBeq]

theorem int_bool_heap_ifexp_types_join_as_int :
    joinHeapConditionalTypes (.scalar .int) (.scalar .bool) .unavailable =
      some (.scalar .int) := by
  simp [joinHeapConditionalTypes, instBEqValueSort, valueSortBeq]

theorem promoted_bool_heap_ifexp_branch_is_int_typed
    (value : Term)
    (typed : inferSort value = some .bool) :
    inferSort (promoteHeapConditionalBoolToInt value) = some .int := by
  simp [promoteHeapConditionalBoolToInt, inferSort, typed,
    instBEqValueSort, valueSortBeq]

theorem proved_then_subtype_joins_to_else_nominal
    (thenNominal elseNominal : ConditionalNominalType)
    (thenSource : thenNominal.sourceOwned = true)
    (elseSource : elseNominal.sourceOwned = true)
    (thenNamed : thenNominal.canonicalClass.isEmpty = false)
    (elseNamed : elseNominal.canonicalClass.isEmpty = false) :
    joinHeapConditionalTypes (.nominal thenNominal) (.nominal elseNominal)
      .thenSubtypeOfElse = some (.nominal {
        elseNominal with optional := thenNominal.optional || elseNominal.optional
      }) := by
  simp [joinHeapConditionalTypes, conditionalNominalTypeValidated,
    thenSource, elseSource, thenNamed, elseNamed]

theorem hash_bound_checked_external_heap_ifexp_nominals_join
    (className contractHash : String) (optional : Bool)
    (named : className.isEmpty = false)
    (hashed : contractHash.isEmpty = false) :
    let external : ConditionalNominalType := {
      canonicalClass := className
      optional := optional
      sourceOwned := false
      checkedExternalContractHash := contractHash
    }
    joinHeapConditionalTypes (.nominal external) (.nominal external) .sameCanonical =
      some (.nominal external) := by
  simp [joinHeapConditionalTypes, conditionalNominalTypeValidated,
    conditionalNominalOriginsAgree, named, hashed]

theorem incompatible_scalar_reference_heap_ifexp_refuses
    (sort : ValueSort) (nominal : ConditionalNominalType) :
    joinHeapConditionalTypes (.scalar sort) (.nominal nominal) .unavailable = none := by
  rfl

theorem effectful_heap_ifexp_branch_refuses
    (request : HeapIfExpRequest)
    (effectful : request.thenBranch.noHeapWrites = false ∨
      request.thenBranch.noPermissionTransfers = false ∨
      request.thenBranch.noExceptionalOutcome = false) :
    lowerHeapIfExp request = none := by
  rcases effectful with writes | transfer | exceptional
  · simp [lowerHeapIfExp, effectFreeHeapIfExpBranchAccepted, writes]
  · simp [lowerHeapIfExp, effectFreeHeapIfExpBranchAccepted, transfer]
  · simp [lowerHeapIfExp, effectFreeHeapIfExpBranchAccepted, exceptional]

inductive OptionalReceiverCallKind where
  | ordinaryMethod
  | pureApplication
  deriving DecidableEq

inductive OptionalReceiverDiagnostic where
  | callPrecondition
  | applicationPrecondition
  deriving DecidableEq

def optionalReceiverDiagnostic : OptionalReceiverCallKind → OptionalReceiverDiagnostic
  | .ordinaryMethod => .callPrecondition
  | .pureApplication => .applicationPrecondition

inductive ReceiverNonnullDisposition where
  | proved
  | refuted
  | unknown
  deriving DecidableEq

structure OptionalReceiverMethodSummary where
  methodName : String
  ownerCanonicalClass : String
  callKind : OptionalReceiverCallKind
  callKindSourceProved : Bool
  sourceOwned : Bool
  instanceMethod : Bool
  exactlyZeroArguments : Bool
  normalOnly : Bool
  completePermissionEffects : Bool
  permissionPreconditions : List Term

structure OptionalReceiverCallRequest where
  receiver : Term
  receiverCanonicalClass : String
  receiverOptional : Bool
  receiverEvaluationCompleted : Bool
  receiverEvaluationEffectFree : Bool
  heap : Nat
  mask : Nat
  assumptions : List Term
  priorObligations : List Term
  summary : OptionalReceiverMethodSummary

def optionalReceiverCallStructurallySupported
    (request : OptionalReceiverCallRequest) : Bool :=
  (inferSort request.receiver == some .reference) &&
    !request.receiverCanonicalClass.isEmpty &&
    request.receiverOptional &&
    request.receiverEvaluationCompleted &&
    request.receiverEvaluationEffectFree &&
    !request.summary.methodName.isEmpty &&
    (request.receiverCanonicalClass == request.summary.ownerCanonicalClass) &&
    request.summary.callKindSourceProved &&
    request.summary.sourceOwned &&
    request.summary.instanceMethod &&
    request.summary.exactlyZeroArguments &&
    request.summary.normalOnly &&
    request.summary.completePermissionEffects

def optionalReceiverNonnullObligation (request : OptionalReceiverCallRequest) : Term :=
  .not (.equal request.receiver .nullReference)

structure OptionalReceiverReadyTrace where
  receiver : Term
  heap : Nat
  mask : Nat
  assumptions : List Term
  obligations : List Term

structure OptionalReceiverFailureTrace where
  diagnostic : OptionalReceiverDiagnostic
  heap : Nat
  mask : Nat
  assumptions : List Term
  obligations : List Term

inductive OptionalReceiverCallOutcome where
  | readyForMethod (trace : OptionalReceiverReadyTrace)
  | receiverPreconditionFailed (trace : OptionalReceiverFailureTrace)
  | receiverPreconditionUnknown (trace : OptionalReceiverFailureTrace)
  | refused

def checkOptionalReceiverForMethod
    (request : OptionalReceiverCallRequest)
    (disposition : ReceiverNonnullDisposition) : OptionalReceiverCallOutcome :=
  if !optionalReceiverCallStructurallySupported request then .refused
  else
    let nonnull := optionalReceiverNonnullObligation request
    match disposition with
    | .proved => .readyForMethod {
        receiver := request.receiver
        heap := request.heap
        mask := request.mask
        assumptions := request.assumptions ++ [nonnull]
        obligations := request.priorObligations ++ [nonnull] ++
          request.summary.permissionPreconditions
      }
    | .refuted => .receiverPreconditionFailed {
        diagnostic := optionalReceiverDiagnostic request.summary.callKind
        heap := request.heap
        mask := request.mask
        assumptions := request.assumptions
        obligations := request.priorObligations ++ [nonnull]
      }
    | .unknown => .receiverPreconditionUnknown {
        diagnostic := optionalReceiverDiagnostic request.summary.callKind
        heap := request.heap
        mask := request.mask
        assumptions := request.assumptions
        obligations := request.priorObligations ++ [nonnull]
      }

theorem optional_receiver_nonnull_obligation_is_bool_typed
    (request : OptionalReceiverCallRequest)
    (receiverTyped : inferSort request.receiver = some .reference) :
    inferSort (optionalReceiverNonnullObligation request) = some .bool := by
  simp [optionalReceiverNonnullObligation, inferSort, receiverTyped,
    instBEqValueSort, valueSortBeq]

theorem proved_optional_receiver_exposes_method_permissions_after_nonnull
    (request : OptionalReceiverCallRequest)
    (supported : optionalReceiverCallStructurallySupported request = true) :
    checkOptionalReceiverForMethod request .proved = .readyForMethod {
      receiver := request.receiver
      heap := request.heap
      mask := request.mask
      assumptions := request.assumptions ++ [optionalReceiverNonnullObligation request]
      obligations := request.priorObligations ++ [optionalReceiverNonnullObligation request] ++
        request.summary.permissionPreconditions
    } := by
  simp [checkOptionalReceiverForMethod, supported]

theorem refuted_optional_receiver_is_absorbing_before_method_permissions
    (request : OptionalReceiverCallRequest)
    (supported : optionalReceiverCallStructurallySupported request = true) :
    checkOptionalReceiverForMethod request .refuted = .receiverPreconditionFailed {
      diagnostic := optionalReceiverDiagnostic request.summary.callKind
      heap := request.heap
      mask := request.mask
      assumptions := request.assumptions
      obligations := request.priorObligations ++ [optionalReceiverNonnullObligation request]
    } := by
  simp [checkOptionalReceiverForMethod, supported]

theorem null_test_refutes_with_call_precondition
    (request : OptionalReceiverCallRequest)
    (supported : optionalReceiverCallStructurallySupported request = true)
    (ordinary : request.summary.callKind = .ordinaryMethod) :
    match checkOptionalReceiverForMethod request .refuted with
    | .receiverPreconditionFailed trace => trace.diagnostic = .callPrecondition
    | _ => False := by
  simp [checkOptionalReceiverForMethod, supported, optionalReceiverDiagnostic, ordinary]

theorem null_test_pure_refutes_with_application_precondition
    (request : OptionalReceiverCallRequest)
    (supported : optionalReceiverCallStructurallySupported request = true)
    (pure : request.summary.callKind = .pureApplication) :
    match checkOptionalReceiverForMethod request .refuted with
    | .receiverPreconditionFailed trace => trace.diagnostic = .applicationPrecondition
    | _ => False := by
  simp [checkOptionalReceiverForMethod, supported, optionalReceiverDiagnostic, pure]

theorem unknown_optional_receiver_does_not_expose_method_permissions
    (request : OptionalReceiverCallRequest)
    (supported : optionalReceiverCallStructurallySupported request = true) :
    checkOptionalReceiverForMethod request .unknown = .receiverPreconditionUnknown {
      diagnostic := optionalReceiverDiagnostic request.summary.callKind
      heap := request.heap
      mask := request.mask
      assumptions := request.assumptions
      obligations := request.priorObligations ++ [optionalReceiverNonnullObligation request]
    } := by
  simp [checkOptionalReceiverForMethod, supported]

/-!
## Statement-level heap conditionals: typed-local, state-neutral v42 slice

The constructive local-type/provenance join functions in this section remain part of the formal
algebra.  The former witness-driven `HeapStatementBranchTrace`, `HeapStatementIfRequest`, and
`lowerHeapStatementIf` APIs have been removed: their Boolean closure fields did not establish
execution.  The authoritative recursive statement semantics is `Maledictus.HeapControl`.

This section models the first deliberately narrow statement-level Python `if`/`else` slice.  A
Boolean, total, state-neutral condition is evaluated before the state is split.  The then entry adds
the condition and the else entry adds its negation.  This file defines only the shared state and
constructive typed-local join algebra; the accepted statement grammar and its recursive execution
are represented by `ExecutableHeapStmt` and `executeExecutableHeapBlock` in `HeapControl`.

The normal-state join is constructive rather than an assertion supplied by the frontend.  Both
branch environments must have the same canonical binding order.  Corresponding scalar values join
at equal sorts or through the localized Boolean-to-integer promotion.  Nominal references require a
supplied canonical same/subtype relation and propagate optionality.  The catalog type may be
verified source or hash-bound checked external.  Exact-runtime and source-construction provenance
remains source-only and survives only when both branches prove it for the identical term and class.
Otherwise the result binds the local to an `ite`.  Path-local assumptions are not promoted to
unconditional facts after the join, and a local absent from either environment fails the domain
check.  These join functions prove finite IR algebra, not Python/frontend correspondence or the
truth of branch execution, typing, reachability, permission, or solver evidence.
-/

structure HeapStatementNominalType where
  canonicalClass : String
  optional : Bool
  sourceOwned : Bool
  checkedExternalContractHash : String

def heapStatementNominalTypeValidated (type : HeapStatementNominalType) : Bool :=
  !type.canonicalClass.isEmpty &&
    (type.sourceOwned || !type.checkedExternalContractHash.isEmpty)

def heapStatementNominalOriginsAgree
    (left right : HeapStatementNominalType) : Bool :=
  (left.sourceOwned && right.sourceOwned) ||
    (!left.sourceOwned && !right.sourceOwned &&
      left.checkedExternalContractHash == right.checkedExternalContractHash)

inductive HeapStatementLocalType where
  | scalar (sort : ValueSort)
  | nominal (type : HeapStatementNominalType)
  | nullOnly
  | opaqueObject

structure HeapStatementLocal where
  name : String
  value : Term
  valueType : HeapStatementLocalType
  exactRuntimeClassProved : Bool
  sourceConstructedProved : Bool

abbrev HeapStatementEnvironment := List HeapStatementLocal

structure HeapStatementLocalJoinEvidence where
  name : String
  nominalEvidence : ConditionalNominalJoinEvidence
  sameTermProved : Bool

structure HeapFunctionState where
  environment : HeapStatementEnvironment
  heap : Nat
  mask : Nat
  assumptions : List Term
  obligations : List Term

def heapStatementThenEntry (state : HeapFunctionState) (condition : Term) : HeapFunctionState :=
  { state with assumptions := state.assumptions ++ [condition] }

def heapStatementElseEntry (state : HeapFunctionState) (condition : Term) : HeapFunctionState :=
  { state with assumptions := state.assumptions ++ [.not condition] }

def heapStatementLocalTypeSort : HeapStatementLocalType → ValueSort
  | .scalar sort => sort
  | .nominal _ | .nullOnly | .opaqueObject => .reference

def joinHeapStatementLocalTypes
    (thenType elseType : HeapStatementLocalType)
    (evidence : ConditionalNominalJoinEvidence) : Option HeapStatementLocalType :=
  match thenType, elseType with
  | .scalar .bool, .scalar .int | .scalar .int, .scalar .bool => some (.scalar .int)
  | .scalar thenSort, .scalar elseSort =>
      if heapIfExpScalarSortSupported thenSort && thenSort == elseSort
      then some (.scalar thenSort) else none
  | .nominal thenType, .nominal elseType =>
      if !heapStatementNominalTypeValidated thenType ||
          !heapStatementNominalTypeValidated elseType then none
      else
        let optional := thenType.optional || elseType.optional
        match evidence with
        | .sameCanonical =>
            if thenType.canonicalClass == elseType.canonicalClass &&
                heapStatementNominalOriginsAgree thenType elseType then
              some (.nominal { thenType with optional }) else none
        | .thenSubtypeOfElse => some (.nominal { elseType with optional })
        | .elseSubtypeOfThen => some (.nominal { thenType with optional })
        | .unavailable => none
  | .nominal nominal, .nullOnly | .nullOnly, .nominal nominal =>
      if heapStatementNominalTypeValidated nominal
      then some (.nominal { nominal with optional := true }) else none
  | .nullOnly, .nullOnly => some .nullOnly
  | _, _ => none

def heapStatementLocalTypesHaveIdenticalNominalClass
    (thenType elseType : HeapStatementLocalType) : Bool :=
  match thenType, elseType with
  | .nominal thenType, .nominal elseType =>
      thenType.sourceOwned && elseType.sourceOwned &&
        heapStatementNominalTypeValidated thenType &&
        heapStatementNominalTypeValidated elseType &&
        thenType.canonicalClass == elseType.canonicalClass
  | _, _ => false

def preserveHeapStatementLocalProvenance
    (sameTerm leftProved rightProved : Bool)
    (leftType rightType : HeapStatementLocalType) : Bool :=
  sameTerm && heapStatementLocalTypesHaveIdenticalNominalClass leftType rightType &&
    leftProved && rightProved

def heapStatementLocalValueAtJoinedType
    (binding : HeapStatementLocal) (joinedType : HeapStatementLocalType) : Term :=
  match binding.valueType, joinedType with
  | .scalar .bool, .scalar .int => promoteHeapConditionalBoolToInt binding.value
  | _, _ => binding.value

def joinHeapStatementLocals
    (condition : Term)
    (thenLocal elseLocal : HeapStatementLocal)
    (evidence : HeapStatementLocalJoinEvidence) : Option HeapStatementLocal :=
  if thenLocal.name != elseLocal.name || thenLocal.name != evidence.name ||
      inferSort thenLocal.value != some (heapStatementLocalTypeSort thenLocal.valueType) ||
      inferSort elseLocal.value != some (heapStatementLocalTypeSort elseLocal.valueType) then
    none
  else
    match joinHeapStatementLocalTypes thenLocal.valueType elseLocal.valueType
        evidence.nominalEvidence with
    | none => none
    | some joinedType =>
        let thenValue := heapStatementLocalValueAtJoinedType thenLocal joinedType
        let elseValue := heapStatementLocalValueAtJoinedType elseLocal joinedType
        some {
          name := thenLocal.name
          value := if evidence.sameTermProved then thenValue
            else .ite condition thenValue elseValue
          valueType := joinedType
          exactRuntimeClassProved := preserveHeapStatementLocalProvenance
            evidence.sameTermProved thenLocal.exactRuntimeClassProved
            elseLocal.exactRuntimeClassProved thenLocal.valueType elseLocal.valueType
          sourceConstructedProved := preserveHeapStatementLocalProvenance
            evidence.sameTermProved thenLocal.sourceConstructedProved
            elseLocal.sourceConstructedProved thenLocal.valueType elseLocal.valueType
        }

def joinHeapStatementEnvironments (condition : Term) :
    HeapStatementEnvironment → HeapStatementEnvironment →
      List HeapStatementLocalJoinEvidence → Option HeapStatementEnvironment
  | [], [], [] => some []
  | thenLocal :: thenRest, elseLocal :: elseRest, evidence :: evidenceRest =>
      match joinHeapStatementLocals condition thenLocal elseLocal evidence,
          joinHeapStatementEnvironments condition thenRest elseRest evidenceRest with
      | some joinedLocal, some joinedRest => some (joinedLocal :: joinedRest)
      | _, _ => none
  | _, _, _ => none

theorem statement_if_split_adds_opposite_path_assumptions
    (state : HeapFunctionState) (condition : Term) :
    (heapStatementThenEntry state condition).assumptions = state.assumptions ++ [condition] ∧
      (heapStatementElseEntry state condition).assumptions =
        state.assumptions ++ [.not condition] := by
  simp [heapStatementThenEntry, heapStatementElseEntry]

theorem statement_if_split_preserves_heap_and_mask
    (state : HeapFunctionState) (condition : Term) :
    (heapStatementThenEntry state condition).heap = state.heap ∧
      (heapStatementThenEntry state condition).mask = state.mask ∧
      (heapStatementElseEntry state condition).heap = state.heap ∧
      (heapStatementElseEntry state condition).mask = state.mask := by
  simp [heapStatementThenEntry, heapStatementElseEntry]

theorem statement_if_equal_bool_locals_join_as_bool_ite
    : joinHeapStatementLocalTypes (.scalar .bool) (.scalar .bool) .unavailable =
      some (.scalar .bool) := by
  simp [joinHeapStatementLocalTypes, heapIfExpScalarSortSupported,
    instBEqValueSort, valueSortBeq]

theorem statement_if_equal_int_locals_join_as_int_ite
    : joinHeapStatementLocalTypes (.scalar .int) (.scalar .int) .unavailable =
      some (.scalar .int) := by
  simp [joinHeapStatementLocalTypes, heapIfExpScalarSortSupported,
    instBEqValueSort, valueSortBeq]

theorem statement_if_bool_int_local_join_promotes_bool
    : joinHeapStatementLocalTypes (.scalar .bool) (.scalar .int) .unavailable =
      some (.scalar .int) := by
  rfl

theorem statement_if_nominal_subtype_join_propagates_optionality
    (thenType elseType : HeapStatementNominalType)
    (thenValid : heapStatementNominalTypeValidated thenType = true)
    (elseValid : heapStatementNominalTypeValidated elseType = true) :
    joinHeapStatementLocalTypes (.nominal thenType) (.nominal elseType)
      .thenSubtypeOfElse = some (.nominal {
        elseType with optional := thenType.optional || elseType.optional
      }) := by
  simp [joinHeapStatementLocalTypes, thenValid, elseValid]

theorem statement_if_scalar_nominal_local_join_refuses
    (sort : ValueSort) (nominal : HeapStatementNominalType) :
    joinHeapStatementLocalTypes (.scalar sort) (.nominal nominal) .unavailable = none := by
  cases sort <;> rfl

theorem statement_if_nominal_none_join_is_optional
    (nominal : HeapStatementNominalType)
    (valid : heapStatementNominalTypeValidated nominal = true) :
    joinHeapStatementLocalTypes (.nominal nominal) .nullOnly .unavailable =
      some (.nominal { nominal with optional := true }) := by
  simp [joinHeapStatementLocalTypes, valid]

theorem statement_if_hash_bound_checked_external_nominal_join_is_allowed
    (className contractHash : String) (optional : Bool)
    (named : className.isEmpty = false)
    (hashed : contractHash.isEmpty = false) :
    let external : HeapStatementNominalType := {
      canonicalClass := className
      optional := optional
      sourceOwned := false
      checkedExternalContractHash := contractHash
    }
    joinHeapStatementLocalTypes (.nominal external) (.nominal external) .sameCanonical =
      some (.nominal external) := by
  simp [joinHeapStatementLocalTypes, heapStatementNominalTypeValidated,
    heapStatementNominalOriginsAgree, named, hashed]

theorem statement_if_unchecked_external_nominal_join_refuses
    (className : String) (optional : Bool) :
    let external : HeapStatementNominalType := {
      canonicalClass := className
      optional := optional
      sourceOwned := false
      checkedExternalContractHash := ""
    }
    joinHeapStatementLocalTypes (.nominal external) (.nominal external) .sameCanonical = none := by
  have emptyHash : "".isEmpty = true := rfl
  simp [joinHeapStatementLocalTypes, heapStatementNominalTypeValidated, emptyHash]

theorem statement_if_nonidentical_join_drops_exact_and_constructed_provenance
    (condition : Term) (thenLocal elseLocal : HeapStatementLocal)
    (evidence : HeapStatementLocalJoinEvidence)
    (notSame : evidence.sameTermProved = false)
    (joined : HeapStatementLocal)
    (success : joinHeapStatementLocals condition thenLocal elseLocal evidence = some joined) :
    joined.exactRuntimeClassProved = false ∧ joined.sourceConstructedProved = false := by
  unfold joinHeapStatementLocals at success
  split at success
  · simp at success
  · split at success
    · simp at success
    · cases success
      simp [notSame, preserveHeapStatementLocalProvenance]

theorem statement_if_identical_source_nominal_term_preserves_provenance
    (className : String) (thenOptional elseOptional : Bool)
    (named : className.isEmpty = false) :
    let thenType : HeapStatementNominalType := {
      canonicalClass := className
      optional := thenOptional
      sourceOwned := true
      checkedExternalContractHash := ""
    }
    let elseType : HeapStatementNominalType := {
      canonicalClass := className
      optional := elseOptional
      sourceOwned := true
      checkedExternalContractHash := ""
    }
    preserveHeapStatementLocalProvenance true true true
      (.nominal thenType) (.nominal elseType) = true := by
  simp [preserveHeapStatementLocalProvenance,
    heapStatementLocalTypesHaveIdenticalNominalClass,
    heapStatementNominalTypeValidated, named]

theorem statement_if_environment_domain_mismatch_refuses
    (condition : Term) (binding : HeapStatementLocal) (rest : HeapStatementEnvironment)
    (evidence : List HeapStatementLocalJoinEvidence) :
    joinHeapStatementEnvironments condition (binding :: rest) [] evidence = none := by
  rfl

/-!
## Guarded path sets and early returns (v43)

The former witness-driven branch-result, continuation-consumption, return-request, and
postcondition-completeness APIs have been removed.  Certificates cite the recursive
`Maledictus.HeapControl` semantics and its finalizer, which constructs actual paths and instantiates
the one function-bound postcondition list. This section retains the supported-return coercion used
by that executable semantics.

From the first return-containing conditional through the remaining function body, v43 does not
merge divergent control-flow states. Earlier v42-pure conditionals may retain their exact typed
local join. The return-sensitive region retains every guarded state across both normal
continuations and completed returns. A read-free Boolean condition splits one incoming
normal state in Python order: the then path conjoins the condition, the else path its negation, and
both preserve that path's heap and permission mask.  Branch execution remains the pure v42
statement subset.  Calls, constructors, field reads/writes, permission changes, contracts inside a
branch, exceptional outcomes, and other effects still refuse until a later fragment.

An explicit return supports only the existing heap-function `None`/Boolean/integer result sorts.  It
is checked against the declared sort after the existing localized Boolean-to-integer promotion,
preserves its path heap/mask, appends that exit's independently
instantiated postcondition obligations under the path guard, and moves the state out of the normal
set.  Returned states remain counted but never execute a continuation.  At function end, Unit
fallthrough becomes an implicit Unit return; any reachable non-Unit fallthrough refuses.  An absent
`else` is one unchanged normal path, and nested conditionals compose by exact list union without
dropping or merging a path.

`HeapControl` proves finite guarded-state execution once a typed IR and source summaries are
supplied.  It does not prove Python AST correspondence, source-summary truth, branch reachability,
or solver validity, and no theorem licenses a conditional heap or mask merge.
-/

def heapV43ReturnSortSupported : ValueSort → Bool
  | .unit | .bool | .int => true
  | _ => false

def coerceV43ReturnValue (declaredSort : ValueSort) (value : Term) : Term :=
  if declaredSort == .int && inferSort value == some .bool then
    promoteHeapConditionalBoolToInt value
  else value

/-!
## Path-local verified source effects (v44)

The former `GuardedPathLocalSourceEffectRequest` batch/failure APIs have been removed.  Their
caller-supplied exit states and Boolean parity/completeness fields could not certify an effect
transition.  Certificates cite `Maledictus.HeapControl`, whose typed effect constructors compute
the next state and whose recursive executor applies them only to normal paths.  This section
retains only the constructive field-write type-compatibility relation used by that executor.

V44 keeps v43's guarded states separate when a conditional subtree contains a supported source
effect, even if the subtree has no return.  Each normal path invokes the same frontend transition
used for the corresponding top-level statement and retains its own environment, assumptions,
obligations, heap, and permission-mask versions.  Returned paths are not inputs to that transition.

The shipped effect subset is deliberately finite: a normal-only verified source constructor
assignment, a normal-only verified source instance-method call, or a direct write to a verified
source field.  Constructor allocation is fresh and leaves the existing heap/mask versions intact;
method summaries advance heap and mask exactly when their complete write and permission-transfer
summaries say so; a direct field write advances the heap once, preserves the mask, and emits the
full-permission obligation.  Every transition must preserve prior obligations, instantiate all
pre/post/frame/permission facts, preserve Python evaluation order, and match the shared ordinary
statement executor.  Dynamic or checked-external behavior, properties/descriptors, predicate
ownership transfer, exceptional outcomes, calls in guards/returns/contracts, and unsupported call
shapes still refuse.  A refuted receiver or method/constructor precondition retains its
path-qualified failing obligation, rolls heap/mask and supplied environment/assumption state back
to the entry versions, and halts only that path before any later effect. Halted paths, like returned
paths, never enter continuation.

The executable IR still relies on frontend-supplied source-summary, source-ownership, and
AST-lowering premises; it does not prove Python correspondence, permission/subtype truth, exception
freedom, solver results, or parity with the production executor.  A successful symbolic transition
may carry proof obligations, and certificate acceptance must discharge them.
-/

inductive GuardedFieldWriteNominalEvidence where
  | sameCanonical
  | actualSubtypeOfField
  | unavailable
  deriving DecidableEq

def guardedFieldWriteTypesCompatible
    (fieldType assignedType : HeapStatementLocalType)
    (nominalEvidence : GuardedFieldWriteNominalEvidence) : Bool :=
  match fieldType, assignedType with
  | .scalar fieldSort, .scalar assignedSort => fieldSort == assignedSort
  | .nominal fieldNominal, .nominal assignedNominal =>
      if !heapStatementNominalTypeValidated fieldNominal ||
          !heapStatementNominalTypeValidated assignedNominal ||
          (assignedNominal.optional && !fieldNominal.optional) then false
      else
        match nominalEvidence with
        | .sameCanonical => fieldNominal.canonicalClass == assignedNominal.canonicalClass
        | .actualSubtypeOfField => true
        | .unavailable => false
  | .nominal fieldNominal, .nullOnly =>
      heapStatementNominalTypeValidated fieldNominal && fieldNominal.optional
  | _, _ => false

end Maledictus
