import Maledictus.HeapControl

namespace Maledictus

/-!
# Ordinary-method nominal results and native assertions (v54)

This module adds the bounded constructive part of the v54 ordinary-method frontend to the
authoritative executable heap paths.  A source method's nominal result type is derived from its
selected summary; it is not accepted as a second caller-supplied target type.  Calls and assertions
run against the path's current heap and permission-mask versions, and constructor-field reads are
checked against a path-local initialized-field set.

The frontend still has to prove Python-AST correspondence, summary selection and truth, and proof
kernel dispositions.  Missing or malformed summaries, uninitialized reads, unresolved proof
results, ill-typed obligations, and unsupported receiver/result shapes return `none`.
-/

structure ExecutableV54NominalMethodSummary where
  ownerCanonicalClass : String
  methodName : String
  resultCanonicalClass : String
  resultOptional : Bool
  sourceOwned : Bool

def executableV54NominalMethodSummaryValid
    (summary : ExecutableV54NominalMethodSummary) : Bool :=
  !summary.ownerCanonicalClass.isEmpty &&
    !summary.methodName.isEmpty &&
    !summary.resultCanonicalClass.isEmpty &&
    summary.sourceOwned

def executableV54NominalResultType
    (summary : ExecutableV54NominalMethodSummary) : HeapStatementLocalType :=
  .nominal {
    canonicalClass := summary.resultCanonicalClass
    optional := summary.resultOptional
    sourceOwned := true
    checkedExternalContractHash := ""
  }

structure ExecutableV54MethodPath where
  core : ExecutableHeapPath
  initializedConstructorFields : List String

def executableV54ReadsInitialized
    (path : ExecutableV54MethodPath) (required : List String) : Bool :=
  required.all path.initializedConstructorFields.contains

structure ExecutableV54DirectSourceResult where
  className : String

structure ExecutableV54NominalMethodCall where
  receiverKind : MethodReceiverKind
  receiver : Option HeapStatementLocal
  targetName : String
  result : Term
  summary : Option ExecutableV54NominalMethodSummary
  directSourceResult : Option ExecutableV54DirectSourceResult
  transferredResultField : Option String
  requiredInitializedFields : List String
  heapTransition : ExecutableVersionTransition
  maskTransition : ExecutableVersionTransition
  preconditionObligations : List Term
  permissionObligations : List Term
  postconditionFacts : List Term
  frameFacts : List Term
  preconditionDisposition : ExecutableProofDisposition
  permissionDisposition : ExecutableProofDisposition

def executableV54CallReceiverSupported
    (call : ExecutableV54NominalMethodCall)
    (summary : ExecutableV54NominalMethodSummary) : Bool :=
  match call.receiverKind, call.receiver with
  | .instance, some receiver =>
      match receiver.valueType with
      | .nominal nominal =>
          inferSort receiver.value == some .reference && nominal.sourceOwned &&
            heapStatementNominalTypeValidated nominal &&
            nominal.canonicalClass == summary.ownerCanonicalClass
      | _ => false
  | .static, none => resolveClassQualifiedCall .static == .succeeded
  | _, _ => false

def executableV54CallReceiverObligations
    (call : ExecutableV54NominalMethodCall) : List Term :=
  match call.receiverKind, call.receiver with
  | .instance, some receiver => [.not (.equal receiver.value .nullReference)]
  | .static, none => []
  | _, _ => []

def executableV54CallPreconditionObligations
    (call : ExecutableV54NominalMethodCall) : List Term :=
  executableV54CallReceiverObligations call ++ call.preconditionObligations

def executableV54CallObligations
    (call : ExecutableV54NominalMethodCall) : List Term :=
  executableV54CallPreconditionObligations call ++ call.permissionObligations

structure ExecutableV54FreshResultTransfer where
  freshnessFacts : List Term
  permissionFacts : List Term

def executableV54FreshResultZeroPermission
    (preMask : Nat) (result : Term) (field : String) : Term :=
  .permissionAtMost preMask result field 0 1

def executableV54FreshResultPermissionTransition
    (preMask postMask : Nat) (result : Term) (field : String) : Term :=
  .permissionMaskTransition preMask postMask field [] [(result, 1, 1)]

def executableV54FreshResultTransferObligations
    (preMask postMask : Nat) (result : Term) (field : String) : List Term :=
  [
    executableV54FreshResultZeroPermission preMask result field,
    .permissionMaskValid preMask field,
    executableV54FreshResultPermissionTransition preMask postMask result field,
    .permissionMaskValid postMask field
  ]

def executableV54PrepareFreshResultTransfer
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (summary : ExecutableV54NominalMethodSummary) :
    Option ExecutableV54FreshResultTransfer :=
  match call.directSourceResult, call.transferredResultField with
  | none, none => some { freshnessFacts := [], permissionFacts := [] }
  | some directSource, transferredField =>
      if directSource.className.isEmpty || inferSort call.result != some .reference ||
          directSource.className != summary.resultCanonicalClass then none
      else
        match transferredField with
        | none => some {
            freshnessFacts := executableConstructorFreshFacts call.result
              directSource.className path.core.state.environment
            permissionFacts := []
          }
        | some field =>
            if field.isEmpty || call.maskTransition != .advances then none
            else
              let postMask := executableNextVersion path.core.state.mask call.maskTransition
              some {
                freshnessFacts := executableConstructorFreshFacts call.result
                  directSource.className path.core.state.environment
                permissionFacts := executableV54FreshResultTransferObligations
                  path.core.state.mask postMask call.result field
              }
  | none, some _ => none

structure ExecutableV54ConstructedNominalCall where
  resultBinding : HeapStatementLocal
  heapTransition : ExecutableVersionTransition
  maskTransition : ExecutableVersionTransition
  obligations : List Term
  postconditionFacts : List Term
  frameFacts : List Term

def executableV54ConstructNominalMethodCall
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath) :
    Option ExecutableV54ConstructedNominalCall :=
  match call.summary with
  | none => none
  | some summary =>
      match executableV54PrepareFreshResultTransfer call path summary with
      | none => none
      | some transfer =>
          if !executableV54NominalMethodSummaryValid summary ||
              !executableV54CallReceiverSupported call summary || call.targetName.isEmpty ||
              inferSort call.result != some .reference ||
              !executableV54ReadsInitialized path call.requiredInitializedFields ||
              !executableTermsAreBoolean
                (transfer.freshnessFacts ++ transfer.permissionFacts ++
                  call.postconditionFacts) ||
              !executableTermsAreBoolean (executableV54CallObligations call) ||
              !executableTermsAreBoolean call.frameFacts then none
          else some {
            resultBinding := {
              name := call.targetName
              value := call.result
              valueType := executableV54NominalResultType summary
              exactRuntimeClassProved := false
              sourceConstructedProved := false
            }
            heapTransition := call.heapTransition
            maskTransition := call.maskTransition
            obligations := executableV54CallObligations call
            postconditionFacts := transfer.freshnessFacts ++ transfer.permissionFacts ++
              call.postconditionFacts
            frameFacts := call.frameFacts
          }

def executableV54ApplyNominalMethodCall
    (effect : ExecutableV54ConstructedNominalCall) (path : ExecutableV54MethodPath) :
    ExecutableV54MethodPath :=
  { path with core := { path.core with state := {
      environment := executableBindLocal path.core.state.environment effect.resultBinding
      heap := executableNextVersion path.core.state.heap effect.heapTransition
      mask := executableNextVersion path.core.state.mask effect.maskTransition
      assumptions := path.core.state.assumptions ++ effect.frameFacts ++
        effect.postconditionFacts
      obligations := path.core.state.obligations ++ effect.obligations
    } } }

def executeExecutableV54NominalMethodCall
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath) :
    Option ExecutableV54MethodPath :=
  match path.core.status with
  | .returned _ | .halted _ => some path
  | .normal =>
      match executableV54ConstructNominalMethodCall call path with
      | none => none
      | some effect =>
          match call.preconditionDisposition with
          | .unresolved => none
          | .refuted failed => some { path with core := (executableHaltPath path.core
              (executableV54CallPreconditionObligations call) failed) }
          | .proved =>
              match call.permissionDisposition with
              | .unresolved => none
              | .refuted failed => some { path with core := (executableHaltPath path.core
                  (executableV54CallObligations call) failed) }
              | .proved => some (executableV54ApplyNominalMethodCall effect path)

structure ExecutableV54NativeAssertion where
  condition : Nat -> Nat -> Term
  obligations : Nat -> Nat -> List Term
  requiredInitializedFields : List String
  disposition : ExecutableProofDisposition

def executableV54NativeAssertionObligations
    (assertion : ExecutableV54NativeAssertion) (path : ExecutableV54MethodPath) : List Term :=
  assertion.obligations path.core.state.heap path.core.state.mask ++
    [assertion.condition path.core.state.heap path.core.state.mask]

def executeExecutableV54NativeAssertion
    (assertion : ExecutableV54NativeAssertion) (path : ExecutableV54MethodPath) :
    Option ExecutableV54MethodPath :=
  match path.core.status with
  | .returned _ | .halted _ => some path
  | .normal =>
      let obligations := executableV54NativeAssertionObligations assertion path
      if !executableV54ReadsInitialized path assertion.requiredInitializedFields ||
          !executableTermsAreBoolean obligations then none
      else
        match assertion.disposition with
        | .unresolved => none
        | .refuted failed => some { path with core :=
            (executableHaltPath path.core obligations failed) }
        | .proved => some { path with core := ({ path.core with state := {
            path.core.state with obligations := path.core.state.obligations ++ obligations }} :
              ExecutableHeapPath) }

inductive ExecutableV54OrdinaryMethodStmt where
  | nominalCall (call : ExecutableV54NominalMethodCall)
  | nativeAssertion (assertion : ExecutableV54NativeAssertion)

def executeExecutableV54OrdinaryMethodStmt
    (statement : ExecutableV54OrdinaryMethodStmt) (path : ExecutableV54MethodPath) :
    Option ExecutableV54MethodPath :=
  match statement with
  | .nominalCall call => executeExecutableV54NominalMethodCall call path
  | .nativeAssertion assertion => executeExecutableV54NativeAssertion assertion path

def executeExecutableV54OrdinaryMethodBlock
    (statements : List ExecutableV54OrdinaryMethodStmt)
    (paths : List ExecutableV54MethodPath) : Option (List ExecutableV54MethodPath) :=
  match statements with
  | [] => some paths
  | statement :: rest =>
      match paths.mapM (executeExecutableV54OrdinaryMethodStmt statement) with
      | none => none
      | some next => executeExecutableV54OrdinaryMethodBlock rest next
termination_by statements.length

theorem executable_v54_missing_nominal_summary_refuses
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (missing : call.summary = none) :
    executableV54ConstructNominalMethodCall call path = none := by
  simp [executableV54ConstructNominalMethodCall, missing]

theorem executable_v54_direct_source_allocation_constructs_environment_freshness
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (summary : ExecutableV54NominalMethodSummary)
    (directSource : ExecutableV54DirectSourceResult)
    (source : call.directSourceResult = some directSource)
    (noTransfer : call.transferredResultField = none)
    (named : directSource.className.isEmpty = false)
    (resultTyped : inferSort call.result = some .reference)
    (classMatch : directSource.className = summary.resultCanonicalClass) :
    executableV54PrepareFreshResultTransfer call path summary = some {
      freshnessFacts := executableConstructorFreshFacts call.result
        directSource.className path.core.state.environment
      permissionFacts := []
    } := by
  have summaryNamed : summary.resultCanonicalClass.isEmpty = false := by
    simpa [classMatch] using named
  have resultAccepted : (inferSort call.result != some .reference) = false := by
    rw [resultTyped]
    rfl
  simp [executableV54PrepareFreshResultTransfer, source, noTransfer,
    resultAccepted, classMatch, summaryNamed]

theorem executable_v54_fresh_result_permission_sequence_starts_at_zero
    (preMask postMask : Nat) (result : Term) (field : String) :
    (executableV54FreshResultTransferObligations
      preMask postMask result field).head? =
        some (executableV54FreshResultZeroPermission preMask result field) := by
  rfl

theorem executable_v54_fresh_result_transfer_preserves_mask_validity
    (preMask : Nat) (result : Term) (field : String)
    (resultTyped : inferSort result = some .reference)
    (fieldNamed : field.isEmpty = false) :
    let postMask := executableNextVersion preMask .advances
    inferSort (.permissionMaskValid preMask field) = some .bool ∧
      inferSort (executableV54FreshResultPermissionTransition
        preMask postMask result field) = some .bool ∧
      inferSort (.permissionMaskValid postMask field) = some .bool := by
  simp [executableV54FreshResultPermissionTransition, executableNextVersion,
    inferSort, allPermissionTransferAmounts, resultTyped, fieldNamed,
    instBEqValueSort, valueSortBeq]

theorem executable_v54_verified_fresh_result_constructs_exact_transfer
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (summary : ExecutableV54NominalMethodSummary)
    (directSource : ExecutableV54DirectSourceResult) (field : String)
    (source : call.directSourceResult = some directSource)
    (transferred : call.transferredResultField = some field)
    (named : directSource.className.isEmpty = false)
    (resultTyped : inferSort call.result = some .reference)
    (classMatch : directSource.className = summary.resultCanonicalClass)
    (fieldNamed : field.isEmpty = false)
    (advances : call.maskTransition = .advances) :
    executableV54PrepareFreshResultTransfer call path summary = some {
      freshnessFacts := executableConstructorFreshFacts call.result
        directSource.className path.core.state.environment
      permissionFacts := executableV54FreshResultTransferObligations
        path.core.state.mask (executableNextVersion path.core.state.mask .advances)
          call.result field
    } := by
  have summaryNamed : summary.resultCanonicalClass.isEmpty = false := by
    simpa [classMatch] using named
  have resultAccepted : (inferSort call.result != some .reference) = false := by
    rw [resultTyped]
    rfl
  simp [executableV54PrepareFreshResultTransfer, source, transferred,
    resultAccepted, classMatch, summaryNamed, fieldNamed, advances]

theorem executable_v54_unverified_fresh_result_transfer_refuses
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (summary : ExecutableV54NominalMethodSummary) (field : String)
    (selected : call.summary = some summary)
    (unverified : call.directSourceResult = none)
    (transferred : call.transferredResultField = some field) :
    executableV54ConstructNominalMethodCall call path = none := by
  simp [executableV54ConstructNominalMethodCall,
    executableV54PrepareFreshResultTransfer, selected, unverified, transferred]

theorem executable_v54_empty_nominal_summary_class_refuses
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (summary : ExecutableV54NominalMethodSummary)
    (selected : call.summary = some summary)
    (emptyResult : summary.resultCanonicalClass.isEmpty = true) :
    executableV54ConstructNominalMethodCall call path = none := by
  unfold executableV54ConstructNominalMethodCall
  simp only [selected]
  cases prepared : executableV54PrepareFreshResultTransfer call path summary <;>
    simp [executableV54NominalMethodSummaryValid, emptyResult]

theorem executable_v54_uninitialized_constructor_call_read_refuses
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (uninitialized : executableV54ReadsInitialized path
      call.requiredInitializedFields = false) :
    executableV54ConstructNominalMethodCall call path = none := by
  cases selected : call.summary with
  | none => simp [executableV54ConstructNominalMethodCall, selected]
  | some summary =>
      unfold executableV54ConstructNominalMethodCall
      simp only [selected]
      cases prepared : executableV54PrepareFreshResultTransfer call path summary <;>
        simp [uninitialized]

theorem executable_v54_class_qualified_static_call_has_no_receiver_obligation
    (call : ExecutableV54NominalMethodCall)
    (summary : ExecutableV54NominalMethodSummary)
    (static : call.receiverKind = .static)
    (classQualified : call.receiver = none) :
    executableV54CallReceiverSupported call summary = true ∧
      executableV54CallReceiverObligations call = [] := by
  simp [executableV54CallReceiverSupported, executableV54CallReceiverObligations,
    static, classQualified, resolveClassQualifiedCall]

theorem executable_v54_constructed_effect_propagates_summary_nominal_class
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (summary : ExecutableV54NominalMethodSummary)
    (effect : ExecutableV54ConstructedNominalCall)
    (selected : call.summary = some summary)
    (constructed : executableV54ConstructNominalMethodCall call path = some effect) :
    effect.resultBinding = {
      name := call.targetName
      value := call.result
      valueType := executableV54NominalResultType summary
      exactRuntimeClassProved := false
      sourceConstructedProved := false
    } := by
  unfold executableV54ConstructNominalMethodCall at constructed
  simp only [selected] at constructed
  split at constructed <;> simp_all
  rcases constructed with ⟨_, _, _, _, _, _, _, _, effectEq⟩
  rfl

theorem executable_v54_constructed_effect_contains_exact_fresh_transfer_facts
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (summary : ExecutableV54NominalMethodSummary)
    (transfer : ExecutableV54FreshResultTransfer)
    (effect : ExecutableV54ConstructedNominalCall)
    (selected : call.summary = some summary)
    (prepared : executableV54PrepareFreshResultTransfer call path summary = some transfer)
    (constructed : executableV54ConstructNominalMethodCall call path = some effect) :
    effect.postconditionFacts = transfer.freshnessFacts ++
      (transfer.permissionFacts ++ call.postconditionFacts) := by
  simp [executableV54ConstructNominalMethodCall, selected, prepared] at constructed
  rcases constructed with ⟨_, _, _, _, _, _, _, _, effectEq⟩
  rfl

theorem executable_v54_nominal_result_clears_stale_provenance
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (effect : ExecutableV54ConstructedNominalCall)
    (constructed : executableV54ConstructNominalMethodCall call path = some effect) :
    effect.resultBinding.exactRuntimeClassProved = false ∧
      effect.resultBinding.sourceConstructedProved = false := by
  cases selected : call.summary with
  | none => simp [executableV54ConstructNominalMethodCall, selected] at constructed
  | some summary =>
      have binding := executable_v54_constructed_effect_propagates_summary_nominal_class
        call path summary effect selected constructed
      simp [binding]

theorem executable_v54_success_threads_exact_current_state
    (call : ExecutableV54NominalMethodCall) (path next : ExecutableV54MethodPath)
    (effect : ExecutableV54ConstructedNominalCall)
    (normal : path.core.status = .normal)
    (constructed : executableV54ConstructNominalMethodCall call path = some effect)
    (preconditions : call.preconditionDisposition = .proved)
    (permission : call.permissionDisposition = .proved)
    (executed : executeExecutableV54NominalMethodCall call path = some next) :
    next.core.state.heap = executableNextVersion path.core.state.heap effect.heapTransition ∧
      next.core.state.mask = executableNextVersion path.core.state.mask effect.maskTransition ∧
      next.core.state.assumptions = path.core.state.assumptions ++ effect.frameFacts ++
        effect.postconditionFacts ∧
      next.core.state.obligations = path.core.state.obligations ++ effect.obligations := by
  simp [executeExecutableV54NominalMethodCall, normal, constructed, preconditions,
    permission] at executed
  subst next
  simp [executableV54ApplyNominalMethodCall]

theorem executable_v54_success_establishes_fresh_transfer_before_postconditions
    (call : ExecutableV54NominalMethodCall) (path next : ExecutableV54MethodPath)
    (summary : ExecutableV54NominalMethodSummary)
    (transfer : ExecutableV54FreshResultTransfer)
    (effect : ExecutableV54ConstructedNominalCall)
    (normal : path.core.status = .normal)
    (selected : call.summary = some summary)
    (prepared : executableV54PrepareFreshResultTransfer call path summary = some transfer)
    (constructed : executableV54ConstructNominalMethodCall call path = some effect)
    (preconditions : call.preconditionDisposition = .proved)
    (permission : call.permissionDisposition = .proved)
    (executed : executeExecutableV54NominalMethodCall call path = some next) :
    next.core.state.assumptions = path.core.state.assumptions ++ effect.frameFacts ++
      transfer.freshnessFacts ++ transfer.permissionFacts ++ call.postconditionFacts := by
  have threaded := executable_v54_success_threads_exact_current_state
    call path next effect normal constructed preconditions permission executed
  have exactFacts := executable_v54_constructed_effect_contains_exact_fresh_transfer_facts
    call path summary transfer effect selected prepared constructed
  rw [exactFacts] at threaded
  simpa [List.append_assoc] using threaded.2.2.1

theorem executable_v54_success_replaces_stale_target_binding
    (call : ExecutableV54NominalMethodCall) (path next : ExecutableV54MethodPath)
    (effect : ExecutableV54ConstructedNominalCall)
    (normal : path.core.status = .normal)
    (constructed : executableV54ConstructNominalMethodCall call path = some effect)
    (preconditions : call.preconditionDisposition = .proved)
    (permission : call.permissionDisposition = .proved)
    (executed : executeExecutableV54NominalMethodCall call path = some next) :
    executableLookupLocal next.core.state.environment call.targetName =
      some effect.resultBinding := by
  have targetName : effect.resultBinding.name = call.targetName := by
    cases selected : call.summary with
    | none => simp [executableV54ConstructNominalMethodCall, selected] at constructed
    | some summary =>
        have binding := executable_v54_constructed_effect_propagates_summary_nominal_class
          call path summary effect selected constructed
        simp [binding]
  simp [executeExecutableV54NominalMethodCall, normal, constructed, preconditions,
    permission] at executed
  subst next
  simp [executableV54ApplyNominalMethodCall, executableBindLocal,
    executableLookupLocal, targetName]

theorem executable_v54_success_target_has_summary_nominal_class
    (call : ExecutableV54NominalMethodCall) (path next : ExecutableV54MethodPath)
    (summary : ExecutableV54NominalMethodSummary)
    (effect : ExecutableV54ConstructedNominalCall)
    (normal : path.core.status = .normal)
    (selected : call.summary = some summary)
    (constructed : executableV54ConstructNominalMethodCall call path = some effect)
    (preconditions : call.preconditionDisposition = .proved)
    (permission : call.permissionDisposition = .proved)
    (executed : executeExecutableV54NominalMethodCall call path = some next) :
    executableLookupLocal next.core.state.environment call.targetName = some {
      name := call.targetName
      value := call.result
      valueType := executableV54NominalResultType summary
      exactRuntimeClassProved := false
      sourceConstructedProved := false
    } := by
  have resultBinding := executable_v54_constructed_effect_propagates_summary_nominal_class
    call path summary effect selected constructed
  have replaced : executableLookupLocal next.core.state.environment call.targetName =
      some effect.resultBinding := by
    exact executable_v54_success_replaces_stale_target_binding call path next effect normal
      constructed preconditions permission executed
  simpa [resultBinding] using replaced

theorem executable_v54_permission_failure_halts_before_nominal_assignment
    (call : ExecutableV54NominalMethodCall) (path : ExecutableV54MethodPath)
    (effect : ExecutableV54ConstructedNominalCall) (failed : Term)
    (normal : path.core.status = .normal)
    (constructed : executableV54ConstructNominalMethodCall call path = some effect)
    (preconditions : call.preconditionDisposition = .proved)
    (permission : call.permissionDisposition = .refuted failed) :
    executeExecutableV54NominalMethodCall call path = some { path with core :=
      (executableHaltPath path.core (executableV54CallObligations call) failed) } := by
  simp [executeExecutableV54NominalMethodCall, normal, constructed, preconditions, permission]

theorem executable_v54_native_assertion_uses_current_heap_and_mask
    (assertion : ExecutableV54NativeAssertion) (path : ExecutableV54MethodPath)
    (normal : path.core.status = .normal)
    (initialized : executableV54ReadsInitialized path
      assertion.requiredInitializedFields = true)
    (typed : executableTermsAreBoolean
      (executableV54NativeAssertionObligations assertion path) = true)
    (proved : assertion.disposition = .proved) :
    executeExecutableV54NativeAssertion assertion path = some { path with core := ({
      path.core with state := { path.core.state with obligations := (
        path.core.state.obligations ++
          assertion.obligations path.core.state.heap path.core.state.mask ++
          [assertion.condition path.core.state.heap path.core.state.mask]) } } :
            ExecutableHeapPath) } := by
  have instantiatedTyped : executableTermsAreBoolean
      (assertion.obligations path.core.state.heap path.core.state.mask ++
        [assertion.condition path.core.state.heap path.core.state.mask]) = true := by
    simpa [executableV54NativeAssertionObligations] using typed
  simp [executeExecutableV54NativeAssertion, executableV54NativeAssertionObligations,
    normal, initialized, instantiatedTyped, proved, List.append_assoc]

theorem executable_v54_native_assertion_refutation_records_obligations
    (assertion : ExecutableV54NativeAssertion) (path : ExecutableV54MethodPath)
    (failed : Term)
    (normal : path.core.status = .normal)
    (initialized : executableV54ReadsInitialized path
      assertion.requiredInitializedFields = true)
    (typed : executableTermsAreBoolean
      (executableV54NativeAssertionObligations assertion path) = true)
    (refuted : assertion.disposition = .refuted failed) :
    executeExecutableV54NativeAssertion assertion path = some { path with core :=
      (executableHaltPath path.core
        (executableV54NativeAssertionObligations assertion path) failed) } := by
  simp [executeExecutableV54NativeAssertion, normal, initialized, typed, refuted]

theorem executable_v54_uninitialized_constructor_assertion_read_refuses
    (assertion : ExecutableV54NativeAssertion) (path : ExecutableV54MethodPath)
    (normal : path.core.status = .normal)
    (uninitialized : executableV54ReadsInitialized path
      assertion.requiredInitializedFields = false) :
    executeExecutableV54NativeAssertion assertion path = none := by
  simp [executeExecutableV54NativeAssertion, normal, uninitialized]

theorem executable_v54_halted_path_absorbs_later_statement
    (statement : ExecutableV54OrdinaryMethodStmt)
    (path : ExecutableV54MethodPath) (failed : Term)
    (halted : path.core.status = .halted failed) :
    executeExecutableV54OrdinaryMethodStmt statement path = some path := by
  cases statement <;>
    simp [executeExecutableV54OrdinaryMethodStmt,
      executeExecutableV54NominalMethodCall, executeExecutableV54NativeAssertion, halted]

end Maledictus
