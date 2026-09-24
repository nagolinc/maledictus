import BindCallFullProofs.LoopSpecs

open Aeneas Aeneas.Std Result

namespace BindCallFull.Proofs


def addParameterCountReference
    (accumulated contribution : Std.Usize) :
    core.result.Result Std.Usize (BindCallFull.BindingError String) :=
  match Std.Usize.checked_add accumulated contribution with
  | none => .Err (.MalformedSignature
      (.ParameterCountOverflow accumulated contribution))
  | some count => .Ok count

def signatureCountsReference
    (signature : BindCallFull.CallSignature String Int) :
    core.result.Result BindCallFull.SignatureCounts
      (BindCallFull.BindingError String) :=
  let positionalOnly := alloc.vec.Vec.len signature.positional_only
  let positional := alloc.vec.Vec.len signature.positional
  match addParameterCountReference positionalOnly positional with
  | .Err error => .Err error
  | .Ok positionalCount =>
      match addParameterCountReference positionalCount
          (alloc.vec.Vec.len signature.keyword_only) with
      | .Err error => .Err error
      | .Ok ordinaryCount =>
          match addParameterCountReference ordinaryCount
              (core.convert.num.FromUsizeBool.from signature.var_args.isSome) with
          | .Err error => .Err error
          | .Ok withVarargs =>
              match addParameterCountReference withVarargs
                  (core.convert.num.FromUsizeBool.from
                    signature.keyword_args.isSome) with
              | .Err error => .Err error
              | .Ok parameterCount => .Ok {
                  parameter_count := parameterCount
                  positional_count := positionalCount
                }

theorem add_parameter_count_matches_reference
    (accumulated contribution : Std.Usize) :
    WP.spec (BindCallFull.add_parameter_count String accumulated contribution)
      (fun output => output =
        addParameterCountReference accumulated contribution) := by
  unfold BindCallFull.add_parameter_count addParameterCountReference
  simp only [Aeneas.Std.lift]
  split <;> rename_i checkedEq <;>
    simp [checkedEq, WP.spec, WP.theta, WP.wp_return]

theorem signature_counts_matches_reference
    (signature : BindCallFull.CallSignature String Int) :
    WP.spec (BindCallFull.signature_counts signature)
      (fun output => output = signatureCountsReference signature) := by
  unfold BindCallFull.signature_counts signatureCountsReference
  simp only [BindCallFull.add_parameter_count, Aeneas.Std.lift]
  repeat' first
  | split
  | simp_all [addParameterCountReference,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    WP.spec, WP.theta, WP.wp_return]

def AllocatorContract {Allocator : Type}
    (allocatorInst : BindCallFull.BindingAllocator Allocator) : Prop :=
  ∀ (T : Type) (allocator : Allocator) (site : BindCallFull.AllocationSite)
      (requested : Std.Usize),
    WP.spec (allocatorInst.allocate (T := T) allocator site requested)
      (fun output =>
        match output.1 with
        | .Ok values => values.val = []
        | .Err _ => True)

inductive AllocationStepReference {T Allocator : Type}
    (site : BindCallFull.AllocationSite) (requested : Std.Usize) :
    core.result.Result (alloc.vec.Vec T) (BindCallFull.BindingError String) →
      Allocator → Prop where
  | allocated (values : alloc.vec.Vec T) (allocator : Allocator)
      (empty : values.val = []) :
      AllocationStepReference site requested (.Ok values) allocator
  | failed (allocator : Allocator) :
      AllocationStepReference site requested
        (.Err (.AllocationFailed site requested)) allocator

theorem allocate_buffer_matches_reference
    {Allocator T : Type}
    (allocatorInst : BindCallFull.BindingAllocator Allocator)
    (allocatorLaw : AllocatorContract allocatorInst)
    (allocator : Allocator) (site : BindCallFull.AllocationSite)
    (requested : Std.Usize) :
    WP.spec
      (BindCallFull.allocate_buffer String T allocatorInst allocator site requested)
      (fun output => AllocationStepReference site requested output.1 output.2) := by
  unfold BindCallFull.allocate_buffer
  apply WP.spec_bind (allocatorLaw T allocator site requested)
  intro output outputPost
  rcases output with ⟨allocationResult, allocatorAfter⟩
  cases allocationResult with
  | Ok values =>
      simp [WP.spec, WP.theta, WP.wp_return]
      exact AllocationStepReference.allocated values allocatorAfter outputPost
  | Err unitValue =>
      simp [WP.spec, WP.theta, WP.wp_return]
      exact AllocationStepReference.failed allocatorAfter

def validateVariadicsReference
    (signature : BindCallFull.CallSignature String Int)
    (names : List String) :
    core.result.Result Unit (BindCallFull.BindingError String) :=
  match signature.var_args with
  | none =>
      match signature.keyword_args with
      | none => .Ok ()
      | some keywordArgs =>
          (validateFormalReference keywordArgs true names).1
  | some varArgs =>
      let varOutput := validateFormalReference varArgs true names
      match varOutput.1 with
      | .Err error => .Err error
      | .Ok _ =>
          match signature.keyword_args with
          | none => .Ok ()
          | some keywordArgs =>
              (validateFormalReference keywordArgs true varOutput.2).1

def validateSignatureBodyReference
    (signature : BindCallFull.CallSignature String Int)
    (counts : BindCallFull.SignatureCounts) :
    core.result.Result BindCallFull.SignatureCounts
      (BindCallFull.BindingError String) :=
  let positionalOnly := validateFormalListReference
    signature.positional_only.val [] none
  match positionalOnly.2 with
  | some error => .Err error
  | none =>
      let positional := validateFormalListReference
        signature.positional.val positionalOnly.1 none
      match positional.2 with
      | some error => .Err error
      | none =>
          let keywordOnly := validateFormalListReference
            signature.keyword_only.val positional.1 none
          match keywordOnly.2 with
          | some error => .Err error
          | none =>
              match validateVariadicsReference signature keywordOnly.1 with
              | .Err error => .Err error
              | .Ok _ => .Ok counts

def AllocatorTransitionReference {Allocator T : Type}
    (_allocatorInst : BindCallFull.BindingAllocator Allocator)
    (_before : Allocator) (_site : BindCallFull.AllocationSite)
    (requested : Std.Usize)
    (result : core.result.Result (alloc.vec.Vec T) Unit)
    (_after : Allocator) : Prop :=
  match result with
  | .Ok values => values.val = []
  | .Err _ => True

inductive ValidateSignatureReference {Allocator : Type}
    (allocatorInst : BindCallFull.BindingAllocator Allocator)
    (signature : BindCallFull.CallSignature String Int) (initial : Allocator) :
    core.result.Result BindCallFull.SignatureCounts
      (BindCallFull.BindingError String) → Allocator → Prop where
  | countError (error : BindCallFull.BindingError String)
      (countReference : signatureCountsReference signature = .Err error) :
      ValidateSignatureReference allocatorInst signature initial (.Err error) initial
  | allocationFailed (counts : BindCallFull.SignatureCounts)
      (allocator : Allocator)
      (countReference : signatureCountsReference signature = .Ok counts) :
      AllocatorTransitionReference allocatorInst initial .SignatureNames
        counts.parameter_count
          ((.Err ()) : core.result.Result (alloc.vec.Vec String) Unit) allocator →
      ValidateSignatureReference allocatorInst signature initial
        (.Err (.AllocationFailed .SignatureNames counts.parameter_count)) allocator
  | validated (counts : BindCallFull.SignatureCounts)
      (values : alloc.vec.Vec String) (allocator : Allocator)
      (result : core.result.Result BindCallFull.SignatureCounts
        (BindCallFull.BindingError String))
      (countReference : signatureCountsReference signature = .Ok counts)
      (bodyReference : validateSignatureBodyReference signature counts = result)
      (transition : AllocatorTransitionReference allocatorInst initial
        .SignatureNames counts.parameter_count (.Ok values) allocator) :
      ValidateSignatureReference allocatorInst signature initial
        result allocator

theorem signatureCountsReference_success_facts
    (signature : BindCallFull.CallSignature String Int)
    (counts : BindCallFull.SignatureCounts)
    (success : signatureCountsReference signature = .Ok counts) :
    counts.positional_count.val =
        signature.positional_only.val.length + signature.positional.val.length ∧
      counts.parameter_count.val =
        signature.positional_only.val.length + signature.positional.val.length +
          signature.keyword_only.val.length +
          (core.convert.num.FromUsizeBool.from signature.var_args.isSome).val +
          (core.convert.num.FromUsizeBool.from
            signature.keyword_args.isSome).val ∧
      counts.parameter_count.val ≤ Std.Usize.max := by
  unfold signatureCountsReference addParameterCountReference at success
  dsimp only at success
  generalize firstEq : Std.Usize.checked_add
    (alloc.vec.Vec.len signature.positional_only)
    (alloc.vec.Vec.len signature.positional) = first at success
  cases first with
  | none => simp [firstEq] at success
  | some positionalCount =>
      generalize secondEq : Std.Usize.checked_add positionalCount
        (alloc.vec.Vec.len signature.keyword_only) = second at success
      cases second with
      | none => simp [firstEq, secondEq] at success
      | some ordinaryCount =>
          generalize thirdEq : Std.Usize.checked_add ordinaryCount
            (core.convert.num.FromUsizeBool.from signature.var_args.isSome) =
              third at success
          cases third with
          | none => simp [firstEq, secondEq, thirdEq] at success
          | some withVarargs =>
              generalize fourthEq : Std.Usize.checked_add withVarargs
                (core.convert.num.FromUsizeBool.from
                  signature.keyword_args.isSome) = fourth at success
              cases fourth with
              | none => simp [firstEq, secondEq, thirdEq, fourthEq] at success
              | some parameterCount =>
                  have firstSpec := Std.Usize.checked_add_bv_spec
                    (alloc.vec.Vec.len signature.positional_only)
                    (alloc.vec.Vec.len signature.positional)
                  rw [firstEq] at firstSpec
                  have secondSpec := Std.Usize.checked_add_bv_spec positionalCount
                    (alloc.vec.Vec.len signature.keyword_only)
                  rw [secondEq] at secondSpec
                  have thirdSpec := Std.Usize.checked_add_bv_spec ordinaryCount
                    (core.convert.num.FromUsizeBool.from
                      signature.var_args.isSome)
                  rw [thirdEq] at thirdSpec
                  have fourthSpec := Std.Usize.checked_add_bv_spec withVarargs
                    (core.convert.num.FromUsizeBool.from
                      signature.keyword_args.isSome)
                  rw [fourthEq] at fourthSpec
                  have countsResultEq :
                      (core.result.Result.Ok ({
                        parameter_count := parameterCount
                        positional_count := positionalCount
                      } : BindCallFull.SignatureCounts) :
                        core.result.Result BindCallFull.SignatureCounts
                          (BindCallFull.BindingError String)) = .Ok counts := by
                    simpa [firstEq, secondEq, thirdEq, fourthEq] using success
                  injection countsResultEq with countsEq
                  subst counts
                  simp [alloc.vec.Vec.len, alloc.vec.Vec.length] at firstSpec secondSpec thirdSpec fourthSpec ⊢
                  omega

set_option maxRecDepth 10000 in
theorem validate_signature_matches_reference
    {Allocator : Type}
    (allocatorInst : BindCallFull.BindingAllocator Allocator)
    (allocatorLaw : AllocatorContract allocatorInst)
    (signature : BindCallFull.CallSignature String Int)
    (allocator : Allocator) :
    WP.spec
      (BindCallFull.validate_signature (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        allocatorInst signature () allocator)
      (fun output => ValidateSignatureReference allocatorInst signature allocator
        output.1 output.2) := by
  unfold BindCallFull.validate_signature
  step with signature_counts_matches_reference as ⟨countResult, countEq⟩
  cases countResult with
  | Err countError =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      simp [WP.spec, WP.theta, WP.wp_return,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      exact ValidateSignatureReference.countError countError countEq.symm
  | Ok counts =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      have countReference : signatureCountsReference signature = .Ok counts :=
        countEq.symm
      have countFacts := signatureCountsReference_success_facts signature counts
        countReference
      step with allocate_buffer_matches_reference allocatorInst allocatorLaw as
        ⟨allocationResult, allocatorAfter, allocationPost⟩
      cases allocationResult with
      | Err allocationError =>
          cases allocationPost
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            WP.spec, WP.theta, WP.wp_return]
          exact ValidateSignatureReference.allocationFailed counts allocatorAfter
            countReference (by simp [AllocatorTransitionReference])
      | Ok names =>
          cases allocationPost with
          | allocated _ _ namesEmpty =>
            have validatedReference : ValidateSignatureReference allocatorInst
                signature allocator (validateSignatureBodyReference signature counts)
                allocatorAfter :=
              @ValidateSignatureReference.validated Allocator allocatorInst
                signature allocator counts names allocatorAfter
                (validateSignatureBodyReference signature counts) countReference
                rfl (by simpa [AllocatorTransitionReference] using namesEmpty)
            have loop0Bound :
                names.val.length +
                    validationLoopRemaining signature.positional_only 0#usize ≤
                  Std.Usize.max := by
              unfold validationLoopRemaining
              simp [namesEmpty]
              have vectorBound := signature.positional_only.property
              omega
            have loop0Spec := validate_signature_loop0_matches_reference
              signature.positional_only names 0#usize none (by simp) loop0Bound
            step with loop0Spec as
              ⟨namesAfterPositionalOnly, positionalOnlyError,
                positionalOnlyPost⟩
            have positionalOnlyNamesEq : namesAfterPositionalOnly.val =
                (validateFormalListReference signature.positional_only.val [] none).1 := by
              simpa [validationOutputView, namesEmpty] using
                congrArg Prod.fst positionalOnlyPost
            have positionalOnlyErrorEq : positionalOnlyError =
                (validateFormalListReference signature.positional_only.val [] none).2 := by
              simpa [validationOutputView, namesEmpty] using
                congrArg Prod.snd positionalOnlyPost
            cases hPositionalOnlyError : positionalOnlyError with
            | some error =>
                have bodyEq : validateSignatureBodyReference signature counts =
                    .Err error := by
                  unfold validateSignatureBodyReference
                  dsimp only
                  have referenceError :
                      (validateFormalListReference
                        signature.positional_only.val [] none).2 = some error :=
                    positionalOnlyErrorEq.symm.trans hPositionalOnlyError
                  rw [referenceError]
                simp [hPositionalOnlyError, positionalOnlyErrorEq,
                  validateSignatureBodyReference, WP.spec, WP.theta, WP.wp_return]
                simpa [bodyEq] using validatedReference
            | none =>
                simp only
                have loop1Bound :
                    namesAfterPositionalOnly.val.length +
                        validationLoopRemaining signature.positional 0#usize ≤
                      Std.Usize.max := by
                  unfold validationLoopRemaining
                  change namesAfterPositionalOnly.val.length +
                    signature.positional.val.length ≤ Std.Usize.max
                  have namesBound := validateFormalListReference_names_length
                    signature.positional_only.val [] none
                  simp at namesBound
                  rw [positionalOnlyNamesEq]
                  omega
                have loop1Spec := validate_signature_loop1_matches_reference
                  signature.positional namesAfterPositionalOnly 0#usize none
                  (by simp) loop1Bound
                step with loop1Spec as
                  ⟨namesAfterPositional, positionalError, positionalPost⟩
                have positionalNamesEq : namesAfterPositional.val =
                    (validateFormalListReference signature.positional.val
                      namesAfterPositionalOnly.val none).1 :=
                  by simpa [validationOutputView] using
                    congrArg Prod.fst positionalPost
                have positionalErrorEq : positionalError =
                    (validateFormalListReference signature.positional.val
                      namesAfterPositionalOnly.val none).2 :=
                  by simpa [validationOutputView] using
                    congrArg Prod.snd positionalPost
                cases hPositionalError : positionalError with
                | some error =>
                    have positionalOnlyReferenceNone :
                        (validateFormalListReference signature.positional_only.val
                          [] none).2 = none :=
                      positionalOnlyErrorEq.symm.trans hPositionalOnlyError
                    have positionalReferenceError :
                        (validateFormalListReference signature.positional.val
                          namesAfterPositionalOnly.val none).2 = some error :=
                      positionalErrorEq.symm.trans hPositionalError
                    simp [hPositionalOnlyError, hPositionalError,
                      positionalOnlyErrorEq, positionalErrorEq,
                      validateSignatureBodyReference, WP.spec, WP.theta,
                      WP.wp_return]
                    simpa [validateSignatureBodyReference,
                      positionalOnlyReferenceNone, positionalReferenceError,
                      ← positionalOnlyNamesEq] using validatedReference
                | none =>
                    simp only
                    have loop2Bound :
                        namesAfterPositional.val.length +
                            validationLoopRemaining signature.keyword_only
                              0#usize ≤ Std.Usize.max := by
                      unfold validationLoopRemaining
                      change namesAfterPositional.val.length +
                        signature.keyword_only.val.length ≤ Std.Usize.max
                      have positionalOnlyNamesBound :=
                        validateFormalListReference_names_length
                          signature.positional_only.val [] none
                      simp at positionalOnlyNamesBound
                      have positionalNamesBound :=
                        validateFormalListReference_names_length
                          signature.positional.val
                          namesAfterPositionalOnly.val none
                      rw [positionalNamesEq]
                      have positionalOnlyLengthEq :=
                        congrArg List.length positionalOnlyNamesEq
                      have totalCountEq := countFacts.2.1
                      have totalCountBound := countFacts.2.2
                      omega
                    have loop2Spec := validate_signature_loop2_matches_reference
                      signature.keyword_only namesAfterPositional 0#usize none
                      (by simp) loop2Bound
                    step with loop2Spec as
                      ⟨namesAfterKeywordOnly, keywordOnlyError,
                        keywordOnlyPost⟩
                    have keywordOnlyNamesEq : namesAfterKeywordOnly.val =
                        (validateFormalListReference signature.keyword_only.val
                          namesAfterPositional.val none).1 :=
                      congrArg Prod.fst keywordOnlyPost
                    have keywordOnlyErrorEq : keywordOnlyError =
                        (validateFormalListReference signature.keyword_only.val
                          namesAfterPositional.val none).2 :=
                      congrArg Prod.snd keywordOnlyPost
                    cases hKeywordOnlyError : keywordOnlyError with
                    | some error =>
                        have positionalOnlyReferenceNone :
                            (validateFormalListReference
                              signature.positional_only.val [] none).2 = none :=
                          positionalOnlyErrorEq.symm.trans hPositionalOnlyError
                        have positionalReferenceNone :
                            (validateFormalListReference signature.positional.val
                              namesAfterPositionalOnly.val none).2 = none :=
                          positionalErrorEq.symm.trans hPositionalError
                        have keywordOnlyReferenceError :
                            (validateFormalListReference
                              signature.keyword_only.val
                              namesAfterPositional.val none).2 = some error :=
                          keywordOnlyErrorEq.symm.trans hKeywordOnlyError
                        simp [hPositionalOnlyError, hPositionalError,
                          hKeywordOnlyError, positionalOnlyErrorEq,
                          positionalErrorEq, keywordOnlyErrorEq,
                          validateSignatureBodyReference, WP.spec, WP.theta,
                          WP.wp_return]
                        simpa [validateSignatureBodyReference,
                          positionalOnlyReferenceNone,
                          positionalReferenceNone,
                          keywordOnlyReferenceError, ← positionalOnlyNamesEq,
                          ← positionalNamesEq] using validatedReference
                    | none =>
                        have positionalOnlyReferenceNone :
                            (validateFormalListReference
                              signature.positional_only.val [] none).2 = none :=
                          positionalOnlyErrorEq.symm.trans hPositionalOnlyError
                        have positionalReferenceNone :
                            (validateFormalListReference signature.positional.val
                              namesAfterPositionalOnly.val none).2 = none :=
                          positionalErrorEq.symm.trans hPositionalError
                        have keywordOnlyReferenceNone :
                            (validateFormalListReference
                              signature.keyword_only.val
                              namesAfterPositional.val none).2 = none :=
                          keywordOnlyErrorEq.symm.trans hKeywordOnlyError
                        have positionalOnlyNamesBound :=
                          validateFormalListReference_names_length
                            signature.positional_only.val [] none
                        simp at positionalOnlyNamesBound
                        have positionalNamesBound :=
                          validateFormalListReference_names_length
                            signature.positional.val
                            namesAfterPositionalOnly.val none
                        have keywordOnlyNamesBound :=
                          validateFormalListReference_names_length
                            signature.keyword_only.val
                            namesAfterPositional.val none
                        have keywordOnlyOutputBound :
                            namesAfterKeywordOnly.val.length ≤
                              signature.positional_only.val.length +
                                signature.positional.val.length +
                                  signature.keyword_only.val.length := by
                          rw [keywordOnlyNamesEq]
                          have positionalOnlyLengthEq :=
                            congrArg List.length positionalOnlyNamesEq
                          have positionalLengthEq :=
                            congrArg List.length positionalNamesEq
                          omega
                        cases hVarargs : signature.var_args with
                        | none =>
                            cases hKeywordArgs : signature.keyword_args with
                            | none =>
                                simp [hVarargs, hKeywordArgs,
                                  hPositionalOnlyError, hPositionalError,
                                  hKeywordOnlyError, positionalOnlyErrorEq,
                                  positionalErrorEq, keywordOnlyErrorEq,
                                  validateSignatureBodyReference,
                                  validateVariadicsReference, WP.spec,
                                  WP.theta, WP.wp_return]
                                simpa [validateSignatureBodyReference,
                                  validateVariadicsReference, hVarargs,
                                  hKeywordArgs, positionalOnlyReferenceNone,
                                  positionalReferenceNone,
                                  keywordOnlyReferenceNone,
                                  ← positionalOnlyNamesEq, ← positionalNamesEq,
                                  ← keywordOnlyNamesEq] using validatedReference
                            | some keywordParameter =>
                                have keywordCapacity :
                                    namesAfterKeywordOnly.val.length <
                                      Std.Usize.max := by
                                  have totalBound := countFacts.2.2
                                  simp [hVarargs, hKeywordArgs,
                                    core.convert.num.FromUsizeBool.from] at countFacts
                                  omega
                                apply WP.spec_bind
                                  (validate_formal_parameter_string_exact
                                    keywordParameter true namesAfterKeywordOnly
                                    keywordCapacity)
                                intro keywordOutput keywordEq
                                rcases keywordOutput with
                                  ⟨keywordResult, namesAfterKeyword⟩
                                have keywordResultEq : keywordResult =
                                    (validateFormalReference keywordParameter
                                      true namesAfterKeywordOnly.val).1 :=
                                  congrArg Prod.fst keywordEq
                                cases hKeywordReference :
                                    (validateFormalReference keywordParameter
                                      true namesAfterKeywordOnly.val).1 with
                                | Ok value =>
                                    have keywordOk : keywordResult = .Ok value := by
                                      rw [keywordResultEq, hKeywordReference]
                                    simp [keywordOk, hKeywordReference,
                                      hVarargs, hKeywordArgs,
                                      hPositionalOnlyError, hPositionalError,
                                      hKeywordOnlyError, positionalOnlyErrorEq,
                                      positionalErrorEq, keywordOnlyErrorEq,
                                      validateSignatureBodyReference,
                                      validateVariadicsReference,
                                      core.result.Result.Insts.CoreOpsTry.branch,
                                      WP.spec, WP.theta, WP.wp_return]
                                    simpa [validateSignatureBodyReference,
                                      validateVariadicsReference, hVarargs,
                                      hKeywordArgs, hKeywordReference,
                                      positionalOnlyReferenceNone,
                                      positionalReferenceNone,
                                      keywordOnlyReferenceNone,
                                      ← positionalOnlyNamesEq, ← positionalNamesEq,
                                      ← keywordOnlyNamesEq]
                                      using validatedReference
                                | Err error =>
                                    have keywordErr : keywordResult = .Err error := by
                                      rw [keywordResultEq, hKeywordReference]
                                    simp [keywordErr, hKeywordReference,
                                      hVarargs, hKeywordArgs,
                                      hPositionalOnlyError, hPositionalError,
                                      hKeywordOnlyError, positionalOnlyErrorEq,
                                      positionalErrorEq, keywordOnlyErrorEq,
                                      validateSignatureBodyReference,
                                      validateVariadicsReference,
                                      core.result.Result.Insts.CoreOpsTry.branch,
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                      WP.spec, WP.theta, WP.wp_return]
                                    simpa [validateSignatureBodyReference,
                                      validateVariadicsReference, hVarargs,
                                      hKeywordArgs, hKeywordReference,
                                      positionalOnlyReferenceNone,
                                      positionalReferenceNone,
                                      keywordOnlyReferenceNone,
                                      ← positionalOnlyNamesEq, ← positionalNamesEq,
                                      ← keywordOnlyNamesEq]
                                      using validatedReference
                        | some varParameter =>
                            have varCapacity :
                                namesAfterKeywordOnly.val.length <
                                  Std.Usize.max := by
                              simp [hVarargs,
                                core.convert.num.FromUsizeBool.from] at countFacts
                              omega
                            apply WP.spec_bind
                              (validate_formal_parameter_string_exact
                                varParameter true namesAfterKeywordOnly
                                varCapacity)
                            intro varOutput varEq
                            rcases varOutput with ⟨varResult, namesAfterVar⟩
                            have varResultEq : varResult =
                                (validateFormalReference varParameter true
                                  namesAfterKeywordOnly.val).1 :=
                              congrArg Prod.fst varEq
                            have varNamesEq : namesAfterVar.val =
                                (validateFormalReference varParameter true
                                  namesAfterKeywordOnly.val).2 :=
                              congrArg Prod.snd varEq
                            cases hVarReference :
                                (validateFormalReference varParameter true
                                  namesAfterKeywordOnly.val).1 with
                            | Err error =>
                                have varErr : varResult = .Err error := by
                                  rw [varResultEq, hVarReference]
                                simp [varErr, hVarReference, hVarargs,
                                  hPositionalOnlyError, hPositionalError,
                                  hKeywordOnlyError, positionalOnlyErrorEq,
                                  positionalErrorEq, keywordOnlyErrorEq,
                                  validateSignatureBodyReference,
                                  validateVariadicsReference,
                                  core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  WP.spec, WP.theta, WP.wp_return]
                                simpa [validateSignatureBodyReference,
                                  validateVariadicsReference, hVarargs,
                                  hVarReference, positionalOnlyReferenceNone,
                                  positionalReferenceNone,
                                  keywordOnlyReferenceNone,
                                  ← positionalOnlyNamesEq, ← positionalNamesEq,
                                  ← keywordOnlyNamesEq] using validatedReference
                            | Ok value =>
                                have varOk : varResult = .Ok value := by
                                  rw [varResultEq, hVarReference]
                                simp only [varOk,
                                  core.result.Result.Insts.CoreOpsTry.branch]
                                cases hKeywordArgs : signature.keyword_args with
                                | none =>
                                    simp [hVarReference, hVarargs, hKeywordArgs,
                                      hPositionalOnlyError, hPositionalError,
                                      hKeywordOnlyError, positionalOnlyErrorEq,
                                      positionalErrorEq, keywordOnlyErrorEq,
                                      validateSignatureBodyReference,
                                      validateVariadicsReference, WP.spec,
                                      WP.theta, WP.wp_return]
                                    simpa [validateSignatureBodyReference,
                                      validateVariadicsReference, hVarargs,
                                      hKeywordArgs, hVarReference,
                                      positionalOnlyReferenceNone,
                                      positionalReferenceNone,
                                      keywordOnlyReferenceNone,
                                      ← positionalOnlyNamesEq, ← positionalNamesEq,
                                      ← keywordOnlyNamesEq]
                                      using validatedReference
                                | some keywordParameter =>
                                    have varNamesBound :=
                                      validateFormalReference_names_length
                                        varParameter true
                                        namesAfterKeywordOnly.val
                                    have keywordCapacity :
                                        namesAfterVar.val.length <
                                          Std.Usize.max := by
                                      simp [hVarargs, hKeywordArgs,
                                        core.convert.num.FromUsizeBool.from] at countFacts
                                      rw [varNamesEq]
                                      omega
                                    apply WP.spec_bind
                                      (validate_formal_parameter_string_exact
                                        keywordParameter true namesAfterVar
                                        keywordCapacity)
                                    intro keywordOutput keywordEq
                                    rcases keywordOutput with
                                      ⟨keywordResult, finalNames⟩
                                    have keywordResultEq : keywordResult =
                                        (validateFormalReference
                                          keywordParameter true
                                          namesAfterVar.val).1 :=
                                      congrArg Prod.fst keywordEq
                                    cases hKeywordReference :
                                        (validateFormalReference
                                          keywordParameter true
                                          namesAfterVar.val).1 with
                                    | Ok keywordValue =>
                                        have keywordOk : keywordResult =
                                            .Ok keywordValue := by
                                          rw [keywordResultEq,
                                            hKeywordReference]
                                        simp [keywordOk, hKeywordReference,
                                          hVarReference, hVarargs, hKeywordArgs,
                                          hPositionalOnlyError,
                                          hPositionalError, hKeywordOnlyError,
                                          positionalOnlyErrorEq,
                                          positionalErrorEq,
                                          keywordOnlyErrorEq,
                                          validateSignatureBodyReference,
                                          validateVariadicsReference,
                                          core.result.Result.Insts.CoreOpsTry.branch,
                                          WP.spec, WP.theta, WP.wp_return]
                                        simpa [validateSignatureBodyReference,
                                          validateVariadicsReference, hVarargs,
                                          hKeywordArgs, hVarReference,
                                          hKeywordReference,
                                          ← varNamesEq,
                                          positionalOnlyReferenceNone,
                                          positionalReferenceNone,
                                          keywordOnlyReferenceNone,
                                          ← positionalOnlyNamesEq,
                                          ← positionalNamesEq,
                                          ← keywordOnlyNamesEq] using
                                            validatedReference
                                    | Err keywordError =>
                                        have keywordErr : keywordResult =
                                            .Err keywordError := by
                                          rw [keywordResultEq,
                                            hKeywordReference]
                                        simp [keywordErr, hKeywordReference,
                                          hVarReference, hVarargs, hKeywordArgs,
                                          hPositionalOnlyError,
                                          hPositionalError, hKeywordOnlyError,
                                          positionalOnlyErrorEq,
                                          positionalErrorEq,
                                          keywordOnlyErrorEq,
                                          validateSignatureBodyReference,
                                          validateVariadicsReference,
                                          core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          WP.spec, WP.theta, WP.wp_return]
                                        simpa [validateSignatureBodyReference,
                                          validateVariadicsReference, hVarargs,
                                          hKeywordArgs, hVarReference,
                                          hKeywordReference,
                                          ← varNamesEq,
                                          positionalOnlyReferenceNone,
                                          positionalReferenceNone,
                                          keywordOnlyReferenceNone,
                                          ← positionalOnlyNamesEq,
                                          ← positionalNamesEq,
                                          ← keywordOnlyNamesEq] using
                                            validatedReference

inductive PreflightErrorView where
  | sourceExpressionCountOverflow (itemCount receiverCount : Nat)
  | expandedArgumentCountOverflow
      (itemIndex accumulated contribution : Nat)
  | dynamicStarUnsupported (itemIndex : Nat)
  | keywordMappingUnsupported (itemIndex : Nat)
  | other (error : BindCallFull.BindingError String)

def preflightErrorView
    (error : BindCallFull.BindingError String) : PreflightErrorView :=
  match error with
  | .SourceExpressionCountOverflow itemCount receiverCount =>
      .sourceExpressionCountOverflow itemCount.val receiverCount.val
  | .ExpandedArgumentCountOverflow itemIndex accumulated contribution =>
      .expandedArgumentCountOverflow itemIndex.val accumulated.val
        contribution.val
  | .DynamicStarUnsupported itemIndex =>
      .dynamicStarUnsupported itemIndex.val
  | .KeywordMappingUnsupported itemIndex =>
      .keywordMappingUnsupported itemIndex.val
  | error => .other error

def preflightReferenceFrom :
    Nat → Std.Usize → Option PreflightErrorView →
      List (BindCallFull.ActualItem String Int) →
        Std.Usize × Option PreflightErrorView
  | _, expandedCount, some error, _ => (expandedCount, some error)
  | _, expandedCount, none, [] => (expandedCount, none)
  | itemIndex, expandedCount, none, item :: remaining =>
      match item with
      | .DynamicStar =>
          (expandedCount, some (.dynamicStarUnsupported itemIndex))
      | .KeywordMapping =>
          (expandedCount, some (.keywordMappingUnsupported itemIndex))
      | .Positional _ =>
          match Std.Usize.checked_add expandedCount 1#usize with
          | none =>
              (expandedCount, some (.expandedArgumentCountOverflow itemIndex
                expandedCount.val 1))
          | some count =>
              preflightReferenceFrom (itemIndex + 1) count none remaining
      | .Named _ _ =>
          match Std.Usize.checked_add expandedCount 1#usize with
          | none =>
              (expandedCount, some (.expandedArgumentCountOverflow itemIndex
                expandedCount.val 1))
          | some count =>
              preflightReferenceFrom (itemIndex + 1) count none remaining
      | .FixedStar values =>
          let contribution := alloc.vec.Vec.len values
          match Std.Usize.checked_add expandedCount contribution with
          | none =>
              (expandedCount, some (.expandedArgumentCountOverflow itemIndex
                expandedCount.val contribution.val))
          | some count =>
              preflightReferenceFrom (itemIndex + 1) count none remaining

def preflightReference
    (items : Slice (BindCallFull.ActualItem String Int))
    (hasReceiver : Bool) :
    core.result.Result (Std.Usize × Std.Usize) PreflightErrorView :=
  let receiverCount := core.convert.num.FromUsizeBool.from hasReceiver
  match Std.Usize.checked_add (Slice.len items) receiverCount with
  | none => .Err (.sourceExpressionCountOverflow
      (Slice.len items).val receiverCount.val)
  | some sourceCount =>
      let output := preflightReferenceFrom 0 receiverCount none items.val
      match output.2 with
      | some error => .Err error
      | none => .Ok (sourceCount, output.1)

def preflightResultView
    (result : core.result.Result (Std.Usize × Std.Usize)
      (BindCallFull.BindingError String)) :
    core.result.Result (Std.Usize × Std.Usize) PreflightErrorView :=
  match result with
  | .Ok counts => .Ok counts
  | .Err error => .Err (preflightErrorView error)

def preflightOutputView
    (output : Std.Usize × Option (BindCallFull.BindingError String)) :
    Std.Usize × Option PreflightErrorView :=
  (output.1, output.2.map preflightErrorView)

structure PreflightInvariant
    (sourceItems : List (BindCallFull.ActualItem String Int))
    (expected : Std.Usize × Option PreflightErrorView)
    (state : core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter (BindCallFull.ActualItem String Int)) ×
      Std.Usize × Option (BindCallFull.BindingError String)) : Prop where
  iterator : preflightIteratorInvariant state.1
  source : state.1.iter.slice.val = sourceItems
  reference :
    preflightReferenceFrom state.1.iter.i state.2.1
        (state.2.2.map preflightErrorView)
        (sourceItems.drop state.1.iter.i) = expected

theorem preflight_actual_items_loop_body_matches_reference_and_decreases
    (sourceItems : List (BindCallFull.ActualItem String Int))
    (expected : Std.Usize × Option PreflightErrorView)
    (state : core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter (BindCallFull.ActualItem String Int)) ×
      Std.Usize × Option (BindCallFull.BindingError String))
    (invariant : PreflightInvariant sourceItems expected state) :
    WP.spec
      (BindCallFull.preflight_actual_items_loop.body
        state.1 state.2.1 state.2.2)
      (fun flow =>
        match flow with
        | .done output => preflightOutputView output = expected
        | .cont next =>
            PreflightInvariant sourceItems expected next ∧
              preflightRemaining next.1 < preflightRemaining state.1) := by
  rcases state with ⟨iter, expandedCount, preflightError⟩
  have iteratorInvariant := invariant.iterator
  have sourceEq := invariant.source
  have referenceEq := invariant.reference
  change preflightIteratorInvariant iter at iteratorInvariant
  change iter.iter.slice.val = sourceItems at sourceEq
  change preflightReferenceFrom iter.iter.i expandedCount
      (preflightError.map preflightErrorView)
      (sourceItems.drop iter.iter.i) = expected at referenceEq
  unfold BindCallFull.preflight_actual_items_loop.body
  unfold preflightIteratorInvariant at iteratorInvariant
  step with preflight_enumerate_slice_next_decreases_or_finishes
  cases o with
  | none =>
      rcases o_post with ⟨sameState, noRemaining⟩
      have exhausted : sourceItems.length ≤ iter.iter.i := by
        unfold preflightRemaining at noRemaining
        rw [sourceEq] at noRemaining
        exact Nat.sub_eq_zero_iff_le.mp noRemaining
      have dropped : sourceItems.drop iter.iter.i = [] :=
        List.drop_eq_nil_iff.mpr exhausted
      cases preflightError <;>
        simp_all [preflightOutputView, preflightReferenceFrom, dropped]
  | some pair =>
      rcases pair with ⟨itemIndex, item⟩
      rcases o_post with
        ⟨returnedIndex, itemAt, decreases, exactDecrease, sameSlice,
          nextIndex, nextIndexBound, nextCountBound⟩
      have sourceBound : iter.iter.i < sourceItems.length := by
        obtain ⟨itemBound, _⟩ := getElem?_eq_some_iff.mp itemAt
        simpa [sourceEq] using itemBound
      have sourceItemAt : sourceItems[iter.iter.i]? = some item := by
        simpa [sourceEq] using itemAt
      have sourceInput : sourceItems[iter.iter.i] = item := by
        simpa only [List.getElem?_eq_getElem sourceBound, Option.some.injEq]
          using sourceItemAt
      have dropStep : sourceItems.drop iter.iter.i =
          item :: sourceItems.drop (iter.iter.i + 1) := by
        rw [List.drop_eq_getElem_cons sourceBound, sourceInput]
      cases preflightError with
      | some error =>
          simp only [Option.isNone, Bool.false_eq_true, if_false]
          constructor
          · refine {
              iterator := ?_, source := ?_, reference := ?_
            }
            · unfold preflightIteratorInvariant
              exact ⟨nextIndexBound, nextCountBound⟩
            · rw [sameSlice]
              exact sourceEq
            · simpa [dropStep, preflightReferenceFrom] using referenceEq
          · exact decreases
      | none =>
          cases item with
          | DynamicStar =>
              simp only [Option.isNone, if_true, if_false]
              constructor
              · refine { iterator := ?_, source := ?_, reference := ?_ }
                · unfold preflightIteratorInvariant
                  exact ⟨nextIndexBound, nextCountBound⟩
                · rw [sameSlice]
                  exact sourceEq
                · simpa [preflightReferenceFrom, preflightErrorView,
                    returnedIndex, nextIndex, dropStep] using referenceEq
              · exact decreases
          | KeywordMapping =>
              simp only [Option.isNone, if_true, if_false]
              constructor
              · refine { iterator := ?_, source := ?_, reference := ?_ }
                · unfold preflightIteratorInvariant
                  exact ⟨nextIndexBound, nextCountBound⟩
                · rw [sameSlice]
                  exact sourceEq
                · simpa [preflightReferenceFrom, preflightErrorView,
                    returnedIndex, nextIndex, dropStep] using referenceEq
              · exact decreases
          | Positional value =>
              simp only [Option.isNone, if_true]
              generalize checkedEq : Std.Usize.checked_add expandedCount
                1#usize = checked
              cases checked with
              | none =>
                  simp [checkedEq]
                  constructor
                  · refine { iterator := ?_, source := ?_, reference := ?_ }
                    · unfold preflightIteratorInvariant
                      exact ⟨nextIndexBound, nextCountBound⟩
                    · rw [sameSlice]
                      exact sourceEq
                    · simpa [preflightReferenceFrom, preflightErrorView,
                        checkedEq, returnedIndex, nextIndex, dropStep] using
                          referenceEq
                  · exact decreases
              | some count =>
                  simp [checkedEq]
                  constructor
                  · refine { iterator := ?_, source := ?_, reference := ?_ }
                    · unfold preflightIteratorInvariant
                      exact ⟨nextIndexBound, nextCountBound⟩
                    · rw [sameSlice]
                      exact sourceEq
                    · simpa [preflightReferenceFrom, checkedEq, returnedIndex,
                        nextIndex, dropStep] using referenceEq
                  · exact decreases
          | Named argumentName value =>
              simp only [Option.isNone, if_true]
              generalize checkedEq : Std.Usize.checked_add expandedCount
                1#usize = checked
              cases checked with
              | none =>
                  simp [checkedEq]
                  constructor
                  · refine { iterator := ?_, source := ?_, reference := ?_ }
                    · unfold preflightIteratorInvariant
                      exact ⟨nextIndexBound, nextCountBound⟩
                    · rw [sameSlice]
                      exact sourceEq
                    · simpa [preflightReferenceFrom, preflightErrorView,
                        checkedEq, returnedIndex, nextIndex, dropStep] using
                          referenceEq
                  · exact decreases
              | some count =>
                  simp [checkedEq]
                  constructor
                  · refine { iterator := ?_, source := ?_, reference := ?_ }
                    · unfold preflightIteratorInvariant
                      exact ⟨nextIndexBound, nextCountBound⟩
                    · rw [sameSlice]
                      exact sourceEq
                    · simpa [preflightReferenceFrom, checkedEq, returnedIndex,
                        nextIndex, dropStep] using referenceEq
                  · exact decreases
          | FixedStar values =>
              simp only [Option.isNone, if_true]
              generalize checkedEq : Std.Usize.checked_add expandedCount
                (alloc.vec.Vec.len values) = checked
              cases checked with
              | none =>
                  simp [checkedEq]
                  constructor
                  · refine { iterator := ?_, source := ?_, reference := ?_ }
                    · unfold preflightIteratorInvariant
                      exact ⟨nextIndexBound, nextCountBound⟩
                    · rw [sameSlice]
                      exact sourceEq
                    · simpa [preflightReferenceFrom, preflightErrorView,
                        checkedEq, returnedIndex, nextIndex, dropStep] using
                          referenceEq
                  · exact decreases
              | some count =>
                  simp [checkedEq]
                  constructor
                  · refine { iterator := ?_, source := ?_, reference := ?_ }
                    · unfold preflightIteratorInvariant
                      exact ⟨nextIndexBound, nextCountBound⟩
                    · rw [sameSlice]
                      exact sourceEq
                    · simpa [preflightReferenceFrom, checkedEq, returnedIndex,
                        nextIndex, dropStep] using referenceEq
                  · exact decreases

theorem preflight_actual_items_loop_matches_reference
    (sourceItems : List (BindCallFull.ActualItem String Int))
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter (BindCallFull.ActualItem String Int)))
    (expandedCount : Std.Usize)
    (preflightError : Option (BindCallFull.BindingError String))
    (iteratorInvariant : preflightIteratorInvariant iter)
    (sourceEq : iter.iter.slice.val = sourceItems) :
    WP.spec
      (BindCallFull.preflight_actual_items_loop iter expandedCount preflightError)
      (fun output =>
        preflightOutputView output =
          preflightReferenceFrom iter.iter.i expandedCount
            (preflightError.map preflightErrorView)
            (sourceItems.drop iter.iter.i)) := by
  let expected := preflightReferenceFrom iter.iter.i expandedCount
    (preflightError.map preflightErrorView) (sourceItems.drop iter.iter.i)
  have initialInvariant : PreflightInvariant sourceItems expected
      (iter, expandedCount, preflightError) := {
    iterator := iteratorInvariant
    source := sourceEq
    reference := rfl
  }
  unfold BindCallFull.preflight_actual_items_loop
  apply loop.spec_decr_nat
      (measure := fun state => preflightRemaining state.1)
      (inv := PreflightInvariant sourceItems expected)
      (post := fun output => preflightOutputView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (preflight_actual_items_loop_body_matches_reference_and_decreases
      sourceItems expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem preflight_actual_items_matches_reference
    (items : Slice (BindCallFull.ActualItem String Int))
    (hasReceiver : Bool) :
    WP.spec (BindCallFull.preflight_actual_items items hasReceiver)
      (fun output =>
        preflightResultView output = preflightReference items hasReceiver) := by
  unfold BindCallFull.preflight_actual_items
  simp [Aeneas.Std.lift]
  unfold preflightReference
  generalize sourceCheckedEq : Std.Usize.checked_add (Slice.len items)
    (core.convert.num.FromUsizeBool.from hasReceiver) = sourceChecked
  cases sourceChecked with
  | none =>
      simp [sourceCheckedEq, preflightResultView,
        preflightErrorView, WP.spec, WP.theta, WP.wp_return]
  | some sourceCount =>
      simp only [sourceCheckedEq]
      simp only [core.slice.Slice.iter]
      step with
        core.iter.traits.iterator.Iterator.enumerate.trait_default.spec
        as ⟨iter, iterPost, countPost⟩
      have iteratorInvariant : preflightIteratorInvariant iter := by
        unfold preflightIteratorInvariant
        simp_all
      have sourceEq : iter.iter.slice.val = items.val := by simp_all
      step with preflight_actual_items_loop_matches_reference as
        ⟨expandedCount, preflightError, loopPost⟩ by
          · exact iteratorInvariant
          · exact sourceEq
      have exactLoop : preflightOutputView (expandedCount, preflightError) =
          preflightReferenceFrom 0
            (core.convert.num.FromUsizeBool.from hasReceiver) none items.val := by
        simpa [iterPost] using loopPost
      generalize referenceEq :
        preflightReferenceFrom 0
          (core.convert.num.FromUsizeBool.from hasReceiver) none items.val =
            reference
      rcases reference with ⟨referenceCount, referenceError⟩
      rw [referenceEq] at exactLoop
      cases hActualError : preflightError <;>
        cases hReferenceError : referenceError <;>
          simp_all [preflightOutputView, preflightResultView,
            sourceCheckedEq, WP.spec, WP.theta, WP.wp_return]

def actualItemSupported : BindCallFull.ActualItem String Int → Prop
  | .DynamicStar | .KeywordMapping => False
  | _ => True

theorem preflightReferenceFrom_success_facts
    (items : List (BindCallFull.ActualItem String Int))
    (itemIndex : Nat) (expandedCount finalCount : Std.Usize)
    (success : preflightReferenceFrom itemIndex expandedCount none items =
      (finalCount, none)) :
    (forall item, item ∈ items → actualItemSupported item) ∧
      finalCount.val = expandedCount.val +
        (items.map outerActualContribution).sum ∧
      finalCount.val ≤ Std.Usize.max := by
  induction items generalizing itemIndex expandedCount with
  | nil =>
      simp [preflightReferenceFrom] at success
      subst finalCount
      have scalarBound := UScalar.hBounds expandedCount
      change expandedCount.val < 2 ^ System.Platform.numBits at scalarBound
      have maxSucc := Std.Usize.max_succ_eq_pow
      exact ⟨by simp, by simp, by omega⟩
  | cons item remainingItems inductionHypothesis =>
      cases item with
      | DynamicStar => simp [preflightReferenceFrom] at success
      | KeywordMapping => simp [preflightReferenceFrom] at success
      | Positional typedValue =>
          simp only [preflightReferenceFrom] at success
          generalize checkedEq : Std.Usize.checked_add expandedCount 1#usize =
            checked at success
          cases checked with
          | none => simp [checkedEq] at success
          | some nextCount =>
              have checkedSpec := Std.Usize.checked_add_bv_spec expandedCount
                1#usize
              rw [checkedEq] at checkedSpec
              have remainingFacts := inductionHypothesis
                (itemIndex := itemIndex + 1) (expandedCount := nextCount)
                success
              simp_all [actualItemSupported, outerActualContribution,
                alloc.vec.Vec.len, alloc.vec.Vec.length]
              omega
      | Named argumentName typedValue =>
          simp only [preflightReferenceFrom] at success
          generalize checkedEq : Std.Usize.checked_add expandedCount 1#usize =
            checked at success
          cases checked with
          | none => simp [checkedEq] at success
          | some nextCount =>
              have checkedSpec := Std.Usize.checked_add_bv_spec expandedCount
                1#usize
              rw [checkedEq] at checkedSpec
              have remainingFacts := inductionHypothesis
                (itemIndex := itemIndex + 1) (expandedCount := nextCount)
                success
              simp_all [actualItemSupported, outerActualContribution,
                alloc.vec.Vec.len, alloc.vec.Vec.length]
              omega
      | FixedStar values =>
          simp only [preflightReferenceFrom] at success
          generalize checkedEq : Std.Usize.checked_add expandedCount
            (alloc.vec.Vec.len values) = checked at success
          cases checked with
          | none => simp [checkedEq] at success
          | some nextCount =>
              have checkedSpec := Std.Usize.checked_add_bv_spec expandedCount
                (alloc.vec.Vec.len values)
              rw [checkedEq] at checkedSpec
              have remainingFacts := inductionHypothesis
                (itemIndex := itemIndex + 1) (expandedCount := nextCount)
                success
              simp_all [actualItemSupported, outerActualContribution,
                alloc.vec.Vec.len, alloc.vec.Vec.length]
              omega

theorem preflightReference_success_facts
    (items : Slice (BindCallFull.ActualItem String Int))
    (hasReceiver : Bool) (sourceCount expandedCount : Std.Usize)
    (success : preflightReference items hasReceiver =
      .Ok (sourceCount, expandedCount)) :
    (forall item, item ∈ items.val → actualItemSupported item) ∧
      sourceCount.val = items.val.length +
        (core.convert.num.FromUsizeBool.from hasReceiver).val ∧
      sourceCount.val ≤ Std.Usize.max ∧
      expandedCount.val =
        (core.convert.num.FromUsizeBool.from hasReceiver).val +
          (items.val.map outerActualContribution).sum ∧
      expandedCount.val ≤ Std.Usize.max := by
  unfold preflightReference at success
  dsimp only at success
  generalize sourceCheckedEq : Std.Usize.checked_add (Slice.len items)
    (core.convert.num.FromUsizeBool.from hasReceiver) = sourceChecked at success
  cases sourceChecked with
  | none => simp [sourceCheckedEq] at success
  | some actualSourceCount =>
      have sourceSpec := Std.Usize.checked_add_bv_spec (Slice.len items)
        (core.convert.num.FromUsizeBool.from hasReceiver)
      rw [sourceCheckedEq] at sourceSpec
      generalize referenceEq : preflightReferenceFrom 0
        (core.convert.num.FromUsizeBool.from hasReceiver) none items.val =
          reference at success
      rcases reference with ⟨referenceCount, referenceError⟩
      cases hError : referenceError with
      | some reason => simp [hError] at success
      | none =>
          have countsEq : (actualSourceCount, referenceCount) =
              (sourceCount, expandedCount) := by
            simpa [hError] using success
          injection countsEq with sourceEq expandedEq
          subst sourceCount
          subst expandedCount
          have referenceSuccess : preflightReferenceFrom 0
              (core.convert.num.FromUsizeBool.from hasReceiver) none items.val =
                (referenceCount, none) := by
            simpa [hError] using referenceEq
          have facts := preflightReferenceFrom_success_facts items.val 0
            (core.convert.num.FromUsizeBool.from hasReceiver) referenceCount
            referenceSuccess
          simp [alloc.vec.Vec.len, alloc.vec.Vec.length] at sourceSpec
          exact ⟨facts.1, sourceSpec.2.1, by omega,
            facts.2.1, facts.2.2⟩

inductive ExactExpansionResultView where
  | ok (buffers : ExpansionBuffersView)
  | error (error : BindCallFull.BindingError String)

def exactExpansionResultView :
    core.result.Result (BindCallFull.ExpandedCall String Int)
      (BindCallFull.BindingError String) → ExactExpansionResultView
  | .Ok expanded => .ok (expansionBuffersView expanded.positional
      expanded.named expanded.evaluation_order none)
  | .Err error => .error error

def receiverExpansionBuffers
    (receiver : Option (BindCallFull.Receiver String Int)) :
    ExpansionBuffersView :=
  match receiver with
  | none => {
      positional := []
      named := []
      evaluationOrder := []
      error := none
    }
  | some receiverValue => {
      positional := [{
        value := receiverValue.value
        origin := .Receiver
        evaluationPosition := .receiver
      }]
      named := []
      evaluationOrder := [.receiver]
      error := none
    }

inductive ExpandActualItemsReference {Allocator : Type}
    (allocatorInst : BindCallFull.BindingAllocator Allocator)
    (items : Slice (BindCallFull.ActualItem String Int))
    (receiver : Option (BindCallFull.Receiver String Int))
    (initial : Allocator) :
    core.result.Result (BindCallFull.ExpandedCall String Int)
      (BindCallFull.BindingError String) → Allocator → Prop where
  | preflightFailed (error : BindCallFull.BindingError String)
      (reason : PreflightErrorView)
      (reference : preflightReference items receiver.isSome = .Err reason)
      (errorView : preflightErrorView error = reason) :
      ExpandActualItemsReference allocatorInst items receiver initial
        (.Err error) initial
  | positionalAllocationFailed (sourceCount expandedCount : Std.Usize)
      (allocatorAfter : Allocator)
      (reference : preflightReference items receiver.isSome =
        .Ok (sourceCount, expandedCount))
      (transition : AllocatorTransitionReference allocatorInst initial
        .ExpandedPositionals expandedCount
        ((.Err ()) : core.result.Result
          (alloc.vec.Vec (BindCallFull.PositionalActual String Int)) Unit)
        allocatorAfter) :
      ExpandActualItemsReference allocatorInst items receiver initial
        (.Err (.AllocationFailed .ExpandedPositionals expandedCount))
        allocatorAfter
  | namedAllocationFailed (sourceCount expandedCount : Std.Usize)
      (positional : alloc.vec.Vec
        (BindCallFull.PositionalActual String Int))
      (allocator1 allocator2 : Allocator)
      (reference : preflightReference items receiver.isSome =
        .Ok (sourceCount, expandedCount))
      (positionalTransition : AllocatorTransitionReference allocatorInst
        initial .ExpandedPositionals expandedCount (.Ok positional) allocator1)
      (namedTransition : AllocatorTransitionReference allocatorInst allocator1
        .ExpandedNamed sourceCount
        ((.Err ()) : core.result.Result
          (alloc.vec.Vec (BindCallFull.NamedActual String Int)) Unit)
        allocator2) :
      ExpandActualItemsReference allocatorInst items receiver initial
        (.Err (.AllocationFailed .ExpandedNamed sourceCount)) allocator2
  | evaluationAllocationFailed (sourceCount expandedCount : Std.Usize)
      (positional : alloc.vec.Vec
        (BindCallFull.PositionalActual String Int))
      (named : alloc.vec.Vec (BindCallFull.NamedActual String Int))
      (allocator1 allocator2 allocator3 : Allocator)
      (reference : preflightReference items receiver.isSome =
        .Ok (sourceCount, expandedCount))
      (positionalTransition : AllocatorTransitionReference allocatorInst
        initial .ExpandedPositionals expandedCount (.Ok positional) allocator1)
      (namedTransition : AllocatorTransitionReference allocatorInst allocator1
        .ExpandedNamed sourceCount (.Ok named) allocator2)
      (evaluationTransition : AllocatorTransitionReference allocatorInst
        allocator2 .EvaluationOrder sourceCount
        ((.Err ()) : core.result.Result
          (alloc.vec.Vec BindCallFull.EvaluationEvent) Unit) allocator3) :
      ExpandActualItemsReference allocatorInst items receiver initial
        (.Err (.AllocationFailed .EvaluationOrder sourceCount)) allocator3
  | completed (sourceCount expandedCount : Std.Usize)
      (positional : alloc.vec.Vec
        (BindCallFull.PositionalActual String Int))
      (named : alloc.vec.Vec (BindCallFull.NamedActual String Int))
      (evaluationOrder : alloc.vec.Vec BindCallFull.EvaluationEvent)
      (allocator1 allocator2 allocator3 : Allocator)
      (result : core.result.Result (BindCallFull.ExpandedCall String Int)
        (BindCallFull.BindingError String))
      (reference : preflightReference items receiver.isSome =
        .Ok (sourceCount, expandedCount))
      (positionalTransition : AllocatorTransitionReference allocatorInst
        initial .ExpandedPositionals expandedCount (.Ok positional) allocator1)
      (namedTransition : AllocatorTransitionReference allocatorInst allocator1
        .ExpandedNamed sourceCount (.Ok named) allocator2)
      (evaluationTransition : AllocatorTransitionReference allocatorInst
        allocator2 .EvaluationOrder sourceCount (.Ok evaluationOrder) allocator3)
      (resultReference :
        match result with
        | .Ok expanded => expansionBuffersView expanded.positional
            expanded.named expanded.evaluation_order none =
              outerExpansionReference 0 items.val
                (receiverExpansionBuffers receiver)
        | .Err error =>
            (outerExpansionReference 0 items.val
              (receiverExpansionBuffers receiver)).error =
                some (outerExpansionErrorView error)) :
      ExpandActualItemsReference allocatorInst items receiver initial result
        allocator3

set_option maxRecDepth 10000 in
theorem expand_actual_items_with_allocator_matches_reference
    {Allocator : Type}
    (allocatorInst : BindCallFull.BindingAllocator Allocator)
    (allocatorLaw : AllocatorContract allocatorInst)
    (items : Slice (BindCallFull.ActualItem String Int))
    (receiver : Option (BindCallFull.Receiver String Int))
    (allocator : Allocator) :
    WP.spec
      (BindCallFull.expand_actual_items_with_allocator
        (totalIdentityClone String) (totalIdentityClone Int) allocatorInst
        items receiver allocator)
      (fun output => ExpandActualItemsReference allocatorInst items receiver
        allocator output.1 output.2) := by
  unfold BindCallFull.expand_actual_items_with_allocator
  step with preflight_actual_items_matches_reference as
    ⟨preflightResult, preflightPost⟩
  cases preflightResult with
  | Err preflightError =>
      have reference : preflightReference items receiver.isSome =
          .Err (preflightErrorView preflightError) := by
        simpa [preflightResultView] using preflightPost.symm
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        WP.spec, WP.theta, WP.wp_return]
      exact ExpandActualItemsReference.preflightFailed preflightError
        (preflightErrorView preflightError) reference rfl
  | Ok counts =>
      rcases counts with ⟨sourceCount, expandedCount⟩
      have reference : preflightReference items receiver.isSome =
          .Ok (sourceCount, expandedCount) := by
        simpa [preflightResultView] using preflightPost.symm
      have preflightFacts := preflightReference_success_facts items
        receiver.isSome sourceCount expandedCount reference
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      step with allocate_buffer_matches_reference allocatorInst allocatorLaw as
        ⟨positionalResult, allocator1, positionalPost⟩
      cases positionalResult with
      | Err positionalError =>
          cases positionalPost
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            WP.spec, WP.theta, WP.wp_return]
          exact ExpandActualItemsReference.positionalAllocationFailed
            sourceCount expandedCount allocator1 reference
              (by simp [AllocatorTransitionReference])
      | Ok positional0 =>
          cases positionalPost with
          | allocated _ _ positionalEmpty =>
            have positionalTransition : AllocatorTransitionReference
                allocatorInst allocator .ExpandedPositionals expandedCount
                (.Ok positional0) allocator1 := by
              simpa [AllocatorTransitionReference] using positionalEmpty
            simp only [core.result.Result.Insts.CoreOpsTry.branch]
            step with allocate_buffer_matches_reference allocatorInst allocatorLaw as
              ⟨namedResult, allocator2, namedPost⟩
            cases namedResult with
            | Err namedError =>
                cases namedPost
                simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  WP.spec, WP.theta, WP.wp_return]
                exact ExpandActualItemsReference.namedAllocationFailed
                  sourceCount expandedCount positional0 allocator1 allocator2
                  reference positionalTransition
                    (by simp [AllocatorTransitionReference])
            | Ok named0 =>
                cases namedPost with
                | allocated _ _ namedEmpty =>
                  have namedTransition : AllocatorTransitionReference
                      allocatorInst allocator1 .ExpandedNamed sourceCount
                      (.Ok named0) allocator2 := by
                    simpa [AllocatorTransitionReference] using namedEmpty
                  simp only [core.result.Result.Insts.CoreOpsTry.branch]
                  step with allocate_buffer_matches_reference allocatorInst allocatorLaw as
                    ⟨evaluationResult, allocator3, evaluationPost⟩
                  cases evaluationResult with
                  | Err evaluationError =>
                      cases evaluationPost
                      simp [core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        WP.spec, WP.theta, WP.wp_return]
                      exact ExpandActualItemsReference.evaluationAllocationFailed
                        sourceCount expandedCount positional0 named0 allocator1
                        allocator2 allocator3 reference positionalTransition
                        namedTransition (by simp [AllocatorTransitionReference])
                  | Ok evaluation0 =>
                      cases evaluationPost with
                      | allocated _ _ evaluationEmpty =>
                        have evaluationTransition : AllocatorTransitionReference
                            allocatorInst allocator2 .EvaluationOrder sourceCount
                            (.Ok evaluation0) allocator3 := by
                          simpa [AllocatorTransitionReference] using
                            evaluationEmpty
                        cases receiver with
                        | none =>
                            simp only
                            have initialView : expansionBuffersView positional0
                                named0 evaluation0 none =
                                receiverExpansionBuffers none := by
                              simp [expansionBuffersView,
                                receiverExpansionBuffers, positionalEmpty,
                                namedEmpty, evaluationEmpty]
                            simp only [core.slice.Slice.iter]
                            step with
                              core.iter.traits.iterator.Iterator.enumerate.trait_default.spec
                              as ⟨iter, iterPost, countPost⟩
                            have iteratorInvariant : preflightIteratorInvariant iter := by
                              unfold preflightIteratorInvariant
                              simp_all
                            have sourceEq : iter.iter.slice.val = items.val := by
                              simp_all
                            have positionalCapacity :
                                positional0.val.length + named0.val.length +
                                    outerRemainingContribution iter ≤
                                  BindCallFull.USIZE_CAPACITY.val := by
                              simp [positionalEmpty, namedEmpty,
                                outerRemainingContribution,
                                BindCallFull.USIZE_CAPACITY, iterPost]
                              simp only [Option.isSome,
                                core.convert.num.FromUsizeBool.from] at preflightFacts
                              omega
                            have evaluationCapacity :
                                evaluation0.val.length + preflightRemaining iter ≤
                                  BindCallFull.USIZE_CAPACITY.val := by
                              simp [evaluationEmpty, preflightRemaining,
                                BindCallFull.USIZE_CAPACITY, iterPost]
                              omega
                            step with expand_actual_items_outer_loop_matches_reference
                              as ⟨positional1, named1, evaluation1,
                                expansionError, loopPost⟩ by
                                  · exact iteratorInvariant
                                  · exact sourceEq
                                  · exact positionalCapacity
                                  · exact evaluationCapacity
                            have exactLoop : expansionBuffersView positional1
                                named1 evaluation1 expansionError =
                                outerExpansionReference 0 items.val
                                  (receiverExpansionBuffers none) := by
                              simpa [iterPost, initialView] using loopPost
                            cases hError : expansionError with
                            | none =>
                                simp [hError, WP.spec, WP.theta, WP.wp_return]
                                exact ExpandActualItemsReference.completed
                                  sourceCount expandedCount positional0 named0
                                  evaluation0 allocator1 allocator2 allocator3
                                  (.Ok ({
                                    positional := positional1
                                    named := named1
                                    evaluation_order := evaluation1 } :
                                      BindCallFull.ExpandedCall String Int)) reference
                                  positionalTransition namedTransition
                                  evaluationTransition (by
                                    simpa [hError] using exactLoop)
                            | some error =>
                                simp [hError, WP.spec, WP.theta, WP.wp_return]
                                exact ExpandActualItemsReference.completed
                                  sourceCount expandedCount positional0 named0
                                  evaluation0 allocator1 allocator2 allocator3
                                  (.Err error) reference positionalTransition
                                  namedTransition evaluationTransition (by
                                    simpa [hError, expansionBuffersView] using
                                      congrArg ExpansionBuffersView.error
                                        exactLoop.symm)

                        | some receiverValue =>
                            simp only
                            step as ⟨evaluationWithReceiver, evaluationPush⟩
                            step as ⟨positionalWithReceiver, positionalPush⟩
                            have initialView : expansionBuffersView
                                positionalWithReceiver named0 evaluationWithReceiver
                                none = receiverExpansionBuffers (some receiverValue) := by
                              simp [expansionBuffersView, receiverExpansionBuffers,
                                positionalEmpty, namedEmpty, evaluationEmpty] at evaluationPush positionalPush ⊢
                              simp_all [evaluationEventView, positionalActualView,
                                evaluationPositionView]
                            simp only [core.slice.Slice.iter]
                            step with
                              core.iter.traits.iterator.Iterator.enumerate.trait_default.spec
                              as ⟨iter, iterPost, countPost⟩
                            have iteratorInvariant : preflightIteratorInvariant iter := by
                              unfold preflightIteratorInvariant
                              simp_all
                            have sourceEq : iter.iter.slice.val = items.val := by
                              simp_all
                            have positionalCapacity :
                                positionalWithReceiver.val.length + named0.val.length +
                                    outerRemainingContribution iter ≤
                                  BindCallFull.USIZE_CAPACITY.val := by
                              simp [positionalEmpty, namedEmpty,
                                outerRemainingContribution,
                                BindCallFull.USIZE_CAPACITY, iterPost] at positionalPush ⊢
                              rw [positionalPush]
                              simp only [Option.isSome,
                                core.convert.num.FromUsizeBool.from] at preflightFacts
                              simp
                              have expandedExact : expandedCount.val = 1 +
                                  (items.val.map outerActualContribution).sum := by
                                simpa [Option.isSome,
                                  core.convert.num.FromUsizeBool.from] using
                                    preflightFacts.2.2.2.1
                              omega
                            have evaluationCapacity :
                                evaluationWithReceiver.val.length +
                                    preflightRemaining iter ≤
                                  BindCallFull.USIZE_CAPACITY.val := by
                              simp [evaluationEmpty, preflightRemaining,
                                BindCallFull.USIZE_CAPACITY, iterPost] at evaluationPush ⊢
                              rw [evaluationPush]
                              simp
                              have sourceExact : sourceCount.val =
                                  items.val.length + 1 := by
                                simpa [Option.isSome,
                                  core.convert.num.FromUsizeBool.from] using
                                    preflightFacts.2.1
                              omega
                            step with expand_actual_items_outer_loop_matches_reference
                              as ⟨positional1, named1, evaluation1,
                                expansionError, loopPost⟩ by
                                  · exact iteratorInvariant
                                  · exact sourceEq
                                  · exact positionalCapacity
                                  · exact evaluationCapacity
                            have exactLoop : expansionBuffersView positional1
                                named1 evaluation1 expansionError =
                                outerExpansionReference 0 items.val
                                  (receiverExpansionBuffers (some receiverValue)) := by
                              simpa [iterPost, initialView] using loopPost
                            cases hError : expansionError with
                            | none =>
                                simp [hError, WP.spec, WP.theta, WP.wp_return]
                                exact ExpandActualItemsReference.completed
                                  sourceCount expandedCount positional0 named0
                                  evaluation0 allocator1 allocator2 allocator3
                                  (.Ok ({
                                    positional := positional1
                                    named := named1
                                    evaluation_order := evaluation1 } :
                                      BindCallFull.ExpandedCall String Int)) reference
                                  positionalTransition namedTransition
                                  evaluationTransition (by
                                    simpa [hError] using exactLoop)
                            | some error =>
                                simp [hError, WP.spec, WP.theta, WP.wp_return]
                                exact ExpandActualItemsReference.completed
                                  sourceCount expandedCount positional0 named0
                                  evaluation0 allocator1 allocator2 allocator3
                                  (.Err error) reference positionalTransition
                                  namedTransition evaluationTransition (by
                                    simpa [hError, expansionBuffersView] using
                                      congrArg ExpansionBuffersView.error
                                        exactLoop.symm)

theorem usize_saturating_add_val (left right : Std.Usize) :
    (UScalar.saturating_add left right).val =
      min Std.Usize.max (left.val + right.val) := by
  unfold UScalar.saturating_add UScalar.val
  rw [UScalar.max_USize_eq, BitVec.toNat_ofNat]
  have maxSucc := Std.Usize.max_succ_eq_pow
  apply Nat.mod_eq_of_lt
  change min Std.Usize.max (left.bv.toNat + right.bv.toNat) <
    2 ^ System.Platform.numBits
  rw [← maxSucc]
  exact Nat.lt_succ_of_le
    (Nat.min_le_left Std.Usize.max (left.bv.toNat + right.bv.toNat))

theorem signaturePositionalCount_eq_counts
    (signature : BindCallFull.CallSignature String Int)
    (counts : BindCallFull.SignatureCounts)
    (success : signatureCountsReference signature = .Ok counts) :
    signaturePositionalCount signature = counts.positional_count := by
  have facts := signatureCountsReference_success_facts signature counts success
  apply UScalar.eq_of_val_eq
  unfold signaturePositionalCount
  unfold core.num.Usize.saturating_add
  rw [usize_saturating_add_val]
  rw [Nat.min_eq_right]
  · exact facts.1.symm
  · calc
      signature.positional_only.val.length +
          signature.positional.val.length = counts.positional_count.val :=
        facts.1.symm
      _ ≤ counts.parameter_count.val := by
        rw [facts.2.1]
        omega
      _ ≤ Std.Usize.max := facts.2.2

theorem validate_call_with_counts_matches_reference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (counts : BindCallFull.SignatureCounts)
    (success : signatureCountsReference signature = .Ok counts) :
    WP.spec
      (BindCallFull.validate_call
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature call counts.positional_count ())
      (fun output => output = validateCallReference signature call) := by
  have facts := signatureCountsReference_success_facts signature counts success
  rw [← signaturePositionalCount_eq_counts signature counts success]
  exact validate_call_matches_exact_reference signature call (by omega)

inductive CanonicalEnvironmentReference {Allocator : Type}
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (counts : BindCallFull.SignatureCounts) :
    core.result.Result (BindCallFull.BindingEnvironment String Int)
      (BindCallFull.BindingError String) → Allocator → Prop where
  | allocationFailed (site : BindCallFull.AllocationSite)
      (requested : Std.Usize) (allocator : Allocator) :
      CanonicalEnvironmentReference signature call counts
        (.Err (.AllocationFailed site requested)) allocator
  | completed (result : core.result.Result
      (BindCallFull.BindingEnvironment String Int)
      (BindCallFull.BindingError String)) (allocator : Allocator)
      (reference : bindingResultView result =
        canonicalEnvironmentReference signature call) :
      CanonicalEnvironmentReference signature call counts result allocator

set_option maxRecDepth 10000 in
theorem canonical_environment_matches_reference
    {Allocator : Type}
    (allocatorInst : BindCallFull.BindingAllocator Allocator)
    (allocatorLaw : AllocatorContract allocatorInst)
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (counts : BindCallFull.SignatureCounts)
    (countReference : signatureCountsReference signature = .Ok counts)
    (allocator : Allocator) :
    WP.spec
      (BindCallFull.canonical_environment (totalIdentityClone String)
        (totalIdentityClone Int) allocatorInst signature call counts allocator)
      (fun output => CanonicalEnvironmentReference signature call counts
        output.1 output.2) := by
  unfold BindCallFull.canonical_environment
  have countFacts := signatureCountsReference_success_facts signature counts
    countReference
  step with allocate_buffer_matches_reference allocatorInst allocatorLaw as
    ⟨cellsResult, allocator1, cellsPost⟩
  cases cellsResult with
  | Err cellsError =>
      cases cellsPost
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        WP.spec, WP.theta, WP.wp_return]
      exact CanonicalEnvironmentReference.allocationFailed .BindingCells
        counts.parameter_count allocator1
  | Ok cells0 =>
      cases cellsPost with
      | allocated _ _ cellsEmpty =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch]
        step with canonical_environment_loop0_matches_reference as
          ⟨call1, cells1, constructionError, call1Eq, loop0Post⟩ by
            change cells0.val.length +
              (signature.positional_only.val.length - 0) ≤ Std.Usize.max
            rw [cellsEmpty]
            simp only [List.length_nil, Nat.zero_add, Nat.sub_zero]
            have totalEq := countFacts.2.1
            omega
        have positionalOnlyEq :
            canonicalPositionalOnlyReference signature.positional_only.val call
              0 [] none = (cells1.val, constructionError) := by
          simpa [cellsEmpty] using loop0Post.symm
        cases hPositionalOnlyError : constructionError with
        | some error =>
            simp only
            apply CanonicalEnvironmentReference.completed
            simp [WP.spec, WP.theta, WP.wp_return, bindingResultView,
              canonicalEnvironmentReference_after_positional_only_error
                signature call cells1.val error
                (by simpa [hPositionalOnlyError] using positionalOnlyEq)]
        | none =>
            simp only
            have positionalOnlySuccessEq :
                canonicalPositionalOnlyReference signature.positional_only.val
                  call 0 [] none = (cells1.val, none) := by
              simpa [hPositionalOnlyError] using positionalOnlyEq
            have cells1Bound := canonicalPositionalOnlyReference_length
              signature.positional_only.val call 0 [] none
            rw [positionalOnlyEq] at cells1Bound
            simp only [List.length_nil, Nat.zero_add] at cells1Bound
            step with canonical_environment_loop1_matches_reference as
              ⟨call2, cells2, constructionError2, call2Eq, loop1Post⟩ by
                change cells1.val.length +
                  (signature.positional.val.length - 0) ≤ Std.Usize.max
                simp only [Nat.sub_zero]
                have totalEq := countFacts.2.1
                omega
            have ordinaryEq :
                canonicalOrdinaryReference signature.positional.val call
                  signature.positional_only.val.length 0 cells1.val none =
                    (cells2.val, constructionError2) := by
              simpa [call1Eq] using loop1Post.symm
            cases hOrdinaryError : constructionError2 with
            | some error =>
                simp only
                apply CanonicalEnvironmentReference.completed
                simp [WP.spec, WP.theta, WP.wp_return, bindingResultView,
                  canonicalEnvironmentReference_after_ordinary_error signature
                    call cells1.val cells2.val error positionalOnlySuccessEq
                    (by simpa [hPositionalOnlyError, hOrdinaryError] using
                      ordinaryEq)]
            | none =>
                simp only
                have ordinarySuccessEq :
                    canonicalOrdinaryReference signature.positional.val call
                      signature.positional_only.val.length 0 cells1.val none =
                        (cells2.val, none) := by
                  simpa [hOrdinaryError] using ordinaryEq
                have cells2Bound := canonicalOrdinaryReference_length
                  signature.positional.val call
                    signature.positional_only.val.length 0 cells1.val none
                rw [ordinaryEq] at cells2Bound
                simp only [Prod.fst] at cells2Bound
                step with canonical_environment_loop2_matches_reference as
                  ⟨call3, cells3, constructionError3, call3Eq, loop2Post⟩ by
                    change cells2.val.length +
                      (signature.keyword_only.val.length - 0) ≤ Std.Usize.max
                    simp only [Nat.sub_zero]
                    have totalEq := countFacts.2.1
                    omega
                have keywordEq :
                    canonicalKeywordOnlyReference signature.keyword_only.val
                      call cells2.val none = (cells3.val, constructionError3) := by
                  simpa [call2Eq, call1Eq] using loop2Post.symm
                cases hKeywordError : constructionError3 with
                | some error =>
                    simp only
                    apply CanonicalEnvironmentReference.completed
                    simp [WP.spec, WP.theta, WP.wp_return, bindingResultView,
                      canonicalEnvironmentReference_after_keyword_error
                        signature call cells1.val cells2.val cells3.val error
                        positionalOnlySuccessEq ordinarySuccessEq
                        (by simpa [hOrdinaryError, hKeywordError] using
                          keywordEq)]
                | none =>
                    simp only
                    have keywordSuccessEq :
                        canonicalKeywordOnlyReference
                          signature.keyword_only.val call cells2.val none =
                            (cells3.val, none) := by
                      simpa [hKeywordError] using keywordEq
                    have call3EqFinal : call3 = call :=
                      call3Eq.trans (call2Eq.trans call1Eq)
                    have cells3Bound := canonicalKeywordOnlyReference_length
                      signature.keyword_only.val call cells2.val none
                    rw [keywordEq] at cells3Bound
                    simp only [Prod.fst] at cells3Bound
                    cases hVarArgs : signature.var_args with
                    | none =>
                        cases hKeywordArgs : signature.keyword_args with
                        | none =>
                            apply CanonicalEnvironmentReference.completed
                            simp [hVarArgs, hKeywordArgs, call3EqFinal,
                              WP.spec, WP.theta, WP.wp_return,
                              bindingResultView, bindingEnvironmentView,
                              canonicalEnvironmentReference,
                              canonicalBaseReference, positionalOnlyEq,
                              ordinaryEq, keywordEq, positionalOnlySuccessEq,
                              ordinarySuccessEq, keywordSuccessEq,
                              hPositionalOnlyError, hOrdinaryError,
                              hKeywordError]
                        | some keywordArgs =>
                            have keywordSignatureEq := canonicalKeywordSignature_eq
                              signature keywordArgs hVarArgs hKeywordArgs
                            step with allocate_buffer_matches_reference
                              allocatorInst allocatorLaw as
                                ⟨residualResult, allocator2, residualPost⟩
                            cases residualResult with
                            | Err residualError =>
                                cases residualPost
                                simp [core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  WP.spec, WP.theta, WP.wp_return]
                                exact CanonicalEnvironmentReference.allocationFailed
                                  .ResidualKeywords (alloc.vec.Vec.len call3.named)
                                  allocator2
                            | Ok residuals0 =>
                                cases residualPost with
                                | allocated _ _ residualsEmpty =>
                                  simp only [core.result.Result.Insts.CoreOpsTry.branch]
                                  step with
                                    canonical_environment_loop3_matches_reference
                                    as ⟨residuals, residualsEq⟩ by
                                      · simp
                                      · simp [residualsEmpty]
                                        exact call3.named.property
                                  step with formal_parameter_total_clone_spec as
                                    ⟨clonedKeywordArgs, clonedKeywordArgsEq⟩
                                  have cells3PushBound : cells3.val.length <
                                      Std.Usize.max := by
                                    have totalEq := countFacts.2.1
                                    simp [hVarArgs, hKeywordArgs,
                                      core.convert.num.FromUsizeBool.from] at totalEq
                                    omega
                                  step with alloc.vec.Vec.push_spec as
                                    ⟨cells4, cells4Eq⟩ by
                                      exact cells3PushBound
                                  apply CanonicalEnvironmentReference.completed
                                  simp [hVarArgs, hKeywordArgs, call3EqFinal,
                                    cells4Eq, residualsEq, residualsEmpty,
                                    keywordSignatureEq, WP.spec, WP.theta,
                                    WP.wp_return, bindingResultView,
                                    bindingEnvironmentView, boundArgumentView,
                                    bindingCellView, clonedKeywordArgsEq,
                                    canonicalEnvironmentReference,
                                    canonicalBaseReference, positionalOnlyEq,
                                    ordinaryEq, keywordEq,
                                    positionalOnlySuccessEq,
                                    ordinarySuccessEq, keywordSuccessEq,
                                    hPositionalOnlyError, hOrdinaryError,
                                    hKeywordError]
                    | some varArgs =>
                        simp only
                        by_cases hResidualCount :
                            alloc.vec.Vec.len call3.positional >
                              counts.positional_count
                        · rw [if_pos hResidualCount]
                          step as ⟨residualCount, residualCountEq⟩ by
                            omega
                          step with allocate_buffer_matches_reference
                            allocatorInst allocatorLaw as
                              ⟨residualResult, allocator2, residualPost⟩
                          cases residualResult with
                          | Err residualError =>
                              cases residualPost
                              simp [core.result.Result.Insts.CoreOpsTry.branch,
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                WP.spec, WP.theta, WP.wp_return]
                              exact CanonicalEnvironmentReference.allocationFailed
                                .ResidualPositionals residualCount allocator2
                          | Ok residuals0 =>
                              cases residualPost with
                              | allocated _ _ residualsEmpty =>
                                simp only [core.result.Result.Insts.CoreOpsTry.branch]
                                step with
                                  canonical_environment_loop4_matches_reference
                                  as ⟨residuals, residualsEq⟩ by
                                    simp [residualsEmpty]
                                    have callBound := call3.positional.property
                                    omega
                                step with formal_parameter_total_clone_spec as
                                  ⟨clonedVarArgs, clonedVarArgsEq⟩
                                have cells3PushBound : cells3.val.length <
                                    Std.Usize.max := by
                                  have totalEq := countFacts.2.1
                                  simp [hVarArgs,
                                    core.convert.num.FromUsizeBool.from] at totalEq
                                  omega
                                step with alloc.vec.Vec.push_spec as
                                  ⟨cells4, cells4Eq⟩ by
                                    exact cells3PushBound
                                cases hKeywordArgs : signature.keyword_args with
                                | none =>
                                    apply CanonicalEnvironmentReference.completed
                                    simp [countFacts.1, hVarArgs, hKeywordArgs,
                                      call3EqFinal, residualCountEq,
                                      residualsEq, residualsEmpty, cells4Eq,
                                      WP.spec, WP.theta, WP.wp_return,
                                      bindingResultView, bindingEnvironmentView,
                                      boundArgumentView, bindingCellView,
                                      clonedVarArgsEq,
                                      canonicalEnvironmentReference,
                                      canonicalBaseReference,
                                      canonicalPositionalReference,
                                      positionalOnlyEq, ordinaryEq, keywordEq,
                                      positionalOnlySuccessEq,
                                      ordinarySuccessEq, keywordSuccessEq,
                                      hPositionalOnlyError, hOrdinaryError,
                                      hKeywordError]
                                | some keywordArgs =>
                                    have variadicSignatureEq :=
                                      canonicalVariadicSignature_eq signature
                                        varArgs keywordArgs hVarArgs hKeywordArgs
                                    step with allocate_buffer_matches_reference
                                      allocatorInst allocatorLaw as
                                        ⟨keywordResult, allocator3,
                                          keywordPost⟩
                                    cases keywordResult with
                                    | Err keywordError =>
                                        cases keywordPost
                                        simp [core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          WP.spec, WP.theta, WP.wp_return]
                                        exact CanonicalEnvironmentReference.allocationFailed
                                          .ResidualKeywords
                                          (alloc.vec.Vec.len call3.named)
                                          allocator3
                                    | Ok residualKeywords0 =>
                                        cases keywordPost with
                                        | allocated _ _ residualKeywordsEmpty =>
                                          simp only [core.result.Result.Insts.CoreOpsTry.branch]
                                          step with
                                            canonical_environment_loop5_matches_reference
                                            as ⟨residualKeywords,
                                              residualKeywordsEq⟩ by
                                                · simp
                                                · simp [residualKeywordsEmpty]
                                                  exact call3.named.property
                                          step with
                                            formal_parameter_total_clone_spec as
                                              ⟨clonedKeywordArgs,
                                                clonedKeywordArgsEq⟩
                                          have cells4PushBound :
                                              cells4.val.length <
                                                Std.Usize.max := by
                                            have totalEq := countFacts.2.1
                                            simp [hVarArgs, hKeywordArgs,
                                              core.convert.num.FromUsizeBool.from]
                                                at totalEq
                                            rw [cells4Eq]
                                            simp only [List.length_append,
                                              List.length_singleton]
                                            omega
                                          step with alloc.vec.Vec.push_spec as
                                            ⟨cells5, cells5Eq⟩ by
                                              exact cells4PushBound
                                          apply
                                            CanonicalEnvironmentReference.completed
                                          simp [countFacts.1, hVarArgs, hKeywordArgs,
                                            call3EqFinal, residualCountEq,
                                            residualsEq, residualsEmpty,
                                            cells4Eq, residualKeywordsEq,
                                            residualKeywordsEmpty, cells5Eq,
                                            variadicSignatureEq, WP.spec,
                                            WP.theta, WP.wp_return,
                                            bindingResultView,
                                            bindingEnvironmentView,
                                            boundArgumentView,
                                            bindingCellView, clonedVarArgsEq,
                                            clonedKeywordArgsEq,
                                            canonicalEnvironmentReference,
                                            canonicalBaseReference,
                                            canonicalPositionalReference,
                                            positionalOnlyEq, ordinaryEq,
                                            keywordEq,
                                            positionalOnlySuccessEq,
                                            ordinarySuccessEq,
                                            keywordSuccessEq,
                                            hPositionalOnlyError,
                                            hOrdinaryError, hKeywordError]

                        · rw [if_neg hResidualCount]
                          step with allocate_buffer_matches_reference
                            allocatorInst allocatorLaw as
                              ⟨residualResult, allocator2, residualPost⟩
                          cases residualResult with
                          | Err residualError =>
                              cases residualPost
                              simp [core.result.Result.Insts.CoreOpsTry.branch,
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                WP.spec, WP.theta, WP.wp_return]
                              exact CanonicalEnvironmentReference.allocationFailed
                                .ResidualPositionals 0#usize allocator2
                          | Ok residuals0 =>
                              cases residualPost with
                              | allocated _ _ residualsEmpty =>
                                simp only [core.result.Result.Insts.CoreOpsTry.branch]
                                step with
                                  canonical_environment_loop4_matches_reference
                                  as ⟨residuals, residualsEq⟩ by
                                    simp [residualsEmpty]
                                    have callBound := call3.positional.property
                                    omega
                                step with formal_parameter_total_clone_spec as
                                  ⟨clonedVarArgs, clonedVarArgsEq⟩
                                have cells3PushBound : cells3.val.length <
                                    Std.Usize.max := by
                                  have totalEq := countFacts.2.1
                                  simp [hVarArgs,
                                    core.convert.num.FromUsizeBool.from] at totalEq
                                  omega
                                step with alloc.vec.Vec.push_spec as
                                  ⟨cells4, cells4Eq⟩ by
                                    exact cells3PushBound
                                cases hKeywordArgs : signature.keyword_args with
                                | none =>
                                    apply CanonicalEnvironmentReference.completed
                                    simp [countFacts.1, hVarArgs, hKeywordArgs,
                                      call3EqFinal, residualsEq,
                                      residualsEmpty, cells4Eq,
                                      WP.spec, WP.theta, WP.wp_return,
                                      bindingResultView, bindingEnvironmentView,
                                      boundArgumentView, bindingCellView,
                                      clonedVarArgsEq,
                                      canonicalEnvironmentReference,
                                      canonicalBaseReference,
                                      canonicalPositionalReference,
                                      positionalOnlyEq, ordinaryEq, keywordEq,
                                      positionalOnlySuccessEq,
                                      ordinarySuccessEq, keywordSuccessEq,
                                      hPositionalOnlyError, hOrdinaryError,
                                      hKeywordError]
                                | some keywordArgs =>
                                    have variadicSignatureEq :=
                                      canonicalVariadicSignature_eq signature
                                        varArgs keywordArgs hVarArgs hKeywordArgs
                                    step with allocate_buffer_matches_reference
                                      allocatorInst allocatorLaw as
                                        ⟨keywordResult, allocator3,
                                          keywordPost⟩
                                    cases keywordResult with
                                    | Err keywordError =>
                                        cases keywordPost
                                        simp [core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          WP.spec, WP.theta, WP.wp_return]
                                        exact CanonicalEnvironmentReference.allocationFailed
                                          .ResidualKeywords
                                          (alloc.vec.Vec.len call3.named)
                                          allocator3
                                    | Ok residualKeywords0 =>
                                        cases keywordPost with
                                        | allocated _ _ residualKeywordsEmpty =>
                                          simp only [core.result.Result.Insts.CoreOpsTry.branch]
                                          step with
                                            canonical_environment_loop5_matches_reference
                                            as ⟨residualKeywords,
                                              residualKeywordsEq⟩ by
                                                · simp
                                                · simp [residualKeywordsEmpty]
                                                  exact call3.named.property
                                          step with
                                            formal_parameter_total_clone_spec as
                                              ⟨clonedKeywordArgs,
                                                clonedKeywordArgsEq⟩
                                          have cells4PushBound :
                                              cells4.val.length <
                                                Std.Usize.max := by
                                            have totalEq := countFacts.2.1
                                            simp [hVarArgs, hKeywordArgs,
                                              core.convert.num.FromUsizeBool.from]
                                                at totalEq
                                            rw [cells4Eq]
                                            simp only [List.length_append,
                                              List.length_singleton]
                                            omega
                                          step with alloc.vec.Vec.push_spec as
                                            ⟨cells5, cells5Eq⟩ by
                                              exact cells4PushBound
                                          apply
                                            CanonicalEnvironmentReference.completed
                                          simp [countFacts.1, hVarArgs, hKeywordArgs,
                                            call3EqFinal, residualsEq,
                                            residualsEmpty, cells4Eq,
                                            residualKeywordsEq,
                                            residualKeywordsEmpty, cells5Eq,
                                            variadicSignatureEq, WP.spec,
                                            WP.theta, WP.wp_return,
                                            bindingResultView,
                                            bindingEnvironmentView,
                                            boundArgumentView,
                                            bindingCellView, clonedVarArgsEq,
                                            clonedKeywordArgsEq,
                                            canonicalEnvironmentReference,
                                            canonicalBaseReference,
                                            canonicalPositionalReference,
                                            positionalOnlyEq, ordinaryEq,
                                            keywordEq,
                                            positionalOnlySuccessEq,
                                            ordinarySuccessEq,
                                            keywordSuccessEq,
                                            hPositionalOnlyError,
                                            hOrdinaryError, hKeywordError]

inductive BindCallReference {Allocator : Type}
    (allocatorInst : BindCallFull.BindingAllocator Allocator)
    (signature : BindCallFull.CallSignature String Int)
    (items : Slice (BindCallFull.ActualItem String Int))
    (receiver : Option (BindCallFull.Receiver String Int))
    (initial : Allocator) :
    core.result.Result (BindCallFull.BindingEnvironment String Int)
      (BindCallFull.BindingError String) → Allocator → Prop where
  | signatureFailed (error : BindCallFull.BindingError String)
      (allocator : Allocator)
      (signatureReference : ValidateSignatureReference allocatorInst signature
        initial (.Err error) allocator) :
      BindCallReference allocatorInst signature items receiver initial
        (.Err error) allocator
  | expansionFailed (counts : BindCallFull.SignatureCounts)
      (signatureAllocator allocator : Allocator)
      (error : BindCallFull.BindingError String)
      (signatureReference : ValidateSignatureReference allocatorInst signature
        initial (.Ok counts) signatureAllocator)
      (expansionReference : ExpandActualItemsReference allocatorInst items
        receiver signatureAllocator (.Err error) allocator) :
      BindCallReference allocatorInst signature items receiver initial
        (.Err error) allocator
  | callFailed (counts : BindCallFull.SignatureCounts)
      (expanded : BindCallFull.ExpandedCall String Int)
      (signatureAllocator expansionAllocator : Allocator)
      (error : BindCallFull.BindingError String)
      (signatureReference : ValidateSignatureReference allocatorInst signature
        initial (.Ok counts) signatureAllocator)
      (expansionReference : ExpandActualItemsReference allocatorInst items
        receiver signatureAllocator (.Ok expanded) expansionAllocator)
      (callReference : validateCallReference signature expanded = .Err error) :
      BindCallReference allocatorInst signature items receiver initial
        (.Err error) expansionAllocator
  | canonical (counts : BindCallFull.SignatureCounts)
      (expanded : BindCallFull.ExpandedCall String Int)
      (signatureAllocator expansionAllocator allocator : Allocator)
      (result : core.result.Result
        (BindCallFull.BindingEnvironment String Int)
        (BindCallFull.BindingError String))
      (signatureReference : ValidateSignatureReference allocatorInst signature
        initial (.Ok counts) signatureAllocator)
      (expansionReference : ExpandActualItemsReference allocatorInst items
        receiver signatureAllocator (.Ok expanded) expansionAllocator)
      (callReference : validateCallReference signature expanded = .Ok ())
      (canonicalReference : CanonicalEnvironmentReference signature expanded
        counts result allocator) :
      BindCallReference allocatorInst signature items receiver initial result
        allocator

theorem validateSignatureBodyReference_success_identity
    (signature : BindCallFull.CallSignature String Int)
    (input output : BindCallFull.SignatureCounts)
    (success : validateSignatureBodyReference signature input = .Ok output) :
    output = input := by
  unfold validateSignatureBodyReference at success
  dsimp only at success
  repeat' first
  | split at success
  | simp_all

set_option maxRecDepth 10000 in
theorem bind_call_with_allocator_matches_exact_reference
    {Allocator : Type}
    (allocatorInst : BindCallFull.BindingAllocator Allocator)
    (allocatorLaw : AllocatorContract allocatorInst)
    (signature : BindCallFull.CallSignature String Int)
    (items : Slice (BindCallFull.ActualItem String Int))
    (receiver : Option (BindCallFull.Receiver String Int))
    (allocator : Allocator) :
    WP.spec
      (BindCallFull.bind_call_with_allocator (totalIdentityClone String)
        totalStringEq (totalIdentityClone Int) allocatorInst signature items
        receiver allocator)
      (fun output => BindCallReference allocatorInst signature items receiver
        allocator output.1 output.2) := by
  unfold BindCallFull.bind_call_with_allocator
  unfold BindCallFull.bind_call_with_relation
  step with validate_signature_matches_reference allocatorInst allocatorLaw as
    ⟨signatureResult, signatureAllocator, signaturePost⟩
  cases signatureResult with
  | Err signatureError =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        WP.spec, WP.theta, WP.wp_return]
      exact BindCallReference.signatureFailed signatureError signatureAllocator
        signaturePost
  | Ok counts =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      step with expand_actual_items_with_allocator_matches_reference
        allocatorInst allocatorLaw as
          ⟨expansionResult, expansionAllocator, expansionPost⟩
      cases expansionResult with
      | Err expansionError =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            WP.spec, WP.theta, WP.wp_return]
          exact BindCallReference.expansionFailed counts signatureAllocator
            expansionAllocator expansionError signaturePost expansionPost
      | Ok expanded =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch]
          unfold BindCallFull.bind_expanded_call_with
          have countReference : signatureCountsReference signature = .Ok counts := by
            cases signaturePost with
            | validated counts0 values allocatorAfter result reference
                bodyReference transition =>
                have countsEq := validateSignatureBodyReference_success_identity
                  signature counts0 counts bodyReference
                subst counts
                exact reference
          step with validate_call_with_counts_matches_reference signature
            expanded counts countReference as ⟨callResult, callPost⟩
          cases callResult with
          | Err callError =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                WP.spec, WP.theta, WP.wp_return]
              exact BindCallReference.callFailed counts expanded
                signatureAllocator expansionAllocator callError signaturePost
                expansionPost callPost.symm
          | Ok unitValue =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch]
              step with canonical_environment_matches_reference allocatorInst
                allocatorLaw signature expanded counts countReference as
                  ⟨output, canonicalPost⟩
              rcases output with ⟨result, finalAllocator⟩
              exact BindCallReference.canonical counts expanded
                signatureAllocator expansionAllocator finalAllocator result
                signaturePost expansionPost callPost.symm canonicalPost

theorem list_map_injective_of_injective
    {alpha beta : Type} (view : alpha → beta)
    (viewInjective : Function.Injective view) :
    Function.Injective (List.map view) := by
  intro left right equal
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => simp at equal
      | cons otherHead otherTail =>
          simp only [List.map_cons, List.cons.injEq] at equal
          rw [viewInjective equal.1]
          rw [inductionHypothesis equal.2]

theorem vec_eq_of_val_eq {alpha : Type}
    (left right : alloc.vec.Vec alpha) (equal : left.val = right.val) :
    left = right := by
  cases left
  cases right
  simp_all

theorem boundArgumentView_injective : Function.Injective boundArgumentView := by
  intro left right equal
  cases left <;> cases right <;>
    simp only [boundArgumentView] at equal
  all_goals try contradiction
  case SuppliedPositional.SuppliedPositional =>
    injection equal with argumentEqual
    rw [argumentEqual]
  case SuppliedNamed.SuppliedNamed =>
    injection equal with argumentEqual
    rw [argumentEqual]
  case Defaulted.Defaulted =>
    injection equal with argumentEqual
    rw [argumentEqual]
  case ResidualPositionals.ResidualPositionals leftValues rightValues =>
    injection equal with valuesEqual
    congr
    exact vec_eq_of_val_eq leftValues rightValues valuesEqual
  case ResidualKeywords.ResidualKeywords leftValues rightValues =>
    injection equal with valuesEqual
    congr
    exact vec_eq_of_val_eq leftValues rightValues valuesEqual

theorem bindingCellView_injective : Function.Injective bindingCellView := by
  intro left right equal
  rcases left with ⟨leftParameter, leftKind, leftArgument⟩
  rcases right with ⟨rightParameter, rightKind, rightArgument⟩
  simp only [bindingCellView] at equal
  injection equal with parameterEqual kindEqual argumentEqual
  congr
  exact boundArgumentView_injective argumentEqual

theorem bindingEnvironmentView_injective :
    Function.Injective bindingEnvironmentView := by
  intro left right equal
  rcases left with ⟨leftCells, leftEvaluation⟩
  rcases right with ⟨rightCells, rightEvaluation⟩
  simp only [bindingEnvironmentView] at equal
  injection equal with cellsEqual evaluationEqual
  have cellsVecEqual : leftCells = rightCells :=
    vec_eq_of_val_eq leftCells rightCells
      (list_map_injective_of_injective bindingCellView
        bindingCellView_injective cellsEqual)
  have evaluationVecEqual : leftEvaluation = rightEvaluation :=
    vec_eq_of_val_eq leftEvaluation rightEvaluation evaluationEqual
  cases leftCells
  cases rightCells
  cases leftEvaluation
  cases rightEvaluation
  simp_all

theorem bindingResultView_injective : Function.Injective bindingResultView := by
  intro left right equal
  cases left <;> cases right <;>
    simp only [bindingResultView] at equal
  all_goals try contradiction
  · congr
    exact bindingEnvironmentView_injective
      (core.result.Result.Ok.inj equal)
  · injection equal with errorEqual
    rw [errorEqual]

end BindCallFull.Proofs
