import BindCallFullProofs.Foundation

open Aeneas Aeneas.Std Result ControlFlow Error

namespace BindCallFull.Proofs

set_option linter.unusedVariables false

/- Compatibility name for retained loop invariants. This is the platform's full `usize` range,
not an application limit; successful checked additions establish the strict bounds needed by
each push. -/
def BindCallFull.USIZE_CAPACITY : Std.Usize := core.num.Usize.MAX

@[step]
theorem result_err_spec {T E : Type} (value : core.result.Result T E) :
    WP.spec (core.result.Result.err value) (fun output =>
      output = match value with | .Ok _ => none | .Err error => some error) := by
  rw [result_err_exact]
  rfl

def stringScanReference
    (names : Slice String) (candidate : String) (index : Std.Usize)
    (found : Bool) : Bool :=
  Bool.or found
    ((names.val.drop index.val).any (fun item => item == candidate))

def stringScanInvariant
    (names : Slice String) (candidate : String) (expected : Bool)
    (state : Std.Usize × Bool) : Prop :=
  state.1.val ≤ names.val.length ∧
    stringScanReference names candidate state.1 state.2 = expected

def stringScanRemaining (names : Slice String) (index : Std.Usize) : Nat :=
  names.val.length - index.val

theorem string_list_contains_body_preserves_reference_and_decreases
    (names : Slice String) (candidate : String) (expected : Bool)
    (state : Std.Usize × Bool)
    (invariant : stringScanInvariant names candidate expected state) :
    WP.spec
      (BindCallFull.string_list_contains_loop.body
        names candidate state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output = expected
        | .cont next =>
            stringScanInvariant names candidate expected next ∧
              stringScanRemaining names next.1 < stringScanRemaining names state.1) := by
  rcases state with ⟨index, found⟩
  unfold BindCallFull.string_list_contains_loop.body
  unfold stringScanInvariant stringScanReference at invariant
  unfold stringScanInvariant stringScanReference stringScanRemaining
  by_cases indexWithin : index < Slice.len names
  · simp only [indexWithin, if_true]
    by_cases alreadyFound : found = true
    · simp_all
    · have foundFalse : found = false := Bool.eq_false_of_not_eq_true alreadyFound
      simp [foundFalse]
      have natIndexBound : index.val < names.val.length := by
        simpa [Slice.len] using indexWithin
      step with Slice.index_usize_spec as ⟨currentName, currentNameEq⟩ by
        exact natIndexBound
      rw [string_eq_exact currentName candidate]
      simp
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        have machineBound : index.val + 1 ≤ Std.Usize.max := by
          have sliceBound := names.property
          omega
        exact machineBound
      have dropStep :
          names.val.drop index.val =
            names.val[index.val] :: names.val.drop (index.val + 1) :=
        List.drop_eq_getElem_cons natIndexBound
      have referenceStep := invariant.2
      rw [dropStep] at referenceStep
      simp only [foundFalse, List.any_cons] at referenceStep
      simp only [currentNameEq, nextIndexEq]
      exact ⟨by omega, referenceStep, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : names.val.length ≤ index.val := by
      simpa [Slice.len] using indexWithin
    simp_all

theorem string_list_contains_loop_matches_reference
    (names : Slice String) (candidate : String) (index : Std.Usize)
    (found : Bool) (indexBound : index.val ≤ names.val.length) :
    WP.spec (BindCallFull.string_list_contains_loop names candidate index found)
      (fun output => output = stringScanReference names candidate index found) := by
  let expected := stringScanReference names candidate index found
  have initialInvariant :
      stringScanInvariant names candidate expected (index, found) := by
    exact ⟨indexBound, rfl⟩
  unfold BindCallFull.string_list_contains_loop
  apply loop.spec_decr_nat
      (measure := fun state => stringScanRemaining names state.1)
      (inv := stringScanInvariant names candidate expected)
      (post := fun output => output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (string_list_contains_body_preserves_reference_and_decreases
      names candidate expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem string_list_contains_matches_reference
    (names : Slice String) (candidate : String) :
    WP.spec (BindCallFull.string_list_contains names candidate)
      (fun output =>
        output = names.val.any (fun item => item == candidate)) := by
  unfold BindCallFull.string_list_contains
  apply WP.spec_mono
    (string_list_contains_loop_matches_reference names candidate 0#usize false (by simp))
  intro output outputEq
  simpa [stringScanReference] using outputEq

def formalValidationView
    (output : core.result.Result Unit (BindCallFull.BindingError String) ×
      alloc.vec.Vec String) :
    core.result.Result Unit (BindCallFull.BindingError String) × List String :=
  (output.1, output.2.val)

def validateFormalReference
    (parameter : BindCallFull.FormalParameter String Int)
    (variadic : Bool) (names : List String) :
    core.result.Result Unit (BindCallFull.BindingError String) × List String :=
  if parameter.name.isEmpty then
    (.Err (.MalformedSignature .EmptyParameterName), names)
  else if names.any (fun item => item == parameter.name) then
    (.Err (.MalformedSignature (.DuplicateParameter parameter.name)), names)
  else
    let namesAfter := names ++ [parameter.name]
    if variadic && parameter.default_value.isSome then
      (.Err (.MalformedSignature (.VariadicDefault parameter.name)), namesAfter)
    else
      match parameter.default_value with
      | none => (.Ok (), namesAfter)
      | some default =>
          if parameter.expected_type == default.type_tag then
            (.Ok (), namesAfter)
          else
            (.Err (.MalformedSignature (.DefaultTypeMismatch parameter.name
              parameter.expected_type default.type_tag)), namesAfter)

theorem validateFormalReference_names_length
    (parameter : BindCallFull.FormalParameter String Int)
    (variadic : Bool) (names : List String) :
    (validateFormalReference parameter variadic names).2.length ≤ names.length + 1 := by
  unfold validateFormalReference
  grind

theorem validate_formal_parameter_string_exact
    (parameter : BindCallFull.FormalParameter String Int)
    (variadic : Bool) (names : alloc.vec.Vec String)
    (capacity : names.val.length < Std.Usize.max) :
    WP.spec
      (BindCallFull.validate_formal_parameter
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameter variadic names ())
      (fun output =>
        formalValidationView output =
          validateFormalReference parameter variadic names.val) := by
  unfold BindCallFull.validate_formal_parameter validateFormalReference
  rw [string_is_empty_exact]
  simp only
  by_cases emptyName : parameter.name.isEmpty = true
  · simp [emptyName, formalValidationView]
  · have nonemptyName : parameter.name.isEmpty = false :=
      Bool.eq_false_of_not_eq_true emptyName
    simp [nonemptyName]
    apply WP.spec_bind
    · exact string_list_contains_matches_reference names.deref parameter.name
    · intro duplicate duplicateEq
      simp only [duplicateEq]
      by_cases isDuplicate :
          names.val.any (fun item => item == parameter.name) = true
      · have member : parameter.name ∈ names.val := by
          simpa using isDuplicate
        have derefMember : parameter.name ∈ names.deref.val := by
          simpa [alloc.vec.Vec.deref] using member
        simp [member, derefMember, string_clone_exact, formalValidationView]
      · have isFresh :
            names.val.any (fun item => item == parameter.name) = false :=
          Bool.eq_false_of_not_eq_true isDuplicate
        have noEqual : ∀ item ∈ names.val, item ≠ parameter.name := by
          simpa using isFresh
        have notMember : parameter.name ∉ names.val := by
          intro member
          exact noEqual parameter.name member rfl
        have derefNotMember : parameter.name ∉ names.deref.val := by
          change parameter.name ∉ names.val
          exact notMember
        rw [string_clone_exact]
        simp [notMember, derefNotMember]
        step with alloc.vec.Vec.push_spec as ⟨namesAfter, namesAfterEq⟩ by
          exact capacity
        cases defaultEq : parameter.default_value with
        | none =>
            by_cases variadicTrue : variadic = true <;>
              simp_all [formalValidationView]
        | some default =>
            by_cases variadicTrue : variadic = true
            · simp_all [formalValidationView, string_clone_exact]
            · simp only [variadicTrue, if_false]
              simp [
                BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility.accepts,
                totalStringEq,
                alloc.string.String.Insts.CoreCmpPartialEqString.eq]
              by_cases typesEqual : parameter.expected_type = default.type_tag
              · simp_all [formalValidationView]
              · rw [totalIdentityClone_exact, totalIdentityClone_exact]
                simp_all [formalValidationView]

def validateFormalListReference :
    List (BindCallFull.FormalParameter String Int) →
      List String → Option (BindCallFull.BindingError String) →
      List String × Option (BindCallFull.BindingError String)
  | _, names, some error => (names, some error)
  | [], names, none => (names, none)
  | parameter :: remaining, names, none =>
      let output := validateFormalReference parameter false names
      match output.1 with
      | .Ok _ => validateFormalListReference remaining output.2 none
      | .Err error => (output.2, some error)

def validationLoopRemaining
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (index : Std.Usize) : Nat :=
  parameters.val.length - index.val

def validationOutputView
    (output : alloc.vec.Vec String ×
      Option (BindCallFull.BindingError String)) :
    List String × Option (BindCallFull.BindingError String) :=
  (output.1.val, output.2)

def validationLoopInvariant
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (expected : List String × Option (BindCallFull.BindingError String))
    (state : alloc.vec.Vec String × Std.Usize ×
      Option (BindCallFull.BindingError String)) : Prop :=
  state.2.1.val ≤ parameters.val.length ∧
    state.1.val.length + validationLoopRemaining parameters state.2.1 ≤
      Std.Usize.max ∧
    validateFormalListReference
      (parameters.val.drop state.2.1.val) state.1.val state.2.2 = expected

theorem validate_signature_loop0_body_preserves_reference_and_decreases
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (expected : List String × Option (BindCallFull.BindingError String))
    (state : alloc.vec.Vec String × Std.Usize ×
      Option (BindCallFull.BindingError String))
    (invariant : validationLoopInvariant parameters expected state) :
    WP.spec
      (BindCallFull.validate_signature_loop0.body
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters () state.1 state.2.1 state.2.2)
      (fun flow =>
        match flow with
        | .done output => validationOutputView output = expected
        | .cont next =>
            validationLoopInvariant parameters expected next ∧
              validationLoopRemaining parameters next.2.1 <
                validationLoopRemaining parameters state.2.1) := by
  rcases state with ⟨names, index, validationError⟩
  unfold BindCallFull.validate_signature_loop0.body
  unfold validationLoopInvariant validationLoopRemaining at invariant ⊢
  change index.val ≤ parameters.val.length ∧
      names.val.length + (parameters.val.length - index.val) ≤ Std.Usize.max ∧
      validateFormalListReference (parameters.val.drop index.val)
        names.val validationError = expected at invariant
  by_cases indexWithin : index < alloc.vec.Vec.len parameters
  · simp only [indexWithin, if_true]
    have natIndexBound : index.val < parameters.val.length := by
      simpa [alloc.vec.Vec.len] using indexWithin
    cases validationError with
    | some error =>
        simp
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have vectorBound := parameters.property
          omega
        simp only [nextIndexEq]
        exact ⟨by omega, by omega,
          by simpa [validateFormalListReference] using invariant.2.2,
          by omega⟩
    | none =>
        simp
        step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
          exact natIndexBound
        have namesCapacity : names.val.length < Std.Usize.max := by
          omega
        step with validate_formal_parameter_string_exact as
          ⟨validationOutput, validationEq⟩ by
            exact namesCapacity
        rcases validationOutput with ⟨validationResult, namesAfter⟩
        have namesAfterEq : namesAfter.val =
            (validateFormalReference parameter false names.val).2 :=
          congrArg Prod.snd validationEq
        have validationResultEq : validationResult =
            (validateFormalReference parameter false names.val).1 :=
          congrArg Prod.fst validationEq
        have namesAfterBound : namesAfter.val.length ≤ names.val.length + 1 := by
          rw [namesAfterEq]
          exact validateFormalReference_names_length parameter false names.val
        step with result_err_spec as
          ⟨validationErrorAfter, validationErrorAfterEq⟩
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have vectorBound := parameters.property
          omega
        have dropStep :
            parameters.val.drop index.val =
              parameters.val[index.val] :: parameters.val.drop (index.val + 1) :=
          List.drop_eq_getElem_cons natIndexBound
        have referenceStep := invariant.2.2
        rw [dropStep, ← parameterEq] at referenceStep
        have remainingStep :
            parameters.val.length - (index.val + 1) + 1 =
              parameters.val.length - index.val := by
          omega
        rcases invariant with ⟨indexBound, resourceBound, referenceEq⟩
        have nextResource :
            namesAfter.val.length +
              (parameters.val.length - (index.val + 1)) ≤ Std.Usize.max := by
          omega
        simp only [validateFormalListReference] at referenceStep
        cases validationResult with
        | Ok value =>
            rw [← validationResultEq] at referenceStep
            have nextReference :
                validateFormalListReference
                    (parameters.val.drop (index.val + 1)) namesAfter.val none =
                  expected := by
              simpa [namesAfterEq, validateFormalListReference] using referenceStep
            simp [nextIndexEq, validationErrorAfterEq]
            exact ⟨natIndexBound, nextResource, nextReference, by omega⟩
        | Err error =>
            rw [← validationResultEq] at referenceStep
            have nextReference :
                validateFormalListReference
                    (parameters.val.drop (index.val + 1)) namesAfter.val
                    (some error) = expected := by
              simpa [namesAfterEq, validateFormalListReference] using referenceStep
            simp [nextIndexEq, validationErrorAfterEq]
            exact ⟨natIndexBound, nextResource, nextReference, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : parameters.val.length ≤ index.val := by
      simpa [alloc.vec.Vec.len] using indexWithin
    have exactIndex : index.val = parameters.val.length := by omega
    have referenceEq := invariant.2.2
    rw [exactIndex, List.drop_length] at referenceEq
    cases validationError <;>
      simpa [validationOutputView, validateFormalListReference] using referenceEq

theorem validate_signature_loop0_matches_reference
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (names : alloc.vec.Vec String) (index : Std.Usize)
    (validationError : Option (BindCallFull.BindingError String))
    (indexBound : index.val ≤ parameters.val.length)
    (resourceBound :
      names.val.length + validationLoopRemaining parameters index ≤ Std.Usize.max) :
    WP.spec
      (BindCallFull.validate_signature_loop0
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters () names index validationError)
      (fun output =>
        validationOutputView output = validateFormalListReference
          (parameters.val.drop index.val) names.val validationError) := by
  let expected := validateFormalListReference
    (parameters.val.drop index.val) names.val validationError
  have initialInvariant :
      validationLoopInvariant parameters expected (names, index, validationError) :=
    ⟨indexBound, resourceBound, rfl⟩
  unfold BindCallFull.validate_signature_loop0
  apply loop.spec_decr_nat
      (measure := fun state => validationLoopRemaining parameters state.2.1)
      (inv := validationLoopInvariant parameters expected)
      (post := fun (output : alloc.vec.Vec String ×
        Option (BindCallFull.BindingError String)) =>
          validationOutputView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (validate_signature_loop0_body_preserves_reference_and_decreases
      parameters expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem validate_signature_loop1_eq_loop0
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (names : alloc.vec.Vec String) (index : Std.Usize)
    (validationError : Option (BindCallFull.BindingError String)) :
    BindCallFull.validate_signature_loop1
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters () names index validationError =
      BindCallFull.validate_signature_loop0
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters () names index validationError := by
  unfold BindCallFull.validate_signature_loop1 BindCallFull.validate_signature_loop0
  congr 1

theorem validate_signature_loop2_eq_loop0
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (names : alloc.vec.Vec String) (index : Std.Usize)
    (validationError : Option (BindCallFull.BindingError String)) :
    BindCallFull.validate_signature_loop2
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters () names index validationError =
      BindCallFull.validate_signature_loop0
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters () names index validationError := by
  unfold BindCallFull.validate_signature_loop2 BindCallFull.validate_signature_loop0
  congr 1

theorem validate_signature_loop1_matches_reference
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (names : alloc.vec.Vec String) (index : Std.Usize)
    (validationError : Option (BindCallFull.BindingError String))
    (indexBound : index.val ≤ parameters.val.length)
    (resourceBound :
      names.val.length + validationLoopRemaining parameters index ≤ Std.Usize.max) :
    WP.spec
      (BindCallFull.validate_signature_loop1
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters () names index validationError)
      (fun output =>
        validationOutputView output = validateFormalListReference
          (parameters.val.drop index.val) names.val validationError) := by
  rw [validate_signature_loop1_eq_loop0]
  exact validate_signature_loop0_matches_reference
    parameters names index validationError indexBound resourceBound

theorem validate_signature_loop2_matches_reference
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (names : alloc.vec.Vec String) (index : Std.Usize)
    (validationError : Option (BindCallFull.BindingError String))
    (indexBound : index.val ≤ parameters.val.length)
    (resourceBound :
      names.val.length + validationLoopRemaining parameters index ≤ Std.Usize.max) :
    WP.spec
      (BindCallFull.validate_signature_loop2
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters () names index validationError)
      (fun output =>
        validationOutputView output = validateFormalListReference
          (parameters.val.drop index.val) names.val validationError) := by
  rw [validate_signature_loop2_eq_loop0]
  exact validate_signature_loop0_matches_reference
    parameters names index validationError indexBound resourceBound

theorem validateFormalListReference_names_length
    (parameters : List (BindCallFull.FormalParameter String Int))
    (names : List String)
    (validationError : Option (BindCallFull.BindingError String)) :
    (validateFormalListReference parameters names validationError).1.length ≤
      names.length + parameters.length := by
  induction parameters generalizing names validationError with
  | nil => cases validationError <;> simp [validateFormalListReference]
  | cons parameter remaining inductionHypothesis =>
      cases validationError with
      | some error => simp [validateFormalListReference]
      | none =>
          simp only [validateFormalListReference]
          generalize hOutput : validateFormalReference parameter false names =
            output
          rcases output with ⟨result, namesAfter⟩
          have headBound : namesAfter.length ≤ names.length + 1 := by
            have outputBound := validateFormalReference_names_length
              parameter false names
            have namesEq := congrArg Prod.snd hOutput
            change (validateFormalReference parameter false names).2 =
              namesAfter at namesEq
            rw [← namesEq]
            exact outputBound
          cases result with
          | Err error =>
              change namesAfter.length ≤
                names.length + (parameter :: remaining).length
              simp only [List.length_cons]
              omega
          | Ok value =>
              have tailBound := inductionHypothesis namesAfter none
              change (validateFormalListReference remaining namesAfter none).1.length ≤
                names.length + (parameter :: remaining).length
              simp only [List.length_cons]
              omega

/- The former fixed-cap signature reference and its top-level theorem are intentionally retired.
They are replaced by the checked-arithmetic, allocator-parametric reference in Composition.lean. -/
/-
def signatureParameterCount
    (signature : BindCallFull.CallSignature String Int) : Std.Usize :=
  let ordinary := core.num.Usize.saturating_add
    (core.num.Usize.saturating_add (alloc.vec.Vec.len signature.positional_only)
      (alloc.vec.Vec.len signature.positional))
    (alloc.vec.Vec.len signature.keyword_only)
  let withVarargs := core.num.Usize.saturating_add ordinary
    (core.convert.num.FromUsizeBool.from signature.var_args.isSome)
  core.num.Usize.saturating_add withVarargs
    (core.convert.num.FromUsizeBool.from signature.keyword_args.isSome)

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

def validateSignatureReference
    (signature : BindCallFull.CallSignature String Int) :
    core.result.Result Unit (BindCallFull.BindingError String) :=
  let parameterCount := signatureParameterCount signature
  if parameterCount > BindCallFull.USIZE_CAPACITY then
    .Err (.MalformedSignature (.ParameterLimitExceeded
      BindCallFull.USIZE_CAPACITY parameterCount))
  else
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
            | none => validateVariadicsReference signature keywordOnly.1

theorem saturating_add_within_small_limit_raw
    (left right limit : Std.Usize)
    (limitStrict : limit.val < Std.Usize.max)
    (withinLimit : (UScalar.saturating_add left right).val ≤ limit.val) :
    left.val + right.val ≤ limit.val := by
  have saturatingEq : (UScalar.saturating_add left right).val =
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
  rw [saturatingEq] at withinLimit
  by_cases rawFits : left.val + right.val ≤ Std.Usize.max
  · rw [Nat.min_eq_right rawFits] at withinLimit
    exact withinLimit
  · rw [Nat.min_eq_left (Nat.le_of_not_ge rawFits)] at withinLimit
    omega

theorem saturating_add_exact_of_sum_lt_max
    (left right : Std.Usize)
    (sumStrict : left.val + right.val < Std.Usize.max) :
    (UScalar.saturating_add left right).val = left.val + right.val := by
  change left.bv.toNat + right.bv.toNat < Std.Usize.max at sumStrict
  unfold UScalar.saturating_add UScalar.val
  rw [UScalar.max_USize_eq, BitVec.toNat_ofNat]
  have maxSucc := Std.Usize.max_succ_eq_pow
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.min_eq_right (Nat.le_of_lt sumStrict)]
  · change min Std.Usize.max (left.bv.toNat + right.bv.toNat) <
      2 ^ System.Platform.numBits
    rw [← maxSucc]
    exact Nat.lt_succ_of_le
      (Nat.min_le_left Std.Usize.max (left.bv.toNat + right.bv.toNat))

theorem signatureParameterCount_within_limit_bounds_raw
    (signature : BindCallFull.CallSignature String Int)
    (withinLimit : signatureParameterCount signature ≤
      BindCallFull.USIZE_CAPACITY) :
    signature.positional_only.val.length + signature.positional.val.length +
        signature.keyword_only.val.length +
        (core.convert.num.FromUsizeBool.from signature.var_args.isSome).val +
        (core.convert.num.FromUsizeBool.from signature.keyword_args.isSome).val ≤
      BindCallFull.USIZE_CAPACITY.val := by
  have maximumStrict : BindCallFull.USIZE_CAPACITY.val <
      Std.Usize.max := by
    have concreteBound := Std.Usize.cMax_bound_concrete.1
    simp [BindCallFull.USIZE_CAPACITY] at concreteBound ⊢
    omega
  let positionalCount := UScalar.saturating_add
    (alloc.vec.Vec.len signature.positional_only)
    (alloc.vec.Vec.len signature.positional)
  let ordinaryCount := UScalar.saturating_add positionalCount
    (alloc.vec.Vec.len signature.keyword_only)
  let withVarargs := UScalar.saturating_add ordinaryCount
    (core.convert.num.FromUsizeBool.from signature.var_args.isSome)
  have finalRaw := saturating_add_within_small_limit_raw withVarargs
    (core.convert.num.FromUsizeBool.from signature.keyword_args.isSome)
    BindCallFull.USIZE_CAPACITY maximumStrict (by
      simpa [signatureParameterCount, positionalCount, ordinaryCount,
        withVarargs, core.num.Usize.saturating_add] using withinLimit)
  have withVarargsBound : withVarargs.val ≤
      BindCallFull.USIZE_CAPACITY.val := by omega
  have varargsRaw := saturating_add_within_small_limit_raw ordinaryCount
    (core.convert.num.FromUsizeBool.from signature.var_args.isSome)
    BindCallFull.USIZE_CAPACITY maximumStrict withVarargsBound
  have ordinaryBound : ordinaryCount.val ≤
      BindCallFull.USIZE_CAPACITY.val := by omega
  have ordinaryRaw := saturating_add_within_small_limit_raw positionalCount
    (alloc.vec.Vec.len signature.keyword_only)
    BindCallFull.USIZE_CAPACITY maximumStrict ordinaryBound
  have positionalBound : positionalCount.val ≤
      BindCallFull.USIZE_CAPACITY.val := by omega
  have positionalRaw := saturating_add_within_small_limit_raw
    (alloc.vec.Vec.len signature.positional_only)
    (alloc.vec.Vec.len signature.positional)
    BindCallFull.USIZE_CAPACITY maximumStrict positionalBound
  have ordinaryRaw' : positionalCount.val +
      signature.keyword_only.val.length ≤
        BindCallFull.USIZE_CAPACITY.val := by
    simpa [alloc.vec.Vec.length] using ordinaryRaw
  have positionalRaw' : signature.positional_only.val.length +
      signature.positional.val.length ≤
        BindCallFull.USIZE_CAPACITY.val := by
    simpa [alloc.vec.Vec.length] using positionalRaw
  have positionalExact : positionalCount.val =
      signature.positional_only.val.length +
        signature.positional.val.length := by
    unfold positionalCount
    rw [saturating_add_exact_of_sum_lt_max]
    · simp [alloc.vec.Vec.length]
    · simp [alloc.vec.Vec.length]
      omega
  have ordinaryExact : ordinaryCount.val = positionalCount.val +
      signature.keyword_only.val.length := by
    unfold ordinaryCount
    rw [saturating_add_exact_of_sum_lt_max]
    · simp [alloc.vec.Vec.length]
    · simpa [alloc.vec.Vec.length] using
        (lt_of_le_of_lt ordinaryRaw maximumStrict)
  have varargsExact : withVarargs.val = ordinaryCount.val +
      (core.convert.num.FromUsizeBool.from signature.var_args.isSome).val := by
    unfold withVarargs
    apply saturating_add_exact_of_sum_lt_max
    exact lt_of_le_of_lt varargsRaw maximumStrict
  omega

theorem validate_signature_matches_exact_reference
    (signature : BindCallFull.CallSignature String Int) :
    WP.spec
      (BindCallFull.validate_signature (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature ())
      (fun output => output = validateSignatureReference signature) := by
  unfold BindCallFull.validate_signature
  simp [Aeneas.Std.lift]
  unfold validateSignatureReference signatureParameterCount
  split <;> rename_i parameterGate
  · simp_all [WP.spec, WP.theta, WP.wp_return]
  · have rawBound := signatureParameterCount_within_limit_bounds_raw
      signature (Nat.le_of_not_gt parameterGate)
    have maximumStrict : BindCallFull.USIZE_CAPACITY.val <
        Std.Usize.max := by
      have concreteBound := Std.Usize.cMax_bound_concrete.1
      simp [BindCallFull.USIZE_CAPACITY] at concreteBound ⊢
      omega
    simp only [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
    apply WP.spec_bind
    · exact validate_signature_loop0_matches_reference
        signature.positional_only (alloc.vec.Vec.new String) 0#usize none
        (by simp) (by
          unfold validationLoopRemaining
          simp
          omega)
    · intro positionalOnlyOutput positionalOnlyEq
      rcases positionalOnlyOutput with
        ⟨namesAfterPositionalOnly, positionalOnlyError⟩
      have positionalOnlyNamesEq : namesAfterPositionalOnly.val =
          (validateFormalListReference signature.positional_only.val [] none).1 :=
        congrArg Prod.fst positionalOnlyEq
      have positionalOnlyErrorEq : positionalOnlyError =
          (validateFormalListReference signature.positional_only.val [] none).2 :=
        congrArg Prod.snd positionalOnlyEq
      rw [← positionalOnlyErrorEq]
      rw [← positionalOnlyNamesEq]
      cases hPositionalOnlyError : positionalOnlyError with
      | some error =>
          simp [WP.spec, WP.theta, WP.wp_return]
          intro oversized
          exact (parameterGate oversized).elim
      | none =>
          simp only
          apply WP.spec_bind
          · exact validate_signature_loop1_matches_reference
              signature.positional namesAfterPositionalOnly 0#usize none
              (by simp) (by
                unfold validationLoopRemaining
                change namesAfterPositionalOnly.val.length +
                    (signature.positional.val.length - 0) < Std.Usize.max
                simp only [Nat.sub_zero]
                have namesBound := validateFormalListReference_names_length
                  signature.positional_only.val [] none
                simp at namesBound
                rw [positionalOnlyNamesEq]
                omega)
          · intro positionalOutput positionalEq
            rcases positionalOutput with
              ⟨namesAfterPositional, positionalError⟩
            have positionalNamesEq : namesAfterPositional.val =
                (validateFormalListReference signature.positional.val
                  namesAfterPositionalOnly.val none).1 :=
              congrArg Prod.fst positionalEq
            have positionalErrorEq : positionalError =
                (validateFormalListReference signature.positional.val
                  namesAfterPositionalOnly.val none).2 :=
              congrArg Prod.snd positionalEq
            rw [← positionalErrorEq]
            rw [← positionalNamesEq]
            cases hPositionalError : positionalError with
            | some error =>
                simp [WP.spec, WP.theta, WP.wp_return]
                intro oversized
                exact (parameterGate oversized).elim
            | none =>
                simp only
                apply WP.spec_bind
                · exact validate_signature_loop2_matches_reference
                    signature.keyword_only namesAfterPositional 0#usize none
                    (by simp) (by
                      unfold validationLoopRemaining
                      change namesAfterPositional.val.length +
                          (signature.keyword_only.val.length - 0) <
                        Std.Usize.max
                      simp only [Nat.sub_zero]
                      have positionalOnlyNamesBound :=
                        validateFormalListReference_names_length
                          signature.positional_only.val [] none
                      simp at positionalOnlyNamesBound
                      have positionalNamesBound :=
                        validateFormalListReference_names_length
                          signature.positional.val
                          namesAfterPositionalOnly.val none
                      have positionalOnlyOutputBound :
                          namesAfterPositionalOnly.val.length ≤
                            signature.positional_only.val.length := by
                        rw [positionalOnlyNamesEq]
                        exact positionalOnlyNamesBound
                      rw [positionalNamesEq]
                      omega)
                · intro keywordOnlyOutput keywordOnlyEq
                  rcases keywordOnlyOutput with
                    ⟨namesAfterKeywordOnly, keywordOnlyError⟩
                  have keywordOnlyNamesEq : namesAfterKeywordOnly.val =
                      (validateFormalListReference signature.keyword_only.val
                        namesAfterPositional.val none).1 :=
                    congrArg Prod.fst keywordOnlyEq
                  have keywordOnlyErrorEq : keywordOnlyError =
                      (validateFormalListReference signature.keyword_only.val
                        namesAfterPositional.val none).2 :=
                    congrArg Prod.snd keywordOnlyEq
                  rw [← keywordOnlyErrorEq]
                  rw [← keywordOnlyNamesEq]
                  cases hKeywordOnlyError : keywordOnlyError with
                  | some error =>
                      simp [WP.spec, WP.theta, WP.wp_return]
                      intro oversized
                      exact (parameterGate oversized).elim
                  | none =>
                      simp only
                      have positionalOnlyNamesBound :=
                        validateFormalListReference_names_length
                          signature.positional_only.val [] none
                      simp at positionalOnlyNamesBound
                      have positionalOnlyOutputBound :
                          namesAfterPositionalOnly.val.length ≤
                            signature.positional_only.val.length := by
                        rw [positionalOnlyNamesEq]
                        exact positionalOnlyNamesBound
                      have positionalNamesBound :=
                        validateFormalListReference_names_length
                          signature.positional.val
                          namesAfterPositionalOnly.val none
                      have positionalOutputBound :
                          namesAfterPositional.val.length ≤
                            signature.positional_only.val.length +
                              signature.positional.val.length := by
                        rw [positionalNamesEq]
                        omega
                      have keywordOnlyNamesBound :=
                        validateFormalListReference_names_length
                          signature.keyword_only.val
                          namesAfterPositional.val none
                      have keywordOnlyCapacity :
                          namesAfterKeywordOnly.val.length < Std.Usize.max := by
                        rw [keywordOnlyNamesEq]
                        omega
                      cases hVarargs : signature.var_args with
                      | none =>
                          cases hKeywordArgs : signature.keyword_args with
                          | none =>
                              have parameterWithin :
                                  signatureParameterCount signature ≤
                                    BindCallFull.USIZE_CAPACITY :=
                                Nat.le_of_not_gt parameterGate
                              simpa [validateVariadicsReference, hVarargs,
                                hKeywordArgs, signatureParameterCount,
                                WP.spec, WP.theta, WP.wp_return] using
                                  parameterWithin
                          | some keywordParameter =>
                              apply WP.spec_bind
                              · exact validate_formal_parameter_string_exact
                                  keywordParameter true namesAfterKeywordOnly
                                  keywordOnlyCapacity
                              · intro keywordOutput keywordEq
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
                                      validateVariadicsReference, hVarargs,
                                      hKeywordArgs,
                                      core.result.Result.Insts.CoreOpsTry.branch,
                                      WP.spec, WP.theta, WP.wp_return]
                                    have parameterWithin :
                                        signatureParameterCount signature ≤
                                          BindCallFull.USIZE_CAPACITY :=
                                      Nat.le_of_not_gt parameterGate
                                    simpa [signatureParameterCount, hVarargs,
                                      hKeywordArgs] using parameterWithin
                                | Err error =>
                                    have keywordErr : keywordResult = .Err error := by
                                      rw [keywordResultEq, hKeywordReference]
                                    simp [keywordErr, hKeywordReference,
                                      validateVariadicsReference, hVarargs,
                                      hKeywordArgs,
                                      core.result.Result.Insts.CoreOpsTry.branch,
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                      WP.spec, WP.theta, WP.wp_return]
                                    intro oversized
                                    have parameterWithin :
                                        signatureParameterCount signature ≤
                                          BindCallFull.USIZE_CAPACITY :=
                                      Nat.le_of_not_gt parameterGate
                                    have specializedWithin :
                                        (core.num.Usize.saturating_add
                                          (core.num.Usize.saturating_add
                                            (core.num.Usize.saturating_add
                                              (core.num.Usize.saturating_add
                                                (alloc.vec.Vec.len signature.positional_only)
                                                (alloc.vec.Vec.len signature.positional))
                                              (alloc.vec.Vec.len signature.keyword_only))
                                            (core.convert.num.FromUsizeBool.from false))
                                          (core.convert.num.FromUsizeBool.from true)).val ≤
                                            BindCallFull.USIZE_CAPACITY.val := by
                                      simpa [signatureParameterCount, hVarargs,
                                        hKeywordArgs] using parameterWithin
                                    simp [alloc.vec.Vec.len] at specializedWithin
                                    omega
                      | some varParameter =>
                          apply WP.spec_bind
                          · exact validate_formal_parameter_string_exact
                              varParameter true namesAfterKeywordOnly
                              keywordOnlyCapacity
                          · intro varOutput varEq
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
                                simp [varErr, hVarReference,
                                  validateVariadicsReference, hVarargs,
                                  core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  WP.spec, WP.theta, WP.wp_return]
                                intro oversized
                                have parameterWithin :
                                    signatureParameterCount signature ≤
                                      BindCallFull.USIZE_CAPACITY :=
                                  Nat.le_of_not_gt parameterGate
                                have specializedWithin :
                                    (signatureParameterCount signature).val ≤
                                      BindCallFull.USIZE_CAPACITY.val := by
                                  exact parameterWithin
                                simp [signatureParameterCount, hVarargs,
                                  alloc.vec.Vec.len] at specializedWithin
                                omega
                            | Ok value =>
                                have varOk : varResult = .Ok value := by
                                  rw [varResultEq, hVarReference]
                                simp only [varOk,
                                  core.result.Result.Insts.CoreOpsTry.branch]
                                cases hKeywordArgs : signature.keyword_args with
                                | none =>
                                    simp [hVarReference,
                                      validateVariadicsReference, hVarargs,
                                      hKeywordArgs, WP.spec, WP.theta,
                                      WP.wp_return]
                                    have parameterWithin :
                                        signatureParameterCount signature ≤
                                          BindCallFull.USIZE_CAPACITY :=
                                      Nat.le_of_not_gt parameterGate
                                    simpa [signatureParameterCount, hVarargs,
                                      hKeywordArgs] using parameterWithin
                                | some keywordParameter =>
                                    have varNamesBound :=
                                      validateFormalReference_names_length
                                        varParameter true
                                        namesAfterKeywordOnly.val
                                    have keywordOnlyOutputBound :
                                        namesAfterKeywordOnly.val.length ≤
                                          signature.positional_only.val.length +
                                            signature.positional.val.length +
                                            signature.keyword_only.val.length := by
                                      rw [keywordOnlyNamesEq]
                                      omega
                                    have specializedRawBound :
                                        signature.positional_only.val.length +
                                              signature.positional.val.length +
                                              signature.keyword_only.val.length + 1 + 1 ≤
                                          BindCallFull.USIZE_CAPACITY.val := by
                                      have bound := rawBound
                                      simp [hVarargs, hKeywordArgs,
                                        core.convert.num.FromUsizeBool.from] at bound
                                      omega
                                    have keywordCapacity :
                                        namesAfterVar.val.length <
                                          Std.Usize.max := by
                                      rw [varNamesEq]
                                      have maximumStrict' :
                                          BindCallFull.USIZE_CAPACITY.val <
                                            Std.Usize.max := maximumStrict
                                      omega
                                    apply WP.spec_bind
                                    · exact validate_formal_parameter_string_exact
                                        keywordParameter true namesAfterVar
                                        keywordCapacity
                                    · intro keywordOutput keywordEq
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
                                          have specializedGate :
                                              ¬BindCallFull.USIZE_CAPACITY.val <
                                                (core.num.Usize.saturating_add
                                                  (core.num.Usize.saturating_add
                                                    (core.num.Usize.saturating_add
                                                      (core.num.Usize.saturating_add
                                                        (alloc.vec.Vec.len signature.positional_only)
                                                        (alloc.vec.Vec.len signature.positional))
                                                      (alloc.vec.Vec.len signature.keyword_only))
                                                    (core.convert.num.FromUsizeBool.from true))
                                                  (core.convert.num.FromUsizeBool.from true)).val := by
                                            simpa [hVarargs, hKeywordArgs] using parameterGate
                                          simp [keywordOk, hKeywordReference,
                                            hVarReference,
                                            validateVariadicsReference,
                                            hVarargs, hKeywordArgs,
                                            specializedGate,
                                            core.result.Result.Insts.CoreOpsTry.branch,
                                            WP.spec, WP.theta, WP.wp_return]
                                          rw [← varNamesEq]
                                          cases keywordValue
                                          exact hKeywordReference.symm
                                      | Err keywordError =>
                                          have keywordErr : keywordResult =
                                              .Err keywordError := by
                                            rw [keywordResultEq,
                                              hKeywordReference]
                                          have specializedGate :
                                              ¬BindCallFull.USIZE_CAPACITY.val <
                                                (core.num.Usize.saturating_add
                                                  (core.num.Usize.saturating_add
                                                    (core.num.Usize.saturating_add
                                                      (core.num.Usize.saturating_add
                                                        (alloc.vec.Vec.len signature.positional_only)
                                                        (alloc.vec.Vec.len signature.positional))
                                                      (alloc.vec.Vec.len signature.keyword_only))
                                                    (core.convert.num.FromUsizeBool.from true))
                                                  (core.convert.num.FromUsizeBool.from true)).val := by
                                            simpa [hVarargs, hKeywordArgs] using parameterGate
                                          simp [keywordErr, hKeywordReference,
                                            hVarReference,
                                            validateVariadicsReference,
                                            hVarargs, hKeywordArgs,
                                            specializedGate,
                                            core.result.Result.Insts.CoreOpsTry.branch,
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                            WP.spec, WP.theta, WP.wp_return]
                                          rw [← varNamesEq]
                                          exact hKeywordReference.symm

-/

def formalNameScanReference {value : Type}
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String value))
    (candidate : String) (index : Std.Usize) (found : Bool) : Bool :=
  Bool.or found ((parameters.val.drop index.val).any
    (fun parameter => parameter.name == candidate))

def formalNameScanRemaining {value : Type}
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String value))
    (index : Std.Usize) : Nat :=
  parameters.val.length - index.val

def formalNameScanInvariant {value : Type}
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String value))
    (candidate : String) (expected : Bool)
    (state : Bool × Std.Usize) : Prop :=
  state.2.val ≤ parameters.val.length ∧
    formalNameScanReference parameters candidate state.2 state.1 = expected

theorem ordinary_parameter_name_loop1_body_preserves_reference_and_decreases
    {value : Type}
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String value))
    (candidate : String) (expected : Bool) (state : Bool × Std.Usize)
    (invariant : formalNameScanInvariant parameters candidate expected state) :
    WP.spec
      (BindCallFull.ordinary_parameter_name_loop1.body
        parameters candidate state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output = expected
        | .cont next =>
            formalNameScanInvariant parameters candidate expected next ∧
              formalNameScanRemaining parameters next.2 <
                formalNameScanRemaining parameters state.2) := by
  rcases state with ⟨found, index⟩
  unfold BindCallFull.ordinary_parameter_name_loop1.body
  unfold formalNameScanInvariant formalNameScanReference at invariant
  unfold formalNameScanInvariant formalNameScanReference formalNameScanRemaining
  by_cases indexWithin : index < alloc.vec.Vec.len parameters
  · simp only [indexWithin, if_true]
    by_cases alreadyFound : found = true
    · simp_all
    · have foundFalse : found = false := Bool.eq_false_of_not_eq_true alreadyFound
      simp [foundFalse]
      have natIndexBound : index.val < parameters.val.length := by
        simpa [alloc.vec.Vec.len] using indexWithin
      step with alloc.vec.Vec.index_usize_spec as
        ⟨parameter, parameterEq⟩ by exact natIndexBound
      rw [string_eq_exact parameter.name candidate]
      simp
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        have vectorBound := parameters.property
        omega
      have dropStep :
          parameters.val.drop index.val =
            parameters.val[index.val] :: parameters.val.drop (index.val + 1) :=
        List.drop_eq_getElem_cons natIndexBound
      have referenceStep := invariant.2
      rw [dropStep] at referenceStep
      simp only [foundFalse, List.any_cons] at referenceStep
      simp only [parameterEq, nextIndexEq]
      exact ⟨by omega, referenceStep, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : parameters.val.length ≤ index.val := by
      simpa [alloc.vec.Vec.len] using indexWithin
    simp_all

theorem ordinary_parameter_name_loop1_matches_reference
    {value : Type}
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String value))
    (candidate : String) (found : Bool) (index : Std.Usize)
    (indexBound : index.val ≤ parameters.val.length) :
    WP.spec
      (BindCallFull.ordinary_parameter_name_loop1
        parameters candidate found index)
      (fun output =>
        output = formalNameScanReference parameters candidate index found) := by
  let expected := formalNameScanReference parameters candidate index found
  have initialInvariant :
      formalNameScanInvariant parameters candidate expected (found, index) :=
    ⟨indexBound, rfl⟩
  unfold BindCallFull.ordinary_parameter_name_loop1
  apply loop.spec_decr_nat
      (measure := fun state => formalNameScanRemaining parameters state.2)
      (inv := formalNameScanInvariant parameters candidate expected)
      (post := fun output => output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (ordinary_parameter_name_loop1_body_preserves_reference_and_decreases
      parameters candidate expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

def ordinaryFirstLoopInvariant {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (candidate : String) (expected : Bool)
    (state : Std.Usize × Bool) : Prop :=
  state.1.val ≤ signature.positional.val.length ∧
    formalNameScanReference signature.positional candidate state.1 state.2 = expected

theorem ordinary_parameter_name_loop0_body_preserves_reference_and_decreases
    {value : Type} (signature : BindCallFull.CallSignature String value)
    (candidate : String) (expected : Bool) (state : Std.Usize × Bool)
    (invariant : ordinaryFirstLoopInvariant signature candidate expected state) :
    WP.spec
      (BindCallFull.ordinary_parameter_name_loop0.body
        signature candidate state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output.1 = signature.keyword_only ∧ output.2 = expected
        | .cont next =>
            ordinaryFirstLoopInvariant signature candidate expected next ∧
              formalNameScanRemaining signature.positional next.1 <
                formalNameScanRemaining signature.positional state.1) := by
  rcases state with ⟨index, found⟩
  unfold BindCallFull.ordinary_parameter_name_loop0.body
  unfold ordinaryFirstLoopInvariant formalNameScanReference at invariant
  unfold ordinaryFirstLoopInvariant formalNameScanReference formalNameScanRemaining
  by_cases indexWithin : index < alloc.vec.Vec.len signature.positional
  · simp only [indexWithin, if_true]
    by_cases alreadyFound : found = true
    · simp_all
    · have foundFalse : found = false := Bool.eq_false_of_not_eq_true alreadyFound
      simp [foundFalse]
      have natIndexBound : index.val < signature.positional.val.length := by
        simpa [alloc.vec.Vec.len] using indexWithin
      step with alloc.vec.Vec.index_usize_spec as
        ⟨parameter, parameterEq⟩ by exact natIndexBound
      rw [string_eq_exact parameter.name candidate]
      simp
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        have vectorBound := signature.positional.property
        omega
      have dropStep :
          signature.positional.val.drop index.val =
            signature.positional.val[index.val] ::
              signature.positional.val.drop (index.val + 1) :=
        List.drop_eq_getElem_cons natIndexBound
      have referenceStep := invariant.2
      rw [dropStep] at referenceStep
      simp only [foundFalse, List.any_cons] at referenceStep
      simp only [parameterEq, nextIndexEq]
      exact ⟨by omega, referenceStep, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : signature.positional.val.length ≤ index.val := by
      simpa [alloc.vec.Vec.len] using indexWithin
    simp_all

theorem ordinary_parameter_name_loop0_matches_reference
    {value : Type} (signature : BindCallFull.CallSignature String value)
    (candidate : String) (index : Std.Usize) (found : Bool)
    (indexBound : index.val ≤ signature.positional.val.length) :
    WP.spec
      (BindCallFull.ordinary_parameter_name_loop0 signature candidate index found)
      (fun output =>
        output.1 = signature.keyword_only ∧
          output.2 = formalNameScanReference
            signature.positional candidate index found) := by
  let expected := formalNameScanReference signature.positional candidate index found
  have initialInvariant :
      ordinaryFirstLoopInvariant signature candidate expected (index, found) :=
    ⟨indexBound, rfl⟩
  unfold BindCallFull.ordinary_parameter_name_loop0
  apply loop.spec_decr_nat
      (measure := fun state =>
        formalNameScanRemaining signature.positional state.1)
      (inv := ordinaryFirstLoopInvariant signature candidate expected)
      (post := fun (output : alloc.vec.Vec
        (BindCallFull.FormalParameter String value) × Bool) =>
        output.1 = signature.keyword_only ∧ output.2 = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (ordinary_parameter_name_loop0_body_preserves_reference_and_decreases
      signature candidate expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem ordinary_parameter_name_matches_reference
    {value : Type} (signature : BindCallFull.CallSignature String value)
    (candidate : String) :
    WP.spec (BindCallFull.ordinary_parameter_name signature candidate)
      (fun output => output = Bool.or
        (signature.positional.val.any
          (fun parameter => parameter.name == candidate))
        (signature.keyword_only.val.any
          (fun parameter => parameter.name == candidate))) := by
  unfold BindCallFull.ordinary_parameter_name
  apply WP.spec_bind
  · exact ordinary_parameter_name_loop0_matches_reference
      signature candidate 0#usize false (by simp)
  · rintro ⟨keywordOnly, positionalFound⟩ outputEq
    rcases outputEq with ⟨keywordOnlyEq, positionalFoundEq⟩
    change keywordOnly = signature.keyword_only at keywordOnlyEq
    change positionalFound = formalNameScanReference
      signature.positional candidate 0#usize false at positionalFoundEq
    apply WP.spec_mono
      (ordinary_parameter_name_loop1_matches_reference
        keywordOnly candidate positionalFound 0#usize (by simp))
    intro output outputEq
    have keywordValuesEq : keywordOnly.val = signature.keyword_only.val :=
      congrArg Subtype.val keywordOnlyEq
    simpa [formalNameScanReference, positionalFoundEq, keywordValuesEq,
      Bool.or_assoc] using outputEq

def namedActualScanReference {value : Type}
    (remaining : List (BindCallFull.NamedActual String value))
    (candidate : String) (index : Nat) (found : Bool) : Nat × Bool :=
  if found then
    (index, true)
  else
    match remaining with
    | [] => (index, false)
    | actual :: tail =>
        if actual.name == candidate then
          (index + 1, true)
        else
          namedActualScanReference tail candidate (index + 1) false
termination_by remaining.length

@[simp]
theorem namedActualScanReference_found_true {value : Type}
    (remaining : List (BindCallFull.NamedActual String value))
    (candidate : String) (index : Nat) :
    namedActualScanReference remaining candidate index true = (index, true) := by
  cases remaining <;>
    simp [namedActualScanReference.eq_1, namedActualScanReference.eq_2]

@[simp]
theorem namedActualScanReference_empty {value : Type}
    (candidate : String) (index : Nat) (found : Bool) :
    namedActualScanReference
      ([] : List (BindCallFull.NamedActual String value)) candidate index found =
        (index, found) := by
  cases found <;> simp [namedActualScanReference.eq_1]

@[simp]
theorem namedActualScanReference_cons_false {value : Type}
    (actual : BindCallFull.NamedActual String value)
    (tail : List (BindCallFull.NamedActual String value))
    (candidate : String) (index : Nat) :
    namedActualScanReference (actual :: tail) candidate index false =
      if actual.name == candidate then
        (index + 1, true)
      else
        namedActualScanReference tail candidate (index + 1) false := by
  simp [namedActualScanReference.eq_2]

def namedActualScanView (output : Std.Usize × Bool) : Nat × Bool :=
  (output.1.val, output.2)

def namedActualScanRemaining {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (index : Std.Usize) : Nat :=
  actuals.val.length - index.val

def namedActualScanInvariant {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (candidate : String) (expected : Nat × Bool)
    (state : Std.Usize × Bool) : Prop :=
  state.1.val ≤ actuals.val.length ∧
    namedActualScanReference (actuals.val.drop state.1.val)
      candidate state.1.val state.2 = expected

theorem named_actual_index_loop_body_preserves_reference_and_decreases
    {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (candidate : String) (expected : Nat × Bool)
    (state : Std.Usize × Bool)
    (invariant : namedActualScanInvariant actuals candidate expected state) :
    WP.spec
      (BindCallFull.named_actual_index_loop.body
        actuals candidate (Slice.len actuals) state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => namedActualScanView output = expected
        | .cont next =>
            namedActualScanInvariant actuals candidate expected next ∧
              namedActualScanRemaining actuals next.1 <
                namedActualScanRemaining actuals state.1) := by
  rcases state with ⟨index, found⟩
  unfold BindCallFull.named_actual_index_loop.body
  unfold namedActualScanInvariant at invariant
  unfold namedActualScanInvariant namedActualScanRemaining namedActualScanView
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  by_cases indexWithin : index < Slice.len actuals
  · simp only [indexWithin, if_true]
    by_cases alreadyFound : found = true
    · have expectedEq : (index.val, true) = expected := by
        simpa [alreadyFound] using invariant.2
      simpa [alreadyFound, namedActualScanView] using expectedEq
    · have foundFalse : found = false := Bool.eq_false_of_not_eq_true alreadyFound
      simp only [foundFalse, Bool.false_eq_true, if_false]
      have natIndexBound : index.val < actuals.val.length := by
        simpa [Slice.len] using indexWithin
      step with Slice.index_usize_spec as ⟨actual, actualEq⟩ by
        exact natIndexBound
      rw [string_eq_exact actual.name candidate]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        have sliceBound := actuals.property
        omega
      have dropStep :
          actuals.val.drop index.val =
            actuals.val[index.val] :: actuals.val.drop (index.val + 1) :=
        List.drop_eq_getElem_cons natIndexBound
      have referenceStep := invariant.2
      rw [dropStep] at referenceStep
      simp only [foundFalse, namedActualScanReference_cons_false] at referenceStep
      simp only [actualEq, nextIndexEq]
      by_cases currentMatches : actuals.val[index.val].name = candidate
      · have matchTrue :
            (actuals.val[index.val].name == candidate) = true := by
          simpa using currentMatches
        have referenceEq : (index.val + 1, true) = expected := by
          simpa [currentMatches] using referenceStep
        have referenceInvariant :
            namedActualScanReference (actuals.val.drop (index.val + 1))
              candidate (index.val + 1) true = expected := by
          simpa using referenceEq
        simp only [matchTrue]
        exact ⟨by omega, referenceInvariant, by omega⟩
      · have matchFalse :
            (actuals.val[index.val].name == candidate) = false := by
          simpa using currentMatches
        have referenceEq :
            namedActualScanReference (actuals.val.drop (index.val + 1))
              candidate (index.val + 1) false = expected := by
          simpa [currentMatches] using referenceStep
        simp only [matchFalse]
        exact ⟨by omega, referenceEq, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : actuals.val.length ≤ index.val := by
      simpa [Slice.len] using indexWithin
    have atEnd : index.val = actuals.val.length := by omega
    have expectedEq := invariant.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    simpa [namedActualScanView, atEnd] using expectedEq

theorem named_actual_index_loop_matches_reference
    {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (candidate : String) (index : Std.Usize) (found : Bool)
    (indexBound : index.val ≤ actuals.val.length) :
    WP.spec
      (BindCallFull.named_actual_index_loop
        actuals candidate (Slice.len actuals) index found)
      (fun output =>
        namedActualScanView output =
          namedActualScanReference (actuals.val.drop index.val)
            candidate index.val found) := by
  let expected := namedActualScanReference (actuals.val.drop index.val)
    candidate index.val found
  have initialInvariant :
      namedActualScanInvariant actuals candidate expected (index, found) :=
    ⟨indexBound, rfl⟩
  unfold BindCallFull.named_actual_index_loop
  apply loop.spec_decr_nat
      (measure := fun state => namedActualScanRemaining actuals state.1)
      (inv := namedActualScanInvariant actuals candidate expected)
      (post := fun output => namedActualScanView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (named_actual_index_loop_body_preserves_reference_and_decreases
      actuals candidate expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem namedActualScanReference_true_after_start {value : Type}
    (remaining : List (BindCallFull.NamedActual String value))
    (candidate : String) (index : Nat)
    (foundTrue : (namedActualScanReference remaining candidate index false).2 = true) :
    index < (namedActualScanReference remaining candidate index false).1 := by
  induction remaining generalizing index with
  | nil => simp at foundTrue
  | cons actual tail inductionHypothesis =>
      rw [namedActualScanReference_cons_false]
      by_cases currentMatches : actual.name = candidate
      · simp [currentMatches]
      · simp [currentMatches] at foundTrue ⊢
        have tailPositive := inductionHypothesis (index + 1) foundTrue
        omega

def namedActualIndexReference {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (candidate : String) : Nat :=
  let scan := namedActualScanReference actuals.val candidate 0 false
  if scan.2 then scan.1 - 1 else actuals.val.length

theorem named_actual_index_matches_reference
    {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (candidate : String) :
    WP.spec (BindCallFull.named_actual_index actuals candidate)
      (fun output => output.val = namedActualIndexReference actuals candidate) := by
  unfold BindCallFull.named_actual_index
  apply WP.spec_bind
  · exact named_actual_index_loop_matches_reference
      actuals candidate 0#usize false (by simp)
  · rintro ⟨index, found⟩ scanEq
    change (index.val, found) =
      namedActualScanReference actuals.val candidate 0 false at scanEq
    let scan := namedActualScanReference actuals.val candidate 0 false
    have scanEq' : (index.val, found) = scan := scanEq
    by_cases foundTrue : found = true
    · simp [foundTrue]
      have scanFoundTrue : scan.2 = true := by
        rw [← scanEq']
        exact foundTrue
      have positive : 0 < scan.1 :=
        namedActualScanReference_true_after_start
          actuals.val candidate 0 scanFoundTrue
      step with Std.Usize.sub_spec as ⟨output, outputEq⟩ by
        rw [← scanEq'] at positive
        simpa using positive
      unfold namedActualIndexReference
      change output.val =
        if scan.2 = true then scan.1 - 1 else actuals.val.length
      rw [scanFoundTrue]
      simp only [if_true]
      rw [← scanEq']
      exact outputEq
    · have foundFalse : found = false := Bool.eq_false_of_not_eq_true foundTrue
      simp [foundFalse]
      unfold namedActualIndexReference
      have scanFoundFalse : scan.2 = false := by
        rw [← scanEq']
        exact foundFalse
      change actuals.val.length =
        if scan.2 = true then scan.1 - 1 else actuals.val.length
      rw [scanFoundFalse]
      simp

def findNamedActualReference {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (candidate : String) : Option (BindCallFull.NamedActual String value) :=
  actuals.val[namedActualIndexReference actuals candidate]?

theorem find_named_actual_matches_reference
    {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (candidate : String) :
    WP.spec (BindCallFull.find_named_actual actuals candidate)
      (fun output => output = findNamedActualReference actuals candidate) := by
  unfold BindCallFull.find_named_actual
  apply WP.spec_bind
  · exact named_actual_index_matches_reference actuals candidate
  · intro index indexEq
    by_cases indexWithin : index < Slice.len actuals
    · simp only [indexWithin, if_true]
      have natIndexBound : index.val < actuals.val.length := by
        simpa [Slice.len] using indexWithin
      step with Slice.index_usize_spec as ⟨actual, actualEq⟩ by
        exact natIndexBound
      unfold findNamedActualReference
      rw [← indexEq]
      simpa [List.getElem?_eq_getElem natIndexBound] using actualEq
    · simp only [indexWithin, if_false]
      have exhausted : actuals.val.length ≤ index.val := by
        simpa [Slice.len] using indexWithin
      unfold findNamedActualReference
      rw [← indexEq]
      simp [List.getElem?_eq_none exhausted]

def positionalOnlyMissingAt {type value : Type}
    (call : BindCallFull.ExpandedCall type value)
    (parameter : BindCallFull.FormalParameter type value)
    (index : Nat) : Bool :=
  if call.positional.val.length ≤ index then
    parameter.default_value.isNone
  else
    false

def positionalOnlyMissingScanReference {type value : Type}
    (remaining : List (BindCallFull.FormalParameter type value))
    (call : BindCallFull.ExpandedCall type value)
    (index : Nat) (isMissing : Bool) : Nat × Bool :=
  if isMissing then
    (index, true)
  else
    match remaining with
    | [] => (index, false)
    | parameter :: tail =>
        if positionalOnlyMissingAt call parameter index then
          (index + 1, true)
        else
          positionalOnlyMissingScanReference tail call (index + 1) false
termination_by remaining.length

@[simp]
theorem positionalOnlyMissingScanReference_found_true {type value : Type}
    (remaining : List (BindCallFull.FormalParameter type value))
    (call : BindCallFull.ExpandedCall type value) (index : Nat) :
    positionalOnlyMissingScanReference remaining call index true =
      (index, true) := by
  cases remaining <;>
    simp [positionalOnlyMissingScanReference.eq_1,
      positionalOnlyMissingScanReference.eq_2]

@[simp]
theorem positionalOnlyMissingScanReference_empty {type value : Type}
    (call : BindCallFull.ExpandedCall type value)
    (index : Nat) (isMissing : Bool) :
    positionalOnlyMissingScanReference
      ([] : List (BindCallFull.FormalParameter type value))
      call index isMissing = (index, isMissing) := by
  cases isMissing <;> simp [positionalOnlyMissingScanReference.eq_1]

@[simp]
theorem positionalOnlyMissingScanReference_cons_false {type value : Type}
    (parameter : BindCallFull.FormalParameter type value)
    (tail : List (BindCallFull.FormalParameter type value))
    (call : BindCallFull.ExpandedCall type value) (index : Nat) :
    positionalOnlyMissingScanReference (parameter :: tail) call index false =
      if positionalOnlyMissingAt call parameter index then
        (index + 1, true)
      else
        positionalOnlyMissingScanReference tail call (index + 1) false := by
  simp [positionalOnlyMissingScanReference.eq_2]

def positionalOnlyMissingRemaining {type value : Type}
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter type value))
    (index : Std.Usize) : Nat :=
  parameters.val.length - index.val

def positionalOnlyMissingInvariant {type value : Type}
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter type value))
    (call : BindCallFull.ExpandedCall type value)
    (expected : Nat × Bool) (state : Std.Usize × Bool) : Prop :=
  state.1.val ≤ parameters.val.length ∧
    positionalOnlyMissingScanReference
      (parameters.val.drop state.1.val) call state.1.val state.2 = expected

theorem first_missing_positional_only_loop_body_preserves_reference_and_decreases
    {type value : Type}
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter type value))
    (call : BindCallFull.ExpandedCall type value)
    (expected : Nat × Bool) (state : Std.Usize × Bool)
    (invariant : positionalOnlyMissingInvariant
      parameters call expected state) :
    WP.spec
      (BindCallFull.first_missing_positional_only_loop.body
        parameters call (alloc.vec.Vec.len parameters) state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => namedActualScanView output = expected
        | .cont next =>
            positionalOnlyMissingInvariant parameters call expected next ∧
              positionalOnlyMissingRemaining parameters next.1 <
                positionalOnlyMissingRemaining parameters state.1) := by
  rcases state with ⟨index, isMissing⟩
  unfold BindCallFull.first_missing_positional_only_loop.body
  unfold positionalOnlyMissingInvariant at invariant
  unfold positionalOnlyMissingInvariant positionalOnlyMissingRemaining
    namedActualScanView
  change index.val ≤ parameters.val.length ∧
      positionalOnlyMissingScanReference (parameters.val.drop index.val)
        call index.val isMissing = expected at invariant
  by_cases indexWithin : index < alloc.vec.Vec.len parameters
  · simp only [indexWithin, if_true]
    by_cases alreadyMissing : isMissing = true
    · have expectedEq : (index.val, true) = expected := by
        simpa [alreadyMissing] using invariant.2
      simpa [alreadyMissing] using expectedEq
    · have notMissing : isMissing = false :=
        Bool.eq_false_of_not_eq_true alreadyMissing
      simp only [notMissing, Bool.false_eq_true, if_false]
      have natIndexBound : index.val < parameters.val.length := by
        simpa [alloc.vec.Vec.len] using indexWithin
      step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
        exact natIndexBound
      by_cases beyondPositionals :
          index ≥ alloc.vec.Vec.len call.positional
      · simp only [beyondPositionals, if_true]
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have vectorBound := parameters.property
          omega
        have dropStep :
            parameters.val.drop index.val =
              parameters.val[index.val] ::
                parameters.val.drop (index.val + 1) :=
          List.drop_eq_getElem_cons natIndexBound
        have referenceStep := invariant.2
        rw [dropStep] at referenceStep
        simp only [notMissing,
          positionalOnlyMissingScanReference_cons_false] at referenceStep
        have beyondNat : call.positional.val.length ≤ index.val := by
          simpa [alloc.vec.Vec.len] using beyondPositionals
        simp only [parameterEq, nextIndexEq]
        cases defaultEq : parameters.val[index.val].default_value with
        | none =>
            have referenceEq : (index.val + 1, true) = expected := by
              simpa [positionalOnlyMissingAt, beyondNat, defaultEq] using
                referenceStep
            simp [defaultEq]
            exact ⟨by omega, referenceEq, by omega⟩
        | some default =>
            have referenceEq :
                positionalOnlyMissingScanReference
                  (parameters.val.drop (index.val + 1)) call
                  (index.val + 1) false = expected := by
              simpa [positionalOnlyMissingAt, beyondNat, defaultEq] using
                referenceStep
            simp [defaultEq]
            exact ⟨by omega, referenceEq, by omega⟩
      · simp only [beyondPositionals, if_false]
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have vectorBound := parameters.property
          omega
        have dropStep :
            parameters.val.drop index.val =
              parameters.val[index.val] ::
                parameters.val.drop (index.val + 1) :=
          List.drop_eq_getElem_cons natIndexBound
        have referenceStep := invariant.2
        rw [dropStep] at referenceStep
        simp only [notMissing,
          positionalOnlyMissingScanReference_cons_false] at referenceStep
        have beforeEnd : ¬ call.positional.val.length ≤ index.val := by
          simpa [alloc.vec.Vec.len] using beyondPositionals
        have referenceEq :
            positionalOnlyMissingScanReference
              (parameters.val.drop (index.val + 1)) call
              (index.val + 1) false = expected := by
          simpa [parameterEq, positionalOnlyMissingAt, beforeEnd] using
            referenceStep
        simp only [nextIndexEq]
        exact ⟨by omega, referenceEq, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : parameters.val.length ≤ index.val := by
      simpa [alloc.vec.Vec.len] using indexWithin
    have atEnd : index.val = parameters.val.length := by omega
    have expectedEq := invariant.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    simpa [atEnd] using expectedEq

theorem first_missing_positional_only_loop_matches_reference
    {type value : Type}
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter type value))
    (call : BindCallFull.ExpandedCall type value)
    (index : Std.Usize) (isMissing : Bool)
    (indexBound : index.val ≤ parameters.val.length) :
    WP.spec
      (BindCallFull.first_missing_positional_only_loop
        parameters call (alloc.vec.Vec.len parameters) index isMissing)
      (fun output => namedActualScanView output =
        positionalOnlyMissingScanReference
          (parameters.val.drop index.val) call index.val isMissing) := by
  let expected := positionalOnlyMissingScanReference
    (parameters.val.drop index.val) call index.val isMissing
  have initialInvariant :
      positionalOnlyMissingInvariant parameters call expected
        (index, isMissing) := ⟨indexBound, rfl⟩
  unfold BindCallFull.first_missing_positional_only_loop
  apply loop.spec_decr_nat
      (measure := fun state =>
        positionalOnlyMissingRemaining parameters state.1)
      (inv := positionalOnlyMissingInvariant parameters call expected)
      (post := fun output => namedActualScanView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_missing_positional_only_loop_body_preserves_reference_and_decreases
      parameters call expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

def ordinaryNameReference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (candidate : String) : Bool :=
  Bool.or
    (signature.positional.val.any
      (fun parameter => parameter.name == candidate))
    (signature.keyword_only.val.any
      (fun parameter => parameter.name == candidate))

def unexpectedKeywordScanReference {value : Type}
    (remaining : List (BindCallFull.NamedActual String value))
    (signature : BindCallFull.CallSignature String value)
    (index : Nat) (found : Bool) : Nat × Bool :=
  if found then
    (index, true)
  else
    match remaining with
    | [] => (index, false)
    | actual :: tail =>
        if ordinaryNameReference signature actual.name then
          unexpectedKeywordScanReference tail signature (index + 1) false
        else
          (index + 1, true)
termination_by remaining.length

@[simp]
theorem unexpectedKeywordScanReference_found_true {value : Type}
    (remaining : List (BindCallFull.NamedActual String value))
    (signature : BindCallFull.CallSignature String value) (index : Nat) :
    unexpectedKeywordScanReference remaining signature index true =
      (index, true) := by
  cases remaining <;>
    simp [unexpectedKeywordScanReference.eq_1,
      unexpectedKeywordScanReference.eq_2]

@[simp]
theorem unexpectedKeywordScanReference_empty {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (index : Nat) (found : Bool) :
    unexpectedKeywordScanReference
      ([] : List (BindCallFull.NamedActual String value))
      signature index found = (index, found) := by
  cases found <;> simp [unexpectedKeywordScanReference.eq_1]

@[simp]
theorem unexpectedKeywordScanReference_cons_false {value : Type}
    (actual : BindCallFull.NamedActual String value)
    (tail : List (BindCallFull.NamedActual String value))
    (signature : BindCallFull.CallSignature String value) (index : Nat) :
    unexpectedKeywordScanReference (actual :: tail) signature index false =
      if ordinaryNameReference signature actual.name then
        unexpectedKeywordScanReference tail signature (index + 1) false
      else
        (index + 1, true) := by
  simp [unexpectedKeywordScanReference.eq_2]

def unexpectedKeywordInvariant {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (signature : BindCallFull.CallSignature String value)
    (expected : Nat × Bool) (state : Std.Usize × Bool) : Prop :=
  state.1.val ≤ actuals.val.length ∧
    unexpectedKeywordScanReference (actuals.val.drop state.1.val)
      signature state.1.val state.2 = expected

theorem first_unexpected_keyword_loop_body_preserves_reference_and_decreases
    {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (signature : BindCallFull.CallSignature String value)
    (expected : Nat × Bool) (state : Std.Usize × Bool)
    (invariant : unexpectedKeywordInvariant
      actuals signature expected state) :
    WP.spec
      (BindCallFull.first_unexpected_keyword_loop.body
        actuals signature (Slice.len actuals) state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => namedActualScanView output = expected
        | .cont next =>
            unexpectedKeywordInvariant actuals signature expected next ∧
              namedActualScanRemaining actuals next.1 <
                namedActualScanRemaining actuals state.1) := by
  rcases state with ⟨index, found⟩
  unfold BindCallFull.first_unexpected_keyword_loop.body
  unfold unexpectedKeywordInvariant at invariant
  unfold unexpectedKeywordInvariant namedActualScanRemaining namedActualScanView
  change index.val ≤ actuals.val.length ∧
      unexpectedKeywordScanReference (actuals.val.drop index.val)
        signature index.val found = expected at invariant
  by_cases indexWithin : index < Slice.len actuals
  · simp only [indexWithin, if_true]
    by_cases alreadyFound : found = true
    · have expectedEq : (index.val, true) = expected := by
        simpa [alreadyFound] using invariant.2
      simpa [alreadyFound] using expectedEq
    · have foundFalse : found = false := Bool.eq_false_of_not_eq_true alreadyFound
      simp only [foundFalse, Bool.false_eq_true, if_false]
      have natIndexBound : index.val < actuals.val.length := by
        simpa [Slice.len] using indexWithin
      step with Slice.index_usize_spec as ⟨actual, actualEq⟩ by
        exact natIndexBound
      step with ordinary_parameter_name_matches_reference as
        ⟨isOrdinary, ordinaryEq⟩
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        have sliceBound := actuals.property
        omega
      have dropStep :
          actuals.val.drop index.val =
            actuals.val[index.val] :: actuals.val.drop (index.val + 1) :=
        List.drop_eq_getElem_cons natIndexBound
      have referenceStep := invariant.2
      rw [dropStep] at referenceStep
      simp only [foundFalse,
        unexpectedKeywordScanReference_cons_false] at referenceStep
      have ordinaryEq' : isOrdinary =
          ordinaryNameReference signature actual.name := by
        simpa [ordinaryNameReference] using ordinaryEq
      simp only [actualEq, ordinaryEq', nextIndexEq]
      by_cases ordinary : ordinaryNameReference
          signature actuals.val[index.val].name = true
      · have nextReference :
            unexpectedKeywordScanReference
              (actuals.val.drop (index.val + 1)) signature
              (index.val + 1) false = expected := by
          simpa [ordinary] using referenceStep
        simp [ordinary]
        exact ⟨by omega, nextReference, by omega⟩
      · have notOrdinary : ordinaryNameReference
            signature actuals.val[index.val].name = false :=
          Bool.eq_false_of_not_eq_true ordinary
        have referenceEq : (index.val + 1, true) = expected := by
          simpa [notOrdinary] using referenceStep
        simp [notOrdinary]
        exact ⟨by omega, referenceEq, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : actuals.val.length ≤ index.val := by
      simpa [Slice.len] using indexWithin
    have atEnd : index.val = actuals.val.length := by omega
    have expectedEq := invariant.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    simpa [atEnd] using expectedEq

theorem first_unexpected_keyword_loop_matches_reference
    {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (signature : BindCallFull.CallSignature String value)
    (index : Std.Usize) (found : Bool)
    (indexBound : index.val ≤ actuals.val.length) :
    WP.spec
      (BindCallFull.first_unexpected_keyword_loop
        actuals signature (Slice.len actuals) index found)
      (fun output => namedActualScanView output =
        unexpectedKeywordScanReference (actuals.val.drop index.val)
          signature index.val found) := by
  let expected := unexpectedKeywordScanReference
    (actuals.val.drop index.val) signature index.val found
  have initialInvariant :
      unexpectedKeywordInvariant actuals signature expected (index, found) :=
    ⟨indexBound, rfl⟩
  unfold BindCallFull.first_unexpected_keyword_loop
  apply loop.spec_decr_nat
      (measure := fun state => namedActualScanRemaining actuals state.1)
      (inv := unexpectedKeywordInvariant actuals signature expected)
      (post := fun output => namedActualScanView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_unexpected_keyword_loop_body_preserves_reference_and_decreases
      actuals signature expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem unexpectedKeywordScanReference_true_after_start {value : Type}
    (remaining : List (BindCallFull.NamedActual String value))
    (signature : BindCallFull.CallSignature String value)
    (index : Nat)
    (foundTrue :
      (unexpectedKeywordScanReference remaining signature index false).2 = true) :
    index < (unexpectedKeywordScanReference
      remaining signature index false).1 := by
  induction remaining generalizing index with
  | nil => simp at foundTrue
  | cons actual tail inductionHypothesis =>
      rw [unexpectedKeywordScanReference_cons_false]
      by_cases ordinary : ordinaryNameReference signature actual.name = true
      · simp [ordinary] at foundTrue ⊢
        have tailPositive := inductionHypothesis (index + 1) foundTrue
        omega
      · have notOrdinary : ordinaryNameReference signature actual.name = false :=
          Bool.eq_false_of_not_eq_true ordinary
        simp [notOrdinary]

def firstUnexpectedKeywordReference {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (signature : BindCallFull.CallSignature String value) : Nat :=
  let scan := unexpectedKeywordScanReference actuals.val signature 0 false
  if scan.2 then scan.1 - 1 else actuals.val.length

theorem first_unexpected_keyword_matches_reference
    {value : Type}
    (actuals : Slice (BindCallFull.NamedActual String value))
    (signature : BindCallFull.CallSignature String value) :
    WP.spec (BindCallFull.first_unexpected_keyword actuals signature)
      (fun output => output.val =
        firstUnexpectedKeywordReference actuals signature) := by
  unfold BindCallFull.first_unexpected_keyword
  apply WP.spec_bind
  · exact first_unexpected_keyword_loop_matches_reference
      actuals signature 0#usize false (by simp)
  · rintro ⟨index, found⟩ scanEq
    change (index.val, found) =
      unexpectedKeywordScanReference actuals.val signature 0 false at scanEq
    let scan := unexpectedKeywordScanReference actuals.val signature 0 false
    have scanEq' : (index.val, found) = scan := scanEq
    by_cases foundTrue : found = true
    · simp [foundTrue]
      have scanFoundTrue : scan.2 = true := by
        rw [← scanEq']
        exact foundTrue
      have positive : 0 < scan.1 :=
        unexpectedKeywordScanReference_true_after_start
          actuals.val signature 0 scanFoundTrue
      step with Std.Usize.sub_spec as ⟨output, outputEq⟩ by
        rw [← scanEq'] at positive
        simpa using positive
      unfold firstUnexpectedKeywordReference
      change output.val =
        if scan.2 = true then scan.1 - 1 else actuals.val.length
      rw [scanFoundTrue]
      simp only [if_true]
      rw [← scanEq']
      exact outputEq
    · have foundFalse : found = false := Bool.eq_false_of_not_eq_true foundTrue
      simp [foundFalse]
      unfold firstUnexpectedKeywordReference
      have scanFoundFalse : scan.2 = false := by
        rw [← scanEq']
        exact foundFalse
      change actuals.val.length =
        if scan.2 = true then scan.1 - 1 else actuals.val.length
      rw [scanFoundFalse]
      simp

def duplicateNamedInnerReference {type value : Type}
    (remaining : List (BindCallFull.NamedActual type value))
    (fuel : Nat) (candidate : String) (seen : Bool) : Bool :=
  match fuel with
  | 0 => seen
  | fuel + 1 =>
      if seen then
        true
      else
        match remaining with
        | [] => false
        | actual :: tail =>
            duplicateNamedInnerReference tail fuel candidate
              (actual.name == candidate)

@[simp]
theorem duplicateNamedInnerReference_zero {type value : Type}
    (remaining : List (BindCallFull.NamedActual type value))
    (candidate : String) (seen : Bool) :
    duplicateNamedInnerReference remaining 0 candidate seen = seen := by
  exact duplicateNamedInnerReference.eq_1 remaining candidate seen

@[simp]
theorem duplicateNamedInnerReference_seen {type value : Type}
    (remaining : List (BindCallFull.NamedActual type value))
    (fuel : Nat) (candidate : String) :
    duplicateNamedInnerReference remaining fuel candidate true = true := by
  cases fuel with
  | zero => exact duplicateNamedInnerReference.eq_1 remaining candidate true
  | succ fuel =>
      cases remaining <;>
        simp [duplicateNamedInnerReference.eq_2,
          duplicateNamedInnerReference.eq_3]

@[simp]
theorem duplicateNamedInnerReference_cons_false {type value : Type}
    (actual : BindCallFull.NamedActual type value)
    (tail : List (BindCallFull.NamedActual type value))
    (fuel : Nat) (candidate : String) :
    duplicateNamedInnerReference (actual :: tail) (fuel + 1)
      candidate false =
        duplicateNamedInnerReference tail fuel candidate
          (actual.name == candidate) := by
  simpa using duplicateNamedInnerReference.eq_3
    candidate false fuel actual tail

def duplicateNamedInnerInvariant {type value : Type}
    (actuals : Slice (BindCallFull.NamedActual type value))
    (outerIndex : Std.Usize) (candidate : String) (expected : Bool)
    (state : Std.Usize × Bool) : Prop :=
  state.1.val ≤ outerIndex.val ∧
    outerIndex.val ≤ actuals.val.length ∧
    duplicateNamedInnerReference (actuals.val.drop state.1.val)
      (outerIndex.val - state.1.val) candidate state.2 = expected

def duplicateNamedInnerRemaining
    (outerIndex index : Std.Usize) : Nat :=
  outerIndex.val - index.val

theorem first_duplicate_named_actual_inner_body_preserves_reference_and_decreases
    {type value : Type}
    (actuals : Slice (BindCallFull.NamedActual type value))
    (outerIndex : Std.Usize) (candidate : String) (expected : Bool)
    (state : Std.Usize × Bool)
    (invariant : duplicateNamedInnerInvariant
      actuals outerIndex candidate expected state) :
    WP.spec
      (BindCallFull.first_duplicate_named_actual_loop0_loop0.body
        actuals outerIndex candidate state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output = expected
        | .cont next =>
            duplicateNamedInnerInvariant
              actuals outerIndex candidate expected next ∧
              duplicateNamedInnerRemaining outerIndex next.1 <
                duplicateNamedInnerRemaining outerIndex state.1) := by
  rcases state with ⟨innerIndex, seen⟩
  unfold BindCallFull.first_duplicate_named_actual_loop0_loop0.body
  unfold duplicateNamedInnerInvariant at invariant
  unfold duplicateNamedInnerInvariant duplicateNamedInnerRemaining
  change innerIndex.val ≤ outerIndex.val ∧
      outerIndex.val ≤ actuals.val.length ∧
      duplicateNamedInnerReference (actuals.val.drop innerIndex.val)
        (outerIndex.val - innerIndex.val) candidate seen = expected at invariant
  by_cases indexWithin : innerIndex < outerIndex
  · simp only [indexWithin, if_true]
    by_cases alreadySeen : seen = true
    · have expectedTrue : true = expected := by
        simpa [alreadySeen] using invariant.2.2
      simpa [alreadySeen] using expectedTrue
    · have seenFalse : seen = false := Bool.eq_false_of_not_eq_true alreadySeen
      simp only [seenFalse, Bool.false_eq_true, if_false]
      have innerOuter : innerIndex.val < outerIndex.val := by
        simpa using indexWithin
      have innerBound : innerIndex.val < actuals.val.length :=
        lt_of_lt_of_le innerOuter invariant.2.1
      step with Slice.index_usize_spec as ⟨actual, actualEq⟩ by
        exact innerBound
      rw [string_eq_exact actual.name candidate]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        have sliceBound := actuals.property
        omega
      have fuelStep :
          outerIndex.val - innerIndex.val =
            (outerIndex.val - (innerIndex.val + 1)) + 1 := by
        omega
      have dropStep :
          actuals.val.drop innerIndex.val =
            actuals.val[innerIndex.val] ::
              actuals.val.drop (innerIndex.val + 1) :=
        List.drop_eq_getElem_cons innerBound
      have referenceStep := invariant.2.2
      rw [dropStep, fuelStep] at referenceStep
      simp only [seenFalse,
        duplicateNamedInnerReference_cons_false] at referenceStep
      simp only [actualEq, nextIndexEq]
      exact ⟨by omega, invariant.2.1, referenceStep, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : outerIndex.val ≤ innerIndex.val := by
      simpa using indexWithin
    have atEnd : innerIndex.val = outerIndex.val := by omega
    have expectedEq := invariant.2.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    exact expectedEq

theorem first_duplicate_named_actual_inner_loop_matches_reference
    {type value : Type}
    (actuals : Slice (BindCallFull.NamedActual type value))
    (outerIndex : Std.Usize) (candidate : String)
    (innerIndex : Std.Usize) (seen : Bool)
    (innerBound : innerIndex.val ≤ outerIndex.val)
    (outerBound : outerIndex.val ≤ actuals.val.length) :
    WP.spec
      (BindCallFull.first_duplicate_named_actual_loop0_loop0
        actuals outerIndex candidate innerIndex seen)
      (fun output => output = duplicateNamedInnerReference
        (actuals.val.drop innerIndex.val)
        (outerIndex.val - innerIndex.val) candidate seen) := by
  let expected := duplicateNamedInnerReference
    (actuals.val.drop innerIndex.val)
    (outerIndex.val - innerIndex.val) candidate seen
  have initialInvariant : duplicateNamedInnerInvariant
      actuals outerIndex candidate expected (innerIndex, seen) :=
    ⟨innerBound, outerBound, rfl⟩
  unfold BindCallFull.first_duplicate_named_actual_loop0_loop0
  apply loop.spec_decr_nat
      (measure := fun state =>
        duplicateNamedInnerRemaining outerIndex state.1)
      (inv := duplicateNamedInnerInvariant
        actuals outerIndex candidate expected)
      (post := fun output => output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_duplicate_named_actual_inner_body_preserves_reference_and_decreases
      actuals outerIndex candidate expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

def duplicateNamedOuterReference {type value : Type}
    (allActuals remaining : List (BindCallFull.NamedActual type value))
    (outerIndex : Nat) (duplicate : Option String) : Option String :=
  match duplicate with
  | some duplicateName => some duplicateName
  | none =>
      match remaining with
      | [] => none
      | actual :: tail =>
          if duplicateNamedInnerReference allActuals outerIndex
              actual.name false then
            some actual.name
          else
            duplicateNamedOuterReference
              allActuals tail (outerIndex + 1) none
termination_by remaining.length

@[simp]
theorem duplicateNamedOuterReference_some {type value : Type}
    (allActuals remaining : List (BindCallFull.NamedActual type value))
    (outerIndex : Nat) (duplicateName : String) :
    duplicateNamedOuterReference allActuals remaining outerIndex
      (some duplicateName) = some duplicateName := by
  exact duplicateNamedOuterReference.eq_1
    allActuals remaining outerIndex duplicateName

@[simp]
theorem duplicateNamedOuterReference_empty {type value : Type}
    (allActuals : List (BindCallFull.NamedActual type value))
    (outerIndex : Nat) :
    duplicateNamedOuterReference allActuals [] outerIndex none = none := by
  exact duplicateNamedOuterReference.eq_2 allActuals outerIndex

@[simp]
theorem duplicateNamedOuterReference_cons_none {type value : Type}
    (allActuals : List (BindCallFull.NamedActual type value))
    (actual : BindCallFull.NamedActual type value)
    (tail : List (BindCallFull.NamedActual type value))
    (outerIndex : Nat) :
    duplicateNamedOuterReference allActuals (actual :: tail)
      outerIndex none =
        if duplicateNamedInnerReference allActuals outerIndex
            actual.name false then
          some actual.name
        else
          duplicateNamedOuterReference
            allActuals tail (outerIndex + 1) none := by
  simpa using duplicateNamedOuterReference.eq_3
    allActuals outerIndex actual tail

def duplicateNamedOuterInvariant {type value : Type}
    (actuals : Slice (BindCallFull.NamedActual type value))
    (expected : Option String) (state : Std.Usize × Option String) : Prop :=
  state.1.val ≤ actuals.val.length ∧
    duplicateNamedOuterReference actuals.val
      (actuals.val.drop state.1.val) state.1.val state.2 = expected

def duplicateNamedOuterRemaining {type value : Type}
    (actuals : Slice (BindCallFull.NamedActual type value))
    (index : Std.Usize) : Nat :=
  actuals.val.length - index.val

theorem first_duplicate_named_actual_outer_body_preserves_reference_and_decreases
    {type value : Type}
    (actuals : Slice (BindCallFull.NamedActual type value))
    (expected : Option String) (state : Std.Usize × Option String)
    (invariant : duplicateNamedOuterInvariant actuals expected state) :
    WP.spec
      (BindCallFull.first_duplicate_named_actual_loop0.body
        actuals state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output = expected
        | .cont next =>
            duplicateNamedOuterInvariant actuals expected next ∧
              duplicateNamedOuterRemaining actuals next.1 <
                duplicateNamedOuterRemaining actuals state.1) := by
  rcases state with ⟨outerIndex, duplicate⟩
  unfold BindCallFull.first_duplicate_named_actual_loop0.body
  unfold duplicateNamedOuterInvariant at invariant
  unfold duplicateNamedOuterInvariant duplicateNamedOuterRemaining
  change outerIndex.val ≤ actuals.val.length ∧
      duplicateNamedOuterReference actuals.val
        (actuals.val.drop outerIndex.val) outerIndex.val duplicate = expected
      at invariant
  by_cases indexWithin : outerIndex < Slice.len actuals
  · simp only [indexWithin, if_true]
    cases duplicate with
    | some duplicateName =>
        simp [duplicateNamedOuterReference_some] at invariant ⊢
        exact invariant.2
    | none =>
        simp
        have natIndexBound : outerIndex.val < actuals.val.length := by
          simpa [Slice.len] using indexWithin
        step with Slice.index_usize_spec as ⟨actual, actualEq⟩ by
          exact natIndexBound
        rw [string_clone_exact]
        step with first_duplicate_named_actual_inner_loop_matches_reference as
          ⟨seen, seenEq⟩ by
            · simp
            · exact invariant.1
        have dropStep :
            actuals.val.drop outerIndex.val =
              actuals.val[outerIndex.val] ::
                actuals.val.drop (outerIndex.val + 1) :=
          List.drop_eq_getElem_cons natIndexBound
        have referenceStep := invariant.2
        rw [dropStep] at referenceStep
        simp only [duplicateNamedOuterReference_cons_none] at referenceStep
        have seenEq' : seen = duplicateNamedInnerReference actuals.val
            outerIndex.val actual.name false := by
          simpa using seenEq
        rw [seenEq']
        by_cases isDuplicate : duplicateNamedInnerReference actuals.val
            outerIndex.val actuals.val[outerIndex.val].name false = true
        · have referenceEq : some actuals.val[outerIndex.val].name = expected := by
            simpa [isDuplicate] using referenceStep
          simp only [actualEq, isDuplicate, if_true]
          step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
            have sliceBound := actuals.property
            omega
          simp only [nextIndexEq, duplicateNamedOuterReference_some]
          exact ⟨by omega, referenceEq, by omega⟩
        · have notDuplicate : duplicateNamedInnerReference actuals.val
              outerIndex.val actuals.val[outerIndex.val].name false = false :=
            Bool.eq_false_of_not_eq_true isDuplicate
          have nextReference : duplicateNamedOuterReference actuals.val
              (actuals.val.drop (outerIndex.val + 1))
              (outerIndex.val + 1) none = expected := by
            simpa [notDuplicate] using referenceStep
          simp only [actualEq, notDuplicate, Bool.false_eq_true, if_false]
          step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
            have sliceBound := actuals.property
            omega
          simp only [nextIndexEq]
          exact ⟨by omega, nextReference, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : actuals.val.length ≤ outerIndex.val := by
      simpa [Slice.len] using indexWithin
    have atEnd : outerIndex.val = actuals.val.length := by omega
    have expectedEq := invariant.2
    rw [atEnd] at expectedEq
    cases duplicate <;> simp at expectedEq ⊢ <;> exact expectedEq

theorem first_duplicate_named_actual_outer_loop_matches_reference
    {type value : Type}
    (actuals : Slice (BindCallFull.NamedActual type value))
    (outerIndex : Std.Usize) (duplicate : Option String)
    (indexBound : outerIndex.val ≤ actuals.val.length) :
    WP.spec
      (BindCallFull.first_duplicate_named_actual_loop0
        actuals outerIndex duplicate)
      (fun output => output = duplicateNamedOuterReference actuals.val
        (actuals.val.drop outerIndex.val) outerIndex.val duplicate) := by
  let expected := duplicateNamedOuterReference actuals.val
    (actuals.val.drop outerIndex.val) outerIndex.val duplicate
  have initialInvariant : duplicateNamedOuterInvariant
      actuals expected (outerIndex, duplicate) := ⟨indexBound, rfl⟩
  unfold BindCallFull.first_duplicate_named_actual_loop0
  apply loop.spec_decr_nat
      (measure := fun state => duplicateNamedOuterRemaining actuals state.1)
      (inv := duplicateNamedOuterInvariant actuals expected)
      (post := fun output => output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_duplicate_named_actual_outer_body_preserves_reference_and_decreases
      actuals expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem first_duplicate_named_actual_matches_reference
    {type value : Type}
    (actuals : Slice (BindCallFull.NamedActual type value)) :
    WP.spec (BindCallFull.first_duplicate_named_actual actuals)
      (fun output => output = duplicateNamedOuterReference
        actuals.val actuals.val 0 none) := by
  unfold BindCallFull.first_duplicate_named_actual
  exact first_duplicate_named_actual_outer_loop_matches_reference
    actuals 0#usize none (by simp)

def keywordOnlyMissingAt {value : Type}
    (call : BindCallFull.ExpandedCall String value)
    (parameter : BindCallFull.FormalParameter String value) : Bool :=
  if namedActualIndexReference (alloc.vec.Vec.deref call.named) parameter.name =
      call.named.val.length then
    parameter.default_value.isNone
  else
    false

def keywordOnlyMissingScanReference {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (index : Nat) (isMissing : Bool) : Nat × Bool :=
  if isMissing then
    (index, true)
  else
    match remaining with
    | [] => (index, false)
    | parameter :: tail =>
        if keywordOnlyMissingAt call parameter then
          (index + 1, true)
        else
          keywordOnlyMissingScanReference tail call (index + 1) false
termination_by remaining.length

@[simp]
theorem keywordOnlyMissingScanReference_found_true {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value) (index : Nat) :
    keywordOnlyMissingScanReference remaining call index true =
      (index, true) := by
  cases remaining <;>
    simp [keywordOnlyMissingScanReference.eq_1,
      keywordOnlyMissingScanReference.eq_2]

@[simp]
theorem keywordOnlyMissingScanReference_empty {value : Type}
    (call : BindCallFull.ExpandedCall String value)
    (index : Nat) (isMissing : Bool) :
    keywordOnlyMissingScanReference
      ([] : List (BindCallFull.FormalParameter String value))
      call index isMissing = (index, isMissing) := by
  cases isMissing <;> simp [keywordOnlyMissingScanReference.eq_1]

@[simp]
theorem keywordOnlyMissingScanReference_cons_false {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (tail : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value) (index : Nat) :
    keywordOnlyMissingScanReference (parameter :: tail) call index false =
      if keywordOnlyMissingAt call parameter then
        (index + 1, true)
      else
        keywordOnlyMissingScanReference tail call (index + 1) false := by
  simp [keywordOnlyMissingScanReference.eq_2]

def keywordOnlyMissingRemaining {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (index : Std.Usize) : Nat :=
  parameters.val.length - index.val

def keywordOnlyMissingInvariant {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (expected : Nat × Bool) (state : Std.Usize × Bool) : Prop :=
  state.1.val ≤ parameters.val.length ∧
    keywordOnlyMissingScanReference
      (parameters.val.drop state.1.val) call state.1.val state.2 = expected

def keywordOnlyMissingOutputView {value : Type}
    (output : alloc.vec.Vec (BindCallFull.FormalParameter String value) ×
      Std.Usize × Bool) : Nat × Bool :=
  (output.2.1.val, output.2.2)

theorem first_missing_keyword_only_loop_body_preserves_reference_and_decreases
    {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value)
    (expected : Nat × Bool) (state : Std.Usize × Bool)
    (invariant : keywordOnlyMissingInvariant
      signature.keyword_only call expected state) :
    WP.spec
      (BindCallFull.first_missing_keyword_only_loop.body
        signature call state.1 state.2)
      (fun flow =>
        match flow with
        | .done output =>
            output.1 = signature.keyword_only ∧
              keywordOnlyMissingOutputView output = expected
        | .cont next =>
            keywordOnlyMissingInvariant
                signature.keyword_only call expected next ∧
              keywordOnlyMissingRemaining signature.keyword_only next.1 <
                keywordOnlyMissingRemaining signature.keyword_only state.1) := by
  rcases state with ⟨index, isMissing⟩
  unfold BindCallFull.first_missing_keyword_only_loop.body
  unfold keywordOnlyMissingInvariant at invariant
  unfold keywordOnlyMissingInvariant keywordOnlyMissingRemaining
    keywordOnlyMissingOutputView
  change index.val ≤ signature.keyword_only.val.length ∧
      keywordOnlyMissingScanReference
        (signature.keyword_only.val.drop index.val)
        call index.val isMissing = expected at invariant
  by_cases indexWithin : index < alloc.vec.Vec.len signature.keyword_only
  · simp only [indexWithin, if_true]
    by_cases alreadyMissing : isMissing = true
    · have expectedEq : (index.val, true) = expected := by
        simpa [alreadyMissing] using invariant.2
      simpa [alreadyMissing] using expectedEq
    · have notMissing : isMissing = false :=
        Bool.eq_false_of_not_eq_true alreadyMissing
      simp only [notMissing, Bool.false_eq_true, if_false]
      have natIndexBound : index.val < signature.keyword_only.val.length := by
        simpa [alloc.vec.Vec.len] using indexWithin
      step with alloc.vec.Vec.index_usize_spec as
        ⟨parameter, parameterEq⟩ by exact natIndexBound
      rw [string_clone_exact]
      step with named_actual_index_matches_reference as
        ⟨namedIndex, namedIndexEq⟩
      have dropStep :
          signature.keyword_only.val.drop index.val =
            signature.keyword_only.val[index.val] ::
              signature.keyword_only.val.drop (index.val + 1) :=
        List.drop_eq_getElem_cons natIndexBound
      have referenceStep := invariant.2
      rw [dropStep] at referenceStep
      simp only [notMissing,
        keywordOnlyMissingScanReference_cons_false] at referenceStep
      by_cases namedAtEnd : namedIndex = alloc.vec.Vec.len call.named
      · simp only [namedAtEnd, if_true]
        have namedAtEndNat : namedActualIndexReference
            (alloc.vec.Vec.deref call.named)
            signature.keyword_only.val[index.val].name =
              call.named.val.length := by
          have valuesEqual :=
            congrArg (fun value : Std.Usize => value.val) namedAtEnd
          simpa [namedIndexEq, alloc.vec.Vec.len, parameterEq] using valuesEqual
        cases defaultEq : signature.keyword_only.val[index.val].default_value with
        | none =>
            step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
              have vectorBound := signature.keyword_only.property
              omega
            have referenceEq : (index.val + 1, true) = expected := by
              simpa [keywordOnlyMissingAt, namedAtEndNat, defaultEq] using
                referenceStep
            simp [parameterEq, defaultEq, nextIndexEq]
            exact ⟨by omega, referenceEq, by omega⟩
        | some default =>
            step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
              have vectorBound := signature.keyword_only.property
              omega
            have referenceEq :
                keywordOnlyMissingScanReference
                  (signature.keyword_only.val.drop (index.val + 1)) call
                  (index.val + 1) false = expected := by
              simpa [keywordOnlyMissingAt, namedAtEndNat, defaultEq] using
                referenceStep
            simp [parameterEq, defaultEq, nextIndexEq]
            exact ⟨by omega, referenceEq, by omega⟩
      · simp only [namedAtEnd, if_false]
        have namedNotAtEndNat : namedActualIndexReference
            (alloc.vec.Vec.deref call.named)
            signature.keyword_only.val[index.val].name ≠
              call.named.val.length := by
          intro valuesEqual
          apply namedAtEnd
          apply UScalar.eq_of_val_eq
          simpa [namedIndexEq, alloc.vec.Vec.len, parameterEq] using valuesEqual
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have vectorBound := signature.keyword_only.property
          omega
        have referenceEq :
            keywordOnlyMissingScanReference
              (signature.keyword_only.val.drop (index.val + 1)) call
              (index.val + 1) false = expected := by
          simpa [keywordOnlyMissingAt, namedNotAtEndNat, parameterEq] using
            referenceStep
        simp only [nextIndexEq]
        exact ⟨by omega, referenceEq, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : signature.keyword_only.val.length ≤ index.val := by
      simpa [alloc.vec.Vec.len] using indexWithin
    have atEnd : index.val = signature.keyword_only.val.length := by omega
    have expectedEq := invariant.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    simpa [atEnd] using expectedEq

theorem first_missing_keyword_only_loop_matches_reference
    {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value)
    (index : Std.Usize) (isMissing : Bool)
    (indexBound : index.val ≤ signature.keyword_only.val.length) :
    WP.spec
      (BindCallFull.first_missing_keyword_only_loop
        signature call index isMissing)
      (fun output =>
        output.1 = signature.keyword_only ∧
          keywordOnlyMissingOutputView output =
            keywordOnlyMissingScanReference
              (signature.keyword_only.val.drop index.val)
              call index.val isMissing) := by
  let expected := keywordOnlyMissingScanReference
    (signature.keyword_only.val.drop index.val) call index.val isMissing
  have initialInvariant : keywordOnlyMissingInvariant
      signature.keyword_only call expected (index, isMissing) :=
    ⟨indexBound, rfl⟩
  unfold BindCallFull.first_missing_keyword_only_loop
  apply loop.spec_decr_nat
      (measure := fun state =>
        keywordOnlyMissingRemaining signature.keyword_only state.1)
      (inv := keywordOnlyMissingInvariant
        signature.keyword_only call expected)
      (post := fun output =>
        output.1 = signature.keyword_only ∧
          keywordOnlyMissingOutputView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_missing_keyword_only_loop_body_preserves_reference_and_decreases
      signature call expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem keywordOnlyMissingScanReference_true_bounds {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value) (index : Nat)
    (foundTrue :
      (keywordOnlyMissingScanReference remaining call index false).2 = true) :
    index < (keywordOnlyMissingScanReference remaining call index false).1 ∧
      (keywordOnlyMissingScanReference remaining call index false).1 ≤
        index + remaining.length := by
  induction remaining generalizing index with
  | nil => simp at foundTrue
  | cons parameter tail inductionHypothesis =>
      rw [keywordOnlyMissingScanReference_cons_false] at foundTrue ⊢
      by_cases missingHere : keywordOnlyMissingAt call parameter = true
      · simp [missingHere]
      · have notMissingHere := Bool.eq_false_of_not_eq_true missingHere
        simp only [notMissingHere, Bool.false_eq_true, if_false] at foundTrue ⊢
        have tailBounds := inductionHypothesis (index + 1) foundTrue
        simp only [List.length_cons]
        omega

def firstMissingKeywordOnlyReference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value) :
    Option (BindCallFull.BindingError String) :=
  let scan := keywordOnlyMissingScanReference
    signature.keyword_only.val call 0 false
  if scan.2 then
    (signature.keyword_only.val[scan.1 - 1]?).map
      (fun parameter =>
        BindCallFull.BindingError.MissingRequiredArgument parameter.name)
  else
    none

theorem first_missing_keyword_only_matches_reference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value) :
    WP.spec (BindCallFull.first_missing_keyword_only
      (totalIdentityClone String) signature call)
      (fun output => output = firstMissingKeywordOnlyReference signature call) := by
  unfold BindCallFull.first_missing_keyword_only
  apply WP.spec_bind
  · exact first_missing_keyword_only_loop_matches_reference
      signature call 0#usize false (by simp)
  · rintro ⟨parameters, index, isMissing⟩ ⟨parametersEq, scanEq⟩
    simp only [Prod.fst, Prod.snd] at parametersEq scanEq
    let scan := keywordOnlyMissingScanReference
      signature.keyword_only.val call 0 false
    have scanEq' : (index.val, isMissing) = scan := scanEq
    have indexEq : index.val = scan.1 := congrArg Prod.fst scanEq'
    by_cases missingTrue : isMissing = true
    · simp [missingTrue]
      have scanFoundTrue : scan.2 = true := by
        rw [← scanEq']
        exact missingTrue
      have scanBounds := keywordOnlyMissingScanReference_true_bounds
        signature.keyword_only.val call 0 scanFoundTrue
      have indexPositive : 0 < index.val := by
        rw [indexEq]
        exact scanBounds.1
      step with Std.Usize.sub_spec as ⟨parameterIndex, parameterIndexEq⟩ by
        simpa using indexPositive
      have scanUpper : scan.1 ≤ signature.keyword_only.val.length := by
        simpa [scan] using scanBounds.2
      have scanPredLt : scan.1 - 1 < scan.1 := by omega
      have scanIndexBound :
          scan.1 - 1 < signature.keyword_only.val.length :=
        lt_of_lt_of_le scanPredLt scanUpper
      have parameterIndexBound :
          parameterIndex.val < signature.keyword_only.val.length := by
        rw [parameterIndexEq, indexEq]
        exact scanIndexBound
      rw [parametersEq]
      step with alloc.vec.Vec.index_usize_spec as
        ⟨parameter, parameterEq⟩ by exact parameterIndexBound
      rw [string_clone_exact]
      unfold firstMissingKeywordOnlyReference
      change some (BindCallFull.BindingError.MissingRequiredArgument parameter.name) =
        if scan.2 = true then
          (signature.keyword_only.val[scan.1 - 1]?).map
            (fun formal =>
              BindCallFull.BindingError.MissingRequiredArgument formal.name)
        else none
      rw [scanFoundTrue]
      simp only [if_true]
      rw [List.getElem?_eq_getElem scanIndexBound]
      have parameterIndexEq' : parameterIndex.val = scan.1 - 1 := by
        rw [parameterIndexEq, indexEq]
      have parameterEq' : parameter =
          signature.keyword_only.val[scan.1 - 1] := by
        simpa [parameterIndexEq'] using parameterEq
      simpa [parameterEq']
    · have missingFalse := Bool.eq_false_of_not_eq_true missingTrue
      simp only [missingFalse, Bool.false_eq_true, if_false]
      unfold firstMissingKeywordOnlyReference
      have scanFoundFalse : scan.2 = false := by
        rw [← scanEq']
        exact missingFalse
      change none = if scan.2 = true then _ else none
      rw [scanFoundFalse]
      simp

def ordinaryMissingAt {value : Type}
    (call : BindCallFull.ExpandedCall String value)
    (parameter : BindCallFull.FormalParameter String value)
    (absoluteIndex : Nat) : Bool :=
  if call.positional.val.length ≤ absoluteIndex then
    if namedActualIndexReference (alloc.vec.Vec.deref call.named)
        parameter.name = call.named.val.length then
      parameter.default_value.isNone
    else
      false
  else
    false

def ordinaryMissingScanReference {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (positionalOffset parameterIndex : Nat) (isMissing : Bool) : Nat × Bool :=
  if isMissing then
    (parameterIndex, true)
  else
    match remaining with
    | [] => (parameterIndex, false)
    | parameter :: tail =>
        if ordinaryMissingAt call parameter
            (positionalOffset + parameterIndex) then
          (parameterIndex + 1, true)
        else
          ordinaryMissingScanReference tail call positionalOffset
            (parameterIndex + 1) false
termination_by remaining.length

@[simp]
theorem ordinaryMissingScanReference_found_true {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (positionalOffset parameterIndex : Nat) :
    ordinaryMissingScanReference remaining call positionalOffset
      parameterIndex true = (parameterIndex, true) := by
  cases remaining <;>
    simp [ordinaryMissingScanReference.eq_1,
      ordinaryMissingScanReference.eq_2]

@[simp]
theorem ordinaryMissingScanReference_empty {value : Type}
    (call : BindCallFull.ExpandedCall String value)
    (positionalOffset parameterIndex : Nat) (isMissing : Bool) :
    ordinaryMissingScanReference
      ([] : List (BindCallFull.FormalParameter String value)) call
      positionalOffset parameterIndex isMissing = (parameterIndex, isMissing) := by
  cases isMissing <;> simp [ordinaryMissingScanReference.eq_1]

@[simp]
theorem ordinaryMissingScanReference_cons_false {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (tail : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (positionalOffset parameterIndex : Nat) :
    ordinaryMissingScanReference (parameter :: tail) call positionalOffset
      parameterIndex false =
        if ordinaryMissingAt call parameter
            (positionalOffset + parameterIndex) then
          (parameterIndex + 1, true)
        else
          ordinaryMissingScanReference tail call positionalOffset
            (parameterIndex + 1) false := by
  simp [ordinaryMissingScanReference.eq_2]

def ordinaryMissingRemaining {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (index : Std.Usize) : Nat :=
  parameters.val.length - index.val

def ordinaryMissingInvariant {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (positionalOffset : Std.Usize) (expected : Nat × Bool)
    (state : Std.Usize × Bool) : Prop :=
  state.1.val ≤ parameters.val.length ∧
    ordinaryMissingScanReference (parameters.val.drop state.1.val) call
      positionalOffset.val state.1.val state.2 = expected

theorem first_missing_ordinary_loop_body_preserves_reference_and_decreases
    {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (positionalOffset : Std.Usize) (expected : Nat × Bool)
    (state : Std.Usize × Bool)
    (offsetBound : positionalOffset.val + parameters.val.length ≤ Std.Usize.max)
    (invariant : ordinaryMissingInvariant
      parameters call positionalOffset expected state) :
    WP.spec
      (BindCallFull.first_missing_ordinary_loop.body
        parameters call positionalOffset state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => namedActualScanView output = expected
        | .cont next =>
            ordinaryMissingInvariant
                parameters call positionalOffset expected next ∧
              ordinaryMissingRemaining parameters next.1 <
                ordinaryMissingRemaining parameters state.1) := by
  rcases state with ⟨parameterIndex, isMissing⟩
  unfold BindCallFull.first_missing_ordinary_loop.body
  unfold ordinaryMissingInvariant at invariant
  unfold ordinaryMissingInvariant ordinaryMissingRemaining namedActualScanView
  change parameterIndex.val ≤ parameters.val.length ∧
      ordinaryMissingScanReference
        (parameters.val.drop parameterIndex.val) call positionalOffset.val
        parameterIndex.val isMissing = expected at invariant
  by_cases indexWithin : parameterIndex < alloc.vec.Vec.len parameters
  · simp only [indexWithin, if_true]
    by_cases alreadyMissing : isMissing = true
    · have expectedEq : (parameterIndex.val, true) = expected := by
        simpa [alreadyMissing] using invariant.2
      simpa [alreadyMissing] using expectedEq
    · have notMissing := Bool.eq_false_of_not_eq_true alreadyMissing
      simp only [notMissing, Bool.false_eq_true, if_false]
      have natIndexBound : parameterIndex.val < parameters.val.length := by
        simpa [alloc.vec.Vec.len] using indexWithin
      step with Std.Usize.add_spec as ⟨absoluteIndex, absoluteIndexEq⟩ by
        omega
      step with alloc.vec.Vec.index_usize_spec as
        ⟨parameter, parameterEq⟩ by exact natIndexBound
      rw [string_clone_exact]
      step with named_actual_index_matches_reference as
        ⟨namedIndex, namedIndexEq⟩
      have dropStep :
          parameters.val.drop parameterIndex.val =
            parameters.val[parameterIndex.val] ::
              parameters.val.drop (parameterIndex.val + 1) :=
        List.drop_eq_getElem_cons natIndexBound
      have referenceStep := invariant.2
      rw [dropStep] at referenceStep
      simp only [notMissing, ordinaryMissingScanReference_cons_false]
        at referenceStep
      by_cases beyondPositionals :
          absoluteIndex ≥ alloc.vec.Vec.len call.positional
      · simp only [beyondPositionals, if_true]
        by_cases namedAtEnd : namedIndex = alloc.vec.Vec.len call.named
        · simp only [namedAtEnd, if_true]
          have beyondNat : call.positional.val.length ≤
              positionalOffset.val + parameterIndex.val := by
            simpa [alloc.vec.Vec.len, absoluteIndexEq] using beyondPositionals
          have namedAtEndNat : namedActualIndexReference
              (alloc.vec.Vec.deref call.named)
              parameters.val[parameterIndex.val].name = call.named.val.length := by
            have valuesEqual :=
              congrArg (fun value : Std.Usize => value.val) namedAtEnd
            simpa [namedIndexEq, alloc.vec.Vec.len, parameterEq] using valuesEqual
          cases defaultEq : parameters.val[parameterIndex.val].default_value with
          | none =>
              step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
                have vectorBound := parameters.property
                omega
              have referenceEq : (parameterIndex.val + 1, true) = expected := by
                simpa [ordinaryMissingAt, beyondNat, namedAtEndNat, defaultEq]
                  using referenceStep
              simp [parameterEq, defaultEq, nextIndexEq]
              exact ⟨by omega, referenceEq, by omega⟩
          | some default =>
              step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
                have vectorBound := parameters.property
                omega
              have referenceEq : ordinaryMissingScanReference
                  (parameters.val.drop (parameterIndex.val + 1)) call
                  positionalOffset.val (parameterIndex.val + 1) false =
                    expected := by
                simpa [ordinaryMissingAt, beyondNat, namedAtEndNat, defaultEq]
                  using referenceStep
              simp [parameterEq, defaultEq, nextIndexEq]
              exact ⟨by omega, referenceEq, by omega⟩
        · simp only [namedAtEnd, if_false]
          have beyondNat : call.positional.val.length ≤
              positionalOffset.val + parameterIndex.val := by
            simpa [alloc.vec.Vec.len, absoluteIndexEq] using beyondPositionals
          have namedNotAtEndNat : namedActualIndexReference
              (alloc.vec.Vec.deref call.named)
              parameters.val[parameterIndex.val].name ≠ call.named.val.length := by
            intro valuesEqual
            apply namedAtEnd
            apply UScalar.eq_of_val_eq
            simpa [namedIndexEq, alloc.vec.Vec.len, parameterEq] using valuesEqual
          step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
            have vectorBound := parameters.property
            omega
          have referenceEq : ordinaryMissingScanReference
              (parameters.val.drop (parameterIndex.val + 1)) call
              positionalOffset.val (parameterIndex.val + 1) false = expected := by
            simpa [ordinaryMissingAt, beyondNat, namedNotAtEndNat, parameterEq]
              using referenceStep
          simp only [nextIndexEq]
          exact ⟨by omega, referenceEq, by omega⟩
      · simp only [beyondPositionals, if_false]
        have beforeEndNat : ¬ call.positional.val.length ≤
            positionalOffset.val + parameterIndex.val := by
          simpa [alloc.vec.Vec.len, absoluteIndexEq] using beyondPositionals
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have vectorBound := parameters.property
          omega
        have referenceEq : ordinaryMissingScanReference
            (parameters.val.drop (parameterIndex.val + 1)) call
            positionalOffset.val (parameterIndex.val + 1) false = expected := by
          simpa [ordinaryMissingAt, beforeEndNat, parameterEq] using referenceStep
        simp only [nextIndexEq]
        exact ⟨by omega, referenceEq, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : parameters.val.length ≤ parameterIndex.val := by
      simpa [alloc.vec.Vec.len] using indexWithin
    have atEnd : parameterIndex.val = parameters.val.length := by omega
    have expectedEq := invariant.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    simpa [atEnd] using expectedEq

theorem first_missing_ordinary_loop_matches_reference
    {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (positionalOffset parameterIndex : Std.Usize) (isMissing : Bool)
    (indexBound : parameterIndex.val ≤ parameters.val.length)
    (offsetBound : positionalOffset.val + parameters.val.length ≤ Std.Usize.max) :
    WP.spec
      (BindCallFull.first_missing_ordinary_loop parameters call positionalOffset
        parameterIndex isMissing)
      (fun output => namedActualScanView output =
        ordinaryMissingScanReference
          (parameters.val.drop parameterIndex.val) call positionalOffset.val
          parameterIndex.val isMissing) := by
  let expected := ordinaryMissingScanReference
    (parameters.val.drop parameterIndex.val) call positionalOffset.val
    parameterIndex.val isMissing
  have initialInvariant : ordinaryMissingInvariant
      parameters call positionalOffset expected (parameterIndex, isMissing) :=
    ⟨indexBound, rfl⟩
  unfold BindCallFull.first_missing_ordinary_loop
  apply loop.spec_decr_nat
      (measure := fun state => ordinaryMissingRemaining parameters state.1)
      (inv := ordinaryMissingInvariant parameters call positionalOffset expected)
      (post := fun output => namedActualScanView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_missing_ordinary_loop_body_preserves_reference_and_decreases
      parameters call positionalOffset expected state offsetBound stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem ordinaryMissingScanReference_true_bounds {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (positionalOffset parameterIndex : Nat)
    (foundTrue :
      (ordinaryMissingScanReference remaining call positionalOffset
        parameterIndex false).2 = true) :
    parameterIndex <
        (ordinaryMissingScanReference remaining call positionalOffset
          parameterIndex false).1 ∧
      (ordinaryMissingScanReference remaining call positionalOffset
        parameterIndex false).1 ≤ parameterIndex + remaining.length := by
  induction remaining generalizing parameterIndex with
  | nil => simp at foundTrue
  | cons parameter tail inductionHypothesis =>
      rw [ordinaryMissingScanReference_cons_false] at foundTrue ⊢
      by_cases missingHere : ordinaryMissingAt call parameter
          (positionalOffset + parameterIndex) = true
      · simp [missingHere]
      · have notMissingHere := Bool.eq_false_of_not_eq_true missingHere
        simp only [notMissingHere, Bool.false_eq_true, if_false] at foundTrue ⊢
        have tailBounds := inductionHypothesis (parameterIndex + 1) foundTrue
        simp only [List.length_cons]
        omega

def firstMissingOrdinaryReference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value) :
    Option (BindCallFull.BindingError String) :=
  let scan := ordinaryMissingScanReference signature.positional.val call
    signature.positional_only.val.length 0 false
  if scan.2 then
    (signature.positional.val[scan.1 - 1]?).map
      (fun parameter =>
        BindCallFull.BindingError.MissingRequiredArgument parameter.name)
  else
    none

theorem first_missing_ordinary_matches_reference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value)
    (parameterBound : signature.positional_only.val.length +
      signature.positional.val.length ≤ Std.Usize.max) :
    WP.spec (BindCallFull.first_missing_ordinary
      (totalIdentityClone String) signature call)
      (fun output => output = firstMissingOrdinaryReference signature call) := by
  unfold BindCallFull.first_missing_ordinary
  apply WP.spec_bind
  · exact first_missing_ordinary_loop_matches_reference signature.positional
      call (alloc.vec.Vec.len signature.positional_only) 0#usize false
      (by simp) (by simpa [alloc.vec.Vec.len] using parameterBound)
  · rintro ⟨index, isMissing⟩ scanEq
    let scan := ordinaryMissingScanReference signature.positional.val call
      signature.positional_only.val.length 0 false
    have scanEq' : (index.val, isMissing) = scan := scanEq
    have indexEq : index.val = scan.1 := congrArg Prod.fst scanEq'
    by_cases missingTrue : isMissing = true
    · simp [missingTrue]
      have scanFoundTrue : scan.2 = true := by
        rw [← scanEq']
        exact missingTrue
      have scanBounds := ordinaryMissingScanReference_true_bounds
        signature.positional.val call signature.positional_only.val.length
        0 scanFoundTrue
      have indexPositive : 0 < index.val := by
        rw [indexEq]
        exact scanBounds.1
      step with Std.Usize.sub_spec as ⟨parameterIndex, parameterIndexEq⟩ by
        simpa using indexPositive
      have scanUpper : scan.1 ≤ signature.positional.val.length := by
        simpa [scan] using scanBounds.2
      have scanPredLt : scan.1 - 1 < scan.1 := by omega
      have scanIndexBound : scan.1 - 1 < signature.positional.val.length :=
        lt_of_lt_of_le scanPredLt scanUpper
      have parameterIndexBound :
          parameterIndex.val < signature.positional.val.length := by
        rw [parameterIndexEq, indexEq]
        exact scanIndexBound
      step with alloc.vec.Vec.index_usize_spec as
        ⟨parameter, parameterEq⟩ by exact parameterIndexBound
      rw [string_clone_exact]
      unfold firstMissingOrdinaryReference
      change some (BindCallFull.BindingError.MissingRequiredArgument parameter.name) =
        if scan.2 = true then
          (signature.positional.val[scan.1 - 1]?).map
            (fun formal =>
              BindCallFull.BindingError.MissingRequiredArgument formal.name)
        else none
      rw [scanFoundTrue]
      simp only [if_true]
      rw [List.getElem?_eq_getElem scanIndexBound]
      have parameterIndexEq' : parameterIndex.val = scan.1 - 1 := by
        rw [parameterIndexEq, indexEq]
      have parameterEq' : parameter =
          signature.positional.val[scan.1 - 1] := by
        simpa [parameterIndexEq'] using parameterEq
      simpa [parameterEq']
    · have missingFalse := Bool.eq_false_of_not_eq_true missingTrue
      simp only [missingFalse, Bool.false_eq_true, if_false]
      unfold firstMissingOrdinaryReference
      have scanFoundFalse : scan.2 = false := by
        rw [← scanEq']
        exact missingFalse
      change none = if scan.2 = true then _ else none
      rw [scanFoundFalse]
      simp

theorem positionalOnlyMissingScanReference_true_bounds {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value) (index : Nat)
    (foundTrue :
      (positionalOnlyMissingScanReference remaining call index false).2 = true) :
    index < (positionalOnlyMissingScanReference remaining call index false).1 ∧
      (positionalOnlyMissingScanReference remaining call index false).1 ≤
        index + remaining.length := by
  induction remaining generalizing index with
  | nil => simp at foundTrue
  | cons parameter tail inductionHypothesis =>
      rw [positionalOnlyMissingScanReference_cons_false] at foundTrue ⊢
      by_cases missingHere : positionalOnlyMissingAt call parameter index = true
      · simp [missingHere]
      · have notMissingHere := Bool.eq_false_of_not_eq_true missingHere
        simp only [notMissingHere, Bool.false_eq_true, if_false] at foundTrue ⊢
        have tailBounds := inductionHypothesis (index + 1) foundTrue
        simp only [List.length_cons]
        omega

def firstMissingPositionalOnlyReference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value) :
    Option (BindCallFull.BindingError String) :=
  let scan := positionalOnlyMissingScanReference
    signature.positional_only.val call 0 false
  if scan.2 then
    (signature.positional_only.val[scan.1 - 1]?).map
      (fun parameter =>
        BindCallFull.BindingError.MissingRequiredArgument parameter.name)
  else
    none

theorem first_missing_positional_only_matches_reference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value) :
    WP.spec (BindCallFull.first_missing_positional_only
      (totalIdentityClone String) signature call)
      (fun output => output = firstMissingPositionalOnlyReference signature call) := by
  unfold BindCallFull.first_missing_positional_only
  apply WP.spec_bind
  · exact first_missing_positional_only_loop_matches_reference
      signature.positional_only call 0#usize false (by simp)
  · rintro ⟨index, isMissing⟩ scanEq
    let scan := positionalOnlyMissingScanReference
      signature.positional_only.val call 0 false
    have scanEq' : (index.val, isMissing) = scan := scanEq
    have indexEq : index.val = scan.1 := congrArg Prod.fst scanEq'
    by_cases missingTrue : isMissing = true
    · simp [missingTrue]
      have scanFoundTrue : scan.2 = true := by
        rw [← scanEq']
        exact missingTrue
      have scanBounds := positionalOnlyMissingScanReference_true_bounds
        signature.positional_only.val call 0 scanFoundTrue
      have indexPositive : 0 < index.val := by
        rw [indexEq]
        exact scanBounds.1
      step with Std.Usize.sub_spec as ⟨parameterIndex, parameterIndexEq⟩ by
        simpa using indexPositive
      have scanUpper : scan.1 ≤ signature.positional_only.val.length := by
        simpa [scan] using scanBounds.2
      have scanPredLt : scan.1 - 1 < scan.1 := by omega
      have scanIndexBound : scan.1 - 1 <
          signature.positional_only.val.length :=
        lt_of_lt_of_le scanPredLt scanUpper
      have parameterIndexBound : parameterIndex.val <
          signature.positional_only.val.length := by
        rw [parameterIndexEq, indexEq]
        exact scanIndexBound
      step with alloc.vec.Vec.index_usize_spec as
        ⟨parameter, parameterEq⟩ by exact parameterIndexBound
      rw [string_clone_exact]
      unfold firstMissingPositionalOnlyReference
      change some (BindCallFull.BindingError.MissingRequiredArgument parameter.name) =
        if scan.2 = true then
          (signature.positional_only.val[scan.1 - 1]?).map
            (fun formal =>
              BindCallFull.BindingError.MissingRequiredArgument formal.name)
        else none
      rw [scanFoundTrue]
      simp only [if_true]
      rw [List.getElem?_eq_getElem scanIndexBound]
      have parameterIndexEq' : parameterIndex.val = scan.1 - 1 := by
        rw [parameterIndexEq, indexEq]
      have parameterEq' : parameter =
          signature.positional_only.val[scan.1 - 1] := by
        simpa [parameterIndexEq'] using parameterEq
      simpa [parameterEq']
    · have missingFalse := Bool.eq_false_of_not_eq_true missingTrue
      simp only [missingFalse, Bool.false_eq_true, if_false]
      unfold firstMissingPositionalOnlyReference
      have scanFoundFalse : scan.2 = false := by
        rw [← scanEq']
        exact missingFalse
      change none = if scan.2 = true then _ else none
      rw [scanFoundFalse]
      simp

def firstMissingRequiredArgumentReference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value) :
    Option (BindCallFull.BindingError String) :=
  match firstMissingPositionalOnlyReference signature call with
  | some error => some error
  | none =>
      match firstMissingOrdinaryReference signature call with
      | some error => some error
      | none => firstMissingKeywordOnlyReference signature call

theorem first_missing_required_argument_matches_reference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value)
    (parameterBound : signature.positional_only.val.length +
      signature.positional.val.length ≤ Std.Usize.max) :
    WP.spec (BindCallFull.first_missing_required_argument
      (totalIdentityClone String) signature call)
      (fun output =>
        output = firstMissingRequiredArgumentReference signature call) := by
  unfold BindCallFull.first_missing_required_argument
  step with first_missing_positional_only_matches_reference as
    ⟨positionalError, positionalErrorEq⟩
  cases positionalReferenceEq :
      firstMissingPositionalOnlyReference signature call with
  | some error =>
      simp only [positionalReferenceEq] at positionalErrorEq
      simp [positionalErrorEq, firstMissingRequiredArgumentReference,
        positionalReferenceEq]
  | none =>
      simp only [positionalReferenceEq] at positionalErrorEq
      simp only [positionalErrorEq, Option.isNone_none, if_true]
      step with first_missing_ordinary_matches_reference as
        ⟨ordinaryError, ordinaryErrorEq⟩ by exact parameterBound
      cases ordinaryReferenceEq :
          firstMissingOrdinaryReference signature call with
      | some error =>
          simp only [ordinaryReferenceEq] at ordinaryErrorEq
          simp [ordinaryErrorEq, firstMissingRequiredArgumentReference,
            positionalReferenceEq, ordinaryReferenceEq]
      | none =>
          simp only [ordinaryReferenceEq] at ordinaryErrorEq
          simp only [ordinaryErrorEq, Option.isNone_none, if_true]
          apply WP.spec_mono
            (first_missing_keyword_only_matches_reference signature call)
          intro output outputEq
          simpa [firstMissingRequiredArgumentReference, positionalReferenceEq,
            ordinaryReferenceEq] using outputEq

def duplicateBindingAt {value : Type}
    (call : BindCallFull.ExpandedCall String value)
    (parameter : BindCallFull.FormalParameter String value)
    (ordinaryPosition : Nat) : Bool :=
  if ordinaryPosition < call.positional.val.length then
    namedActualIndexReference (alloc.vec.Vec.deref call.named) parameter.name <
      call.named.val.length
  else
    false

def duplicateBindingScanReference {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (ordinaryPosition parameterIndex : Nat) (duplicate : Bool) : Nat × Bool :=
  if duplicate then
    (parameterIndex, true)
  else
    match remaining with
    | [] => (parameterIndex, false)
    | parameter :: tail =>
        if duplicateBindingAt call parameter ordinaryPosition then
          (parameterIndex + 1, true)
        else
          duplicateBindingScanReference tail call (ordinaryPosition + 1)
            (parameterIndex + 1) false
termination_by remaining.length

@[simp]
theorem duplicateBindingScanReference_found_true {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (ordinaryPosition parameterIndex : Nat) :
    duplicateBindingScanReference remaining call ordinaryPosition
      parameterIndex true = (parameterIndex, true) := by
  cases remaining <;>
    simp [duplicateBindingScanReference.eq_1,
      duplicateBindingScanReference.eq_2]

@[simp]
theorem duplicateBindingScanReference_empty {value : Type}
    (call : BindCallFull.ExpandedCall String value)
    (ordinaryPosition parameterIndex : Nat) (duplicate : Bool) :
    duplicateBindingScanReference
      ([] : List (BindCallFull.FormalParameter String value)) call
      ordinaryPosition parameterIndex duplicate = (parameterIndex, duplicate) := by
  cases duplicate <;> simp [duplicateBindingScanReference.eq_1]

@[simp]
theorem duplicateBindingScanReference_cons_false {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (tail : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (ordinaryPosition parameterIndex : Nat) :
    duplicateBindingScanReference (parameter :: tail) call ordinaryPosition
      parameterIndex false =
        if duplicateBindingAt call parameter ordinaryPosition then
          (parameterIndex + 1, true)
        else
          duplicateBindingScanReference tail call (ordinaryPosition + 1)
            (parameterIndex + 1) false := by
  simp [duplicateBindingScanReference.eq_2]

def duplicateBindingRemaining {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (index : Std.Usize) : Nat :=
  parameters.val.length - index.val

def duplicateBindingInvariant {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (expected : Nat × Bool)
    (state : Std.Usize × Std.Usize × Bool) : Prop :=
  state.2.1.val ≤ parameters.val.length ∧
    state.1.val + (parameters.val.length - state.2.1.val) ≤ Std.Usize.max ∧
      duplicateBindingScanReference (parameters.val.drop state.2.1.val) call
        state.1.val state.2.1.val state.2.2 = expected

theorem first_duplicate_binding_loop_body_preserves_reference_and_decreases
    {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (expected : Nat × Bool)
    (state : Std.Usize × Std.Usize × Bool)
    (ordinaryBound : state.1.val +
      (parameters.val.length - state.2.1.val) ≤ Std.Usize.max)
    (invariant : duplicateBindingInvariant parameters call expected state) :
    WP.spec
      (BindCallFull.first_duplicate_binding_loop.body parameters call
        state.1 state.2.1 state.2.2)
      (fun flow =>
        match flow with
        | .done output => namedActualScanView output = expected
        | .cont next =>
            duplicateBindingInvariant parameters call expected next ∧
              duplicateBindingRemaining parameters next.2.1 <
                duplicateBindingRemaining parameters state.2.1) := by
  rcases state with ⟨ordinaryPosition, parameterIndex, duplicate⟩
  unfold BindCallFull.first_duplicate_binding_loop.body
  unfold duplicateBindingInvariant at invariant
  unfold duplicateBindingInvariant duplicateBindingRemaining namedActualScanView
  change parameterIndex.val ≤ parameters.val.length ∧
      ordinaryPosition.val + (parameters.val.length - parameterIndex.val) ≤
          Std.Usize.max ∧
        duplicateBindingScanReference (parameters.val.drop parameterIndex.val)
          call ordinaryPosition.val parameterIndex.val duplicate = expected at invariant
  by_cases indexWithin : parameterIndex < alloc.vec.Vec.len parameters
  · simp only [indexWithin, if_true]
    by_cases alreadyDuplicate : duplicate = true
    · have expectedEq : (parameterIndex.val, true) = expected := by
        simpa [alreadyDuplicate] using invariant.2.2
      simpa [alreadyDuplicate] using expectedEq
    · have notDuplicate := Bool.eq_false_of_not_eq_true alreadyDuplicate
      simp only [notDuplicate, Bool.false_eq_true, if_false]
      have natIndexBound : parameterIndex.val < parameters.val.length := by
        simpa [alloc.vec.Vec.len] using indexWithin
      step with alloc.vec.Vec.index_usize_spec as
        ⟨parameter, parameterEq⟩ by exact natIndexBound
      have dropStep : parameters.val.drop parameterIndex.val =
          parameters.val[parameterIndex.val] ::
            parameters.val.drop (parameterIndex.val + 1) :=
        List.drop_eq_getElem_cons natIndexBound
      have referenceStep := invariant.2.2
      rw [dropStep] at referenceStep
      simp only [notDuplicate, duplicateBindingScanReference_cons_false]
        at referenceStep
      by_cases hasPositional : ordinaryPosition < alloc.vec.Vec.len call.positional
      · simp only [hasPositional, if_true]
        step with named_actual_index_matches_reference as
          ⟨namedIndex, namedIndexEq⟩
        by_cases namedPresent : namedIndex < alloc.vec.Vec.len call.named
        · simp only [namedPresent]
          have positionalNat : ordinaryPosition.val < call.positional.val.length := by
            simpa [alloc.vec.Vec.len] using hasPositional
          have namedNat : namedActualIndexReference
              (alloc.vec.Vec.deref call.named)
              parameters.val[parameterIndex.val].name < call.named.val.length := by
            simpa [namedIndexEq, alloc.vec.Vec.len, parameterEq] using namedPresent
          step with Std.Usize.add_spec as
            ⟨nextOrdinaryPosition, nextOrdinaryEq⟩ by omega
          step with Std.Usize.add_spec as ⟨nextParameterIndex, nextParameterEq⟩ by
            have vectorBound := parameters.property
            omega
          have referenceEq : (parameterIndex.val + 1, true) = expected := by
            simpa [duplicateBindingAt, positionalNat, namedNat] using referenceStep
          simp only [nextOrdinaryEq, nextParameterEq]
          simp only [decide_true, duplicateBindingScanReference_found_true]
          exact ⟨by omega, by omega, referenceEq, by omega⟩
        · simp only [namedPresent]
          have positionalNat : ordinaryPosition.val < call.positional.val.length := by
            simpa [alloc.vec.Vec.len] using hasPositional
          have namedNotPresent : ¬ namedActualIndexReference
              (alloc.vec.Vec.deref call.named)
              parameters.val[parameterIndex.val].name < call.named.val.length := by
            simpa [namedIndexEq, alloc.vec.Vec.len, parameterEq] using namedPresent
          step with Std.Usize.add_spec as
            ⟨nextOrdinaryPosition, nextOrdinaryEq⟩ by omega
          step with Std.Usize.add_spec as ⟨nextParameterIndex, nextParameterEq⟩ by
            have vectorBound := parameters.property
            omega
          have referenceEq : duplicateBindingScanReference
              (parameters.val.drop (parameterIndex.val + 1)) call
              (ordinaryPosition.val + 1) (parameterIndex.val + 1) false =
                expected := by
            simpa [duplicateBindingAt, positionalNat, namedNotPresent,
              parameterEq] using referenceStep
          simp only [nextOrdinaryEq, nextParameterEq]
          exact ⟨by omega, by omega, referenceEq, by omega⟩
      · simp only [hasPositional, if_false]
        have noPositional : ¬ ordinaryPosition.val < call.positional.val.length := by
          simpa [alloc.vec.Vec.len] using hasPositional
        step with Std.Usize.add_spec as
          ⟨nextOrdinaryPosition, nextOrdinaryEq⟩ by omega
        step with Std.Usize.add_spec as ⟨nextParameterIndex, nextParameterEq⟩ by
          have vectorBound := parameters.property
          omega
        have referenceEq : duplicateBindingScanReference
            (parameters.val.drop (parameterIndex.val + 1)) call
            (ordinaryPosition.val + 1) (parameterIndex.val + 1) false = expected := by
          simpa [duplicateBindingAt, noPositional, parameterEq] using referenceStep
        simp only [nextOrdinaryEq, nextParameterEq]
        exact ⟨by omega, by omega, referenceEq, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : parameters.val.length ≤ parameterIndex.val := by
      simpa [alloc.vec.Vec.len] using indexWithin
    have atEnd : parameterIndex.val = parameters.val.length := by omega
    have expectedEq := invariant.2.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    simpa [atEnd] using expectedEq

theorem first_duplicate_binding_loop_matches_reference {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (ordinaryPosition parameterIndex : Std.Usize) (duplicate : Bool)
    (indexBound : parameterIndex.val ≤ parameters.val.length)
    (ordinaryBound : ordinaryPosition.val +
      (parameters.val.length - parameterIndex.val) ≤ Std.Usize.max) :
    WP.spec
      (BindCallFull.first_duplicate_binding_loop parameters call
        ordinaryPosition parameterIndex duplicate)
      (fun output => namedActualScanView output =
        duplicateBindingScanReference (parameters.val.drop parameterIndex.val)
          call ordinaryPosition.val parameterIndex.val duplicate) := by
  let expected := duplicateBindingScanReference
    (parameters.val.drop parameterIndex.val) call ordinaryPosition.val
    parameterIndex.val duplicate
  have initialInvariant : duplicateBindingInvariant parameters call expected
      (ordinaryPosition, parameterIndex, duplicate) :=
    ⟨indexBound, ordinaryBound, rfl⟩
  unfold BindCallFull.first_duplicate_binding_loop
  apply loop.spec_decr_nat
      (measure := fun state => duplicateBindingRemaining parameters state.2.1)
      (inv := duplicateBindingInvariant parameters call expected)
      (post := fun output => namedActualScanView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  have stateOrdinaryBound : state.1.val +
      (parameters.val.length - state.2.1.val) ≤ Std.Usize.max := by
    exact stateInvariant.2.1
  apply WP.spec_mono
    (first_duplicate_binding_loop_body_preserves_reference_and_decreases
      parameters call expected state stateOrdinaryBound stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem duplicateBindingScanReference_true_bounds {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (call : BindCallFull.ExpandedCall String value)
    (ordinaryPosition parameterIndex : Nat)
    (foundTrue :
      (duplicateBindingScanReference remaining call ordinaryPosition
        parameterIndex false).2 = true) :
    parameterIndex <
        (duplicateBindingScanReference remaining call ordinaryPosition
          parameterIndex false).1 ∧
      (duplicateBindingScanReference remaining call ordinaryPosition
        parameterIndex false).1 ≤ parameterIndex + remaining.length := by
  induction remaining generalizing ordinaryPosition parameterIndex with
  | nil => simp at foundTrue
  | cons parameter tail inductionHypothesis =>
      rw [duplicateBindingScanReference_cons_false] at foundTrue ⊢
      by_cases duplicateHere :
          duplicateBindingAt call parameter ordinaryPosition = true
      · simp [duplicateHere]
      · have notDuplicateHere := Bool.eq_false_of_not_eq_true duplicateHere
        simp only [notDuplicateHere, Bool.false_eq_true, if_false] at foundTrue ⊢
        have tailBounds := inductionHypothesis (ordinaryPosition + 1)
          (parameterIndex + 1) foundTrue
        simp only [List.length_cons]
        omega

def firstDuplicateBindingReference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value) :
    Option (BindCallFull.BindingError String) :=
  let scan := duplicateBindingScanReference signature.positional.val call
    signature.positional_only.val.length 0 false
  if scan.2 then
    (signature.positional.val[scan.1 - 1]?).map
      (fun parameter => BindCallFull.BindingError.DuplicateBinding parameter.name)
  else
    none

theorem first_duplicate_binding_matches_reference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value)
    (parameterBound : signature.positional_only.val.length +
      signature.positional.val.length ≤ Std.Usize.max) :
    WP.spec (BindCallFull.first_duplicate_binding
      (totalIdentityClone String) signature call)
      (fun output => output = firstDuplicateBindingReference signature call) := by
  unfold BindCallFull.first_duplicate_binding
  apply WP.spec_bind
  · exact first_duplicate_binding_loop_matches_reference signature.positional
      call (alloc.vec.Vec.len signature.positional_only) 0#usize false
      (by simp) (by simpa [alloc.vec.Vec.len] using parameterBound)
  · rintro ⟨index, duplicate⟩ scanEq
    let scan := duplicateBindingScanReference signature.positional.val call
      signature.positional_only.val.length 0 false
    have scanEq' : (index.val, duplicate) = scan := scanEq
    have indexEq : index.val = scan.1 := congrArg Prod.fst scanEq'
    by_cases duplicateTrue : duplicate = true
    · simp [duplicateTrue]
      have scanFoundTrue : scan.2 = true := by
        rw [← scanEq']
        exact duplicateTrue
      have scanBounds := duplicateBindingScanReference_true_bounds
        signature.positional.val call signature.positional_only.val.length
        0 scanFoundTrue
      have indexPositive : 0 < index.val := by
        rw [indexEq]
        exact scanBounds.1
      step with Std.Usize.sub_spec as ⟨parameterIndex, parameterIndexEq⟩ by
        simpa using indexPositive
      have scanUpper : scan.1 ≤ signature.positional.val.length := by
        simpa [scan] using scanBounds.2
      have scanPredLt : scan.1 - 1 < scan.1 := by omega
      have scanIndexBound : scan.1 - 1 < signature.positional.val.length :=
        lt_of_lt_of_le scanPredLt scanUpper
      have parameterIndexBound :
          parameterIndex.val < signature.positional.val.length := by
        rw [parameterIndexEq, indexEq]
        exact scanIndexBound
      step with alloc.vec.Vec.index_usize_spec as
        ⟨parameter, parameterEq⟩ by exact parameterIndexBound
      rw [string_clone_exact]
      unfold firstDuplicateBindingReference
      change some (BindCallFull.BindingError.DuplicateBinding parameter.name) =
        if scan.2 = true then
          (signature.positional.val[scan.1 - 1]?).map
            (fun formal => BindCallFull.BindingError.DuplicateBinding formal.name)
        else none
      rw [scanFoundTrue]
      simp only [if_true]
      rw [List.getElem?_eq_getElem scanIndexBound]
      have parameterIndexEq' : parameterIndex.val = scan.1 - 1 := by
        rw [parameterIndexEq, indexEq]
      have parameterEq' : parameter =
          signature.positional.val[scan.1 - 1] := by
        simpa [parameterIndexEq'] using parameterEq
      simpa [parameterEq']
    · have duplicateFalse := Bool.eq_false_of_not_eq_true duplicateTrue
      simp only [duplicateFalse, Bool.false_eq_true, if_false]
      unfold firstDuplicateBindingReference
      have scanFoundFalse : scan.2 = false := by
        rw [← scanEq']
        exact duplicateFalse
      change none = if scan.2 = true then _ else none
      rw [scanFoundFalse]
      simp

def extraPositionalMismatchAt {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (actual : BindCallFull.PositionalActual String value) : Bool :=
  if parameter.expected_type == actual.value.type_tag then false else true

def extraPositionalMismatchScanReference {value : Type}
    (remaining : List (BindCallFull.PositionalActual String value))
    (parameter : BindCallFull.FormalParameter String value)
    (index : Nat) (mismatch : Bool) : Nat × Bool :=
  if mismatch then
    (index, true)
  else
    match remaining with
    | [] => (index, false)
    | actual :: tail =>
        if extraPositionalMismatchAt parameter actual then
          (index + 1, true)
        else
          extraPositionalMismatchScanReference tail parameter (index + 1) false
termination_by remaining.length

@[simp]
theorem extraPositionalMismatchScanReference_found_true {value : Type}
    (remaining : List (BindCallFull.PositionalActual String value))
    (parameter : BindCallFull.FormalParameter String value) (index : Nat) :
    extraPositionalMismatchScanReference remaining parameter index true =
      (index, true) := by
  cases remaining <;>
    simp [extraPositionalMismatchScanReference.eq_1,
      extraPositionalMismatchScanReference.eq_2]

@[simp]
theorem extraPositionalMismatchScanReference_empty {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (index : Nat) (mismatch : Bool) :
    extraPositionalMismatchScanReference
      ([] : List (BindCallFull.PositionalActual String value))
      parameter index mismatch = (index, mismatch) := by
  cases mismatch <;> simp [extraPositionalMismatchScanReference.eq_1]

@[simp]
theorem extraPositionalMismatchScanReference_cons_false {value : Type}
    (actual : BindCallFull.PositionalActual String value)
    (tail : List (BindCallFull.PositionalActual String value))
    (parameter : BindCallFull.FormalParameter String value) (index : Nat) :
    extraPositionalMismatchScanReference (actual :: tail) parameter index false =
      if extraPositionalMismatchAt parameter actual then
        (index + 1, true)
      else
        extraPositionalMismatchScanReference tail parameter (index + 1) false := by
  simp [extraPositionalMismatchScanReference.eq_2]

def extraPositionalMismatchRemaining {value : Type}
    (actuals : alloc.vec.Vec
      (BindCallFull.PositionalActual String value))
    (index : Std.Usize) : Nat :=
  actuals.val.length - index.val

def extraPositionalMismatchInvariant {value : Type}
    (actuals : alloc.vec.Vec
      (BindCallFull.PositionalActual String value))
    (parameter : BindCallFull.FormalParameter String value)
    (expected : Nat × Bool) (state : Std.Usize × Bool) : Prop :=
  state.1.val ≤ actuals.val.length ∧
    extraPositionalMismatchScanReference (actuals.val.drop state.1.val)
      parameter state.1.val state.2 = expected

def extraPositionalMismatchOutputView {value : Type}
    (output : BindCallFull.FormalParameter String value ×
      alloc.vec.Vec (BindCallFull.PositionalActual String value) ×
        Std.Usize × Bool) : Nat × Bool :=
  (output.2.2.1.val, output.2.2.2)

theorem first_extra_positional_type_mismatch_loop_body_preserves_reference_and_decreases
    {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (call : BindCallFull.ExpandedCall String value)
    (expected : Nat × Bool) (state : Std.Usize × Bool)
    (invariant : extraPositionalMismatchInvariant
      call.positional parameter expected state) :
    WP.spec
      (BindCallFull.first_extra_positional_type_mismatch_loop.body
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameter call () state.1 state.2)
      (fun flow =>
        match flow with
        | .done output =>
            output.1 = parameter ∧ output.2.1 = call.positional ∧
              extraPositionalMismatchOutputView output = expected
        | .cont next =>
            extraPositionalMismatchInvariant
                call.positional parameter expected next ∧
              extraPositionalMismatchRemaining call.positional next.1 <
                extraPositionalMismatchRemaining call.positional state.1) := by
  rcases state with ⟨index, mismatch⟩
  unfold BindCallFull.first_extra_positional_type_mismatch_loop.body
  unfold extraPositionalMismatchInvariant at invariant
  unfold extraPositionalMismatchInvariant extraPositionalMismatchRemaining
    extraPositionalMismatchOutputView
  change index.val ≤ call.positional.val.length ∧
      extraPositionalMismatchScanReference (call.positional.val.drop index.val)
        parameter index.val mismatch = expected at invariant
  by_cases indexWithin : index < alloc.vec.Vec.len call.positional
  · simp only [indexWithin, if_true]
    by_cases alreadyMismatch : mismatch = true
    · have expectedEq : (index.val, true) = expected := by
        simpa [alreadyMismatch] using invariant.2
      simpa [alreadyMismatch] using expectedEq
    · have noMismatch := Bool.eq_false_of_not_eq_true alreadyMismatch
      simp only [noMismatch, Bool.false_eq_true, if_false]
      have natIndexBound : index.val < call.positional.val.length := by
        simpa [alloc.vec.Vec.len] using indexWithin
      step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
        exact natIndexBound
      rw [compatibility_mismatch_string_exact]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        have vectorBound := call.positional.property
        omega
      have dropStep : call.positional.val.drop index.val =
          call.positional.val[index.val] ::
            call.positional.val.drop (index.val + 1) :=
        List.drop_eq_getElem_cons natIndexBound
      have referenceStep := invariant.2
      rw [dropStep] at referenceStep
      simp only [noMismatch,
        extraPositionalMismatchScanReference_cons_false] at referenceStep
      by_cases typesEqual :
          parameter.expected_type = call.positional.val[index.val].value.type_tag
      · have equalityTrue :
            (parameter.expected_type ==
              call.positional.val[index.val].value.type_tag) = true := by
          simpa using typesEqual
        have referenceEq : extraPositionalMismatchScanReference
            (call.positional.val.drop (index.val + 1)) parameter
            (index.val + 1) false = expected := by
          simpa [extraPositionalMismatchAt, typesEqual] using referenceStep
        simp only [actualEq, equalityTrue, if_true, nextIndexEq]
        exact ⟨by omega, referenceEq, by omega⟩
      · have equalityFalse :
            (parameter.expected_type ==
              call.positional.val[index.val].value.type_tag) = false := by
          simpa using typesEqual
        have referenceEq : (index.val + 1, true) = expected := by
          simpa [extraPositionalMismatchAt, typesEqual] using referenceStep
        simp only [actualEq, equalityFalse, if_false, nextIndexEq,
          Bool.false_eq_true, extraPositionalMismatchScanReference_found_true]
        exact ⟨by omega, referenceEq, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : call.positional.val.length ≤ index.val := by
      simpa [alloc.vec.Vec.len] using indexWithin
    have atEnd : index.val = call.positional.val.length := by omega
    have expectedEq := invariant.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    simpa [atEnd] using expectedEq

theorem first_extra_positional_type_mismatch_loop_matches_reference
    {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (call : BindCallFull.ExpandedCall String value)
    (index : Std.Usize) (mismatch : Bool)
    (indexBound : index.val ≤ call.positional.val.length) :
    WP.spec
      (BindCallFull.first_extra_positional_type_mismatch_loop
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameter call () index mismatch)
      (fun output =>
        output.1 = parameter ∧ output.2.1 = call.positional ∧
          extraPositionalMismatchOutputView output =
            extraPositionalMismatchScanReference
              (call.positional.val.drop index.val) parameter index.val mismatch) := by
  let expected := extraPositionalMismatchScanReference
    (call.positional.val.drop index.val) parameter index.val mismatch
  have initialInvariant : extraPositionalMismatchInvariant
      call.positional parameter expected (index, mismatch) := ⟨indexBound, rfl⟩
  unfold BindCallFull.first_extra_positional_type_mismatch_loop
  apply loop.spec_decr_nat
      (measure := fun state =>
        extraPositionalMismatchRemaining call.positional state.1)
      (inv := extraPositionalMismatchInvariant call.positional parameter expected)
      (post := fun output =>
        output.1 = parameter ∧ output.2.1 = call.positional ∧
          extraPositionalMismatchOutputView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_extra_positional_type_mismatch_loop_body_preserves_reference_and_decreases
      parameter call expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem extraPositionalMismatchScanReference_true_bounds {value : Type}
    (remaining : List (BindCallFull.PositionalActual String value))
    (parameter : BindCallFull.FormalParameter String value) (index : Nat)
    (foundTrue :
      (extraPositionalMismatchScanReference remaining parameter index false).2 =
        true) :
    index <
        (extraPositionalMismatchScanReference remaining parameter index false).1 ∧
      (extraPositionalMismatchScanReference remaining parameter index false).1 ≤
        index + remaining.length := by
  induction remaining generalizing index with
  | nil => simp at foundTrue
  | cons actual tail inductionHypothesis =>
      rw [extraPositionalMismatchScanReference_cons_false] at foundTrue ⊢
      by_cases mismatchHere : extraPositionalMismatchAt parameter actual = true
      · simp [mismatchHere]
      · have noMismatchHere := Bool.eq_false_of_not_eq_true mismatchHere
        simp only [noMismatchHere, Bool.false_eq_true, if_false] at foundTrue ⊢
        have tailBounds := inductionHypothesis (index + 1) foundTrue
        simp only [List.length_cons]
        omega

def firstExtraPositionalTypeMismatchReference {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (call : BindCallFull.ExpandedCall String value)
    (positionalCount : Nat) : Option (BindCallFull.BindingError String) :=
  let scan := extraPositionalMismatchScanReference
    (call.positional.val.drop positionalCount) parameter positionalCount false
  if scan.2 then
    (call.positional.val[scan.1 - 1]?).map
      (fun actual => BindCallFull.BindingError.TypeMismatch parameter.name
        parameter.expected_type actual.value.type_tag
        (some actual.evaluation_position))
  else
    none

theorem first_extra_positional_type_mismatch_matches_reference {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (call : BindCallFull.ExpandedCall String value)
    (positionalCount : Std.Usize)
    (indexBound : positionalCount.val ≤ call.positional.val.length) :
    WP.spec
      (BindCallFull.first_extra_positional_type_mismatch
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameter call positionalCount ())
      (fun output => output =
        firstExtraPositionalTypeMismatchReference parameter call
          positionalCount.val) := by
  unfold BindCallFull.first_extra_positional_type_mismatch
  apply WP.spec_bind
  · exact first_extra_positional_type_mismatch_loop_matches_reference
      parameter call positionalCount false indexBound
  · rintro ⟨parameterAfter, actuals, index, mismatch⟩
      ⟨parameterEq, actualsEq, scanEq⟩
    simp only [Prod.fst, Prod.snd] at parameterEq actualsEq scanEq
    let scan := extraPositionalMismatchScanReference
      (call.positional.val.drop positionalCount.val) parameter
      positionalCount.val false
    have scanEq' : (index.val, mismatch) = scan := scanEq
    have indexEq : index.val = scan.1 := congrArg Prod.fst scanEq'
    by_cases mismatchTrue : mismatch = true
    · simp [mismatchTrue]
      have scanFoundTrue : scan.2 = true := by
        rw [← scanEq']
        exact mismatchTrue
      have scanBounds := extraPositionalMismatchScanReference_true_bounds
        (call.positional.val.drop positionalCount.val) parameter
        positionalCount.val scanFoundTrue
      have indexPositive : 0 < index.val := by
        rw [indexEq]
        exact lt_of_le_of_lt (Nat.zero_le positionalCount.val) scanBounds.1
      step with Std.Usize.sub_spec as ⟨actualIndex, actualIndexEq⟩ by
        simpa using indexPositive
      have scanUpper : scan.1 ≤ call.positional.val.length := by
        have scanUpperRelative := scanBounds.2
        simp only [List.length_drop] at scanUpperRelative
        rw [Nat.add_sub_of_le indexBound] at scanUpperRelative
        exact scanUpperRelative
      have scanPredLt : scan.1 - 1 < scan.1 := by omega
      have scanIndexBound : scan.1 - 1 < call.positional.val.length :=
        lt_of_lt_of_le scanPredLt scanUpper
      have actualIndexBound : actualIndex.val < call.positional.val.length := by
        rw [actualIndexEq, indexEq]
        exact scanIndexBound
      rw [parameterEq, actualsEq]
      step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
        exact actualIndexBound
      rw [string_clone_exact, totalIdentityClone_exact,
        totalIdentityClone_exact]
      unfold firstExtraPositionalTypeMismatchReference
      change some (BindCallFull.BindingError.TypeMismatch parameter.name
          parameter.expected_type actual.value.type_tag
          (some actual.evaluation_position)) =
        if scan.2 = true then
          (call.positional.val[scan.1 - 1]?).map
            (fun candidate => BindCallFull.BindingError.TypeMismatch
              parameter.name parameter.expected_type candidate.value.type_tag
              (some candidate.evaluation_position))
        else none
      rw [scanFoundTrue]
      simp only [if_true]
      rw [List.getElem?_eq_getElem scanIndexBound]
      have actualIndexEq' : actualIndex.val = scan.1 - 1 := by
        rw [actualIndexEq, indexEq]
      have actualEq' : actual = call.positional.val[scan.1 - 1] := by
        simpa [actualIndexEq'] using actualEq
      simpa [actualEq']
    · have mismatchFalse := Bool.eq_false_of_not_eq_true mismatchTrue
      simp only [mismatchFalse, Bool.false_eq_true, if_false]
      unfold firstExtraPositionalTypeMismatchReference
      have scanFoundFalse : scan.2 = false := by
        rw [← scanEq']
        exact mismatchFalse
      change none = if scan.2 = true then _ else none
      rw [scanFoundFalse]
      simp

theorem first_extra_positional_type_mismatch_beyond_end
    (parameter : BindCallFull.FormalParameter String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalCount : Std.Usize)
    (exhausted : call.positional.val.length ≤ positionalCount.val) :
    WP.spec
      (BindCallFull.first_extra_positional_type_mismatch
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameter call positionalCount ())
      (fun output => output = none) := by
  unfold BindCallFull.first_extra_positional_type_mismatch
  apply WP.spec_bind
  · unfold BindCallFull.first_extra_positional_type_mismatch_loop
    apply loop.spec_decr_nat
        (measure := fun (_ : Std.Usize × Bool) => 0)
        (inv := fun state => state.1 = positionalCount ∧ state.2 = false)
        (post := fun output => output =
          (parameter, call.positional, positionalCount, false))
        (hInv := by simp)
    intro state stateInvariant
    rcases state with ⟨index, mismatch⟩
    simp only [Prod.fst, Prod.snd] at stateInvariant
    unfold BindCallFull.first_extra_positional_type_mismatch_loop.body
    have notWithin : ¬positionalCount < alloc.vec.Vec.len call.positional := by
      simpa [alloc.vec.Vec.len] using exhausted
    simp [stateInvariant.1, stateInvariant.2, notWithin,
      WP.spec, WP.theta, WP.wp_return]
  · rintro ⟨parameterAfter, actualsAfter, indexAfter, mismatchAfter⟩ outputEq
    simp [outputEq, WP.spec, WP.theta, WP.wp_return]

def extraNamedMismatchAt {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value)
    (actual : BindCallFull.NamedActual String value) : Bool :=
  if ordinaryNameReference signature actual.name then
    false
  else if parameter.expected_type == actual.value.type_tag then
    false
  else
    true

def extraNamedMismatchScanReference {value : Type}
    (remaining : List (BindCallFull.NamedActual String value))
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value)
    (index : Nat) (mismatch : Bool) : Nat × Bool :=
  if mismatch then
    (index, true)
  else
    match remaining with
    | [] => (index, false)
    | actual :: tail =>
        if extraNamedMismatchAt parameter signature actual then
          (index + 1, true)
        else
          extraNamedMismatchScanReference tail parameter signature
            (index + 1) false
termination_by remaining.length

@[simp]
theorem extraNamedMismatchScanReference_found_true {value : Type}
    (remaining : List (BindCallFull.NamedActual String value))
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value) (index : Nat) :
    extraNamedMismatchScanReference remaining parameter signature index true =
      (index, true) := by
  cases remaining <;>
    simp [extraNamedMismatchScanReference.eq_1,
      extraNamedMismatchScanReference.eq_2]

@[simp]
theorem extraNamedMismatchScanReference_empty {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value)
    (index : Nat) (mismatch : Bool) :
    extraNamedMismatchScanReference
      ([] : List (BindCallFull.NamedActual String value))
      parameter signature index mismatch = (index, mismatch) := by
  cases mismatch <;> simp [extraNamedMismatchScanReference.eq_1]

@[simp]
theorem extraNamedMismatchScanReference_cons_false {value : Type}
    (actual : BindCallFull.NamedActual String value)
    (tail : List (BindCallFull.NamedActual String value))
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value) (index : Nat) :
    extraNamedMismatchScanReference (actual :: tail) parameter signature
      index false =
        if extraNamedMismatchAt parameter signature actual then
          (index + 1, true)
        else
          extraNamedMismatchScanReference tail parameter signature
            (index + 1) false := by
  simp [extraNamedMismatchScanReference.eq_2]

def extraNamedMismatchRemaining {value : Type}
    (actuals : alloc.vec.Vec (BindCallFull.NamedActual String value))
    (index : Std.Usize) : Nat :=
  actuals.val.length - index.val

def extraNamedMismatchInvariant {value : Type}
    (actuals : alloc.vec.Vec (BindCallFull.NamedActual String value))
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value)
    (expected : Nat × Bool)
    (state : BindCallFull.FormalParameter String value ×
      Std.Usize × Bool) : Prop :=
  state.1 = parameter ∧ state.2.1.val ≤ actuals.val.length ∧
    extraNamedMismatchScanReference (actuals.val.drop state.2.1.val)
      parameter signature state.2.1.val state.2.2 = expected

def extraNamedMismatchOutputView {value : Type}
    (output : BindCallFull.FormalParameter String value ×
      alloc.vec.Vec (BindCallFull.NamedActual String value) ×
        Std.Usize × Bool) : Nat × Bool :=
  (output.2.2.1.val, output.2.2.2)

theorem first_extra_named_type_mismatch_loop_body_preserves_reference_and_decreases
    {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value)
    (expected : Nat × Bool)
    (state : BindCallFull.FormalParameter String value ×
      Std.Usize × Bool)
    (invariant : extraNamedMismatchInvariant
      call.named parameter signature expected state) :
    WP.spec
      (BindCallFull.first_extra_named_type_mismatch_loop.body
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature call () state.1 state.2.1 state.2.2)
      (fun flow =>
        match flow with
        | .done output =>
            output.1 = parameter ∧ output.2.1 = call.named ∧
              extraNamedMismatchOutputView output = expected
        | .cont next =>
            extraNamedMismatchInvariant
                call.named parameter signature expected next ∧
              extraNamedMismatchRemaining call.named next.2.1 <
                extraNamedMismatchRemaining call.named state.2.1) := by
  rcases state with ⟨stateParameter, index, mismatch⟩
  have stateParameterEq : stateParameter = parameter := invariant.1
  subst stateParameter
  have invariant := invariant.2
  unfold BindCallFull.first_extra_named_type_mismatch_loop.body
  unfold extraNamedMismatchInvariant at invariant
  unfold extraNamedMismatchInvariant extraNamedMismatchRemaining
    extraNamedMismatchOutputView
  change index.val ≤ call.named.val.length ∧
      extraNamedMismatchScanReference (call.named.val.drop index.val)
        parameter signature index.val mismatch = expected at invariant
  by_cases indexWithin : index < alloc.vec.Vec.len call.named
  · simp only [indexWithin, if_true]
    by_cases alreadyMismatch : mismatch = true
    · have expectedEq : (index.val, true) = expected := by
        simpa [alreadyMismatch] using invariant.2
      simpa [alreadyMismatch] using expectedEq
    · have noMismatch := Bool.eq_false_of_not_eq_true alreadyMismatch
      simp only [noMismatch, Bool.false_eq_true, if_false]
      have natIndexBound : index.val < call.named.val.length := by
        simpa [alloc.vec.Vec.len] using indexWithin
      step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
        exact natIndexBound
      rw [string_clone_exact]
      step with ordinary_parameter_name_matches_reference as
        ⟨isOrdinary, ordinaryEq⟩
      have dropStep : call.named.val.drop index.val =
          call.named.val[index.val] :: call.named.val.drop (index.val + 1) :=
        List.drop_eq_getElem_cons natIndexBound
      have referenceStep := invariant.2
      rw [dropStep] at referenceStep
      simp only [noMismatch, extraNamedMismatchScanReference_cons_false]
        at referenceStep
      by_cases ordinary : ordinaryNameReference signature
          call.named.val[index.val].name = true
      · have ordinaryTrue : isOrdinary = true := by
          calc
            isOrdinary = ordinaryNameReference signature actual.name := by
              simpa [ordinaryNameReference] using ordinaryEq
            _ = true := by simpa [actualEq] using ordinary
        simp only [ordinaryTrue, if_true]
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have vectorBound := call.named.property
          omega
        have referenceEq : extraNamedMismatchScanReference
            (call.named.val.drop (index.val + 1)) parameter signature
            (index.val + 1) false = expected := by
          simpa [extraNamedMismatchAt, ordinary, actualEq] using referenceStep
        simp only [nextIndexEq]
        exact ⟨by omega, referenceEq, by omega⟩
      · have ordinaryFalse : ordinaryNameReference signature
            call.named.val[index.val].name = false :=
          Bool.eq_false_of_not_eq_true ordinary
        have isOrdinaryFalse : isOrdinary = false := by
          calc
            isOrdinary = ordinaryNameReference signature actual.name := by
              simpa [ordinaryNameReference] using ordinaryEq
            _ = false := by simpa [actualEq] using ordinaryFalse
        simp only [isOrdinaryFalse, Bool.false_eq_true, if_false]
        rw [compatibility_mismatch_string_exact]
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have vectorBound := call.named.property
          omega
        by_cases typesEqual :
            parameter.expected_type = call.named.val[index.val].value.type_tag
        · have equalityTrue :
              (parameter.expected_type ==
                call.named.val[index.val].value.type_tag) = true := by
            simpa using typesEqual
          have referenceEq : extraNamedMismatchScanReference
              (call.named.val.drop (index.val + 1)) parameter signature
              (index.val + 1) false = expected := by
            simpa [extraNamedMismatchAt, ordinaryFalse, typesEqual] using
              referenceStep
          simp only [actualEq, equalityTrue, if_true, nextIndexEq]
          exact ⟨by omega, referenceEq, by omega⟩
        · have equalityFalse :
              (parameter.expected_type ==
                call.named.val[index.val].value.type_tag) = false := by
            simpa using typesEqual
          have referenceEq : (index.val + 1, true) = expected := by
            simpa [extraNamedMismatchAt, ordinaryFalse, typesEqual] using
              referenceStep
          simp only [actualEq, equalityFalse, if_false, Bool.false_eq_true,
            nextIndexEq, extraNamedMismatchScanReference_found_true]
          exact ⟨by omega, referenceEq, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : call.named.val.length ≤ index.val := by
      simpa [alloc.vec.Vec.len] using indexWithin
    have atEnd : index.val = call.named.val.length := by omega
    have expectedEq := invariant.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    simpa [atEnd] using expectedEq

theorem first_extra_named_type_mismatch_loop_matches_reference
    {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value)
    (index : Std.Usize) (mismatch : Bool)
    (indexBound : index.val ≤ call.named.val.length) :
    WP.spec
      (BindCallFull.first_extra_named_type_mismatch_loop
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameter signature call () index mismatch)
      (fun output =>
        output.1 = parameter ∧ output.2.1 = call.named ∧
          extraNamedMismatchOutputView output =
            extraNamedMismatchScanReference (call.named.val.drop index.val)
              parameter signature index.val mismatch) := by
  let expected := extraNamedMismatchScanReference
    (call.named.val.drop index.val) parameter signature index.val mismatch
  have initialInvariant : extraNamedMismatchInvariant
      call.named parameter signature expected (parameter, index, mismatch) :=
    ⟨rfl, indexBound, rfl⟩
  unfold BindCallFull.first_extra_named_type_mismatch_loop
  apply loop.spec_decr_nat
      (measure := fun state => extraNamedMismatchRemaining call.named state.2.1)
      (inv := extraNamedMismatchInvariant call.named parameter signature expected)
      (post := fun output =>
        output.1 = parameter ∧ output.2.1 = call.named ∧
          extraNamedMismatchOutputView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_extra_named_type_mismatch_loop_body_preserves_reference_and_decreases
      parameter signature call expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem extraNamedMismatchScanReference_true_bounds {value : Type}
    (remaining : List (BindCallFull.NamedActual String value))
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value) (index : Nat)
    (foundTrue :
      (extraNamedMismatchScanReference remaining parameter signature
        index false).2 = true) :
    index <
        (extraNamedMismatchScanReference remaining parameter signature
          index false).1 ∧
      (extraNamedMismatchScanReference remaining parameter signature
        index false).1 ≤ index + remaining.length := by
  induction remaining generalizing index with
  | nil => simp at foundTrue
  | cons actual tail inductionHypothesis =>
      rw [extraNamedMismatchScanReference_cons_false] at foundTrue ⊢
      by_cases mismatchHere :
          extraNamedMismatchAt parameter signature actual = true
      · simp [mismatchHere]
      · have noMismatchHere := Bool.eq_false_of_not_eq_true mismatchHere
        simp only [noMismatchHere, Bool.false_eq_true, if_false] at foundTrue ⊢
        have tailBounds := inductionHypothesis (index + 1) foundTrue
        simp only [List.length_cons]
        omega

def firstExtraNamedTypeMismatchReference {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value) :
    Option (BindCallFull.BindingError String) :=
  let scan := extraNamedMismatchScanReference call.named.val parameter signature
    0 false
  if scan.2 then
    (call.named.val[scan.1 - 1]?).map
      (fun actual => BindCallFull.BindingError.TypeMismatch parameter.name
        parameter.expected_type actual.value.type_tag
        (some actual.evaluation_position))
  else
    none

theorem first_extra_named_type_mismatch_matches_reference {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value) :
    WP.spec
      (BindCallFull.first_extra_named_type_mismatch
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameter signature call ())
      (fun output => output =
        firstExtraNamedTypeMismatchReference parameter signature call) := by
  unfold BindCallFull.first_extra_named_type_mismatch
  apply WP.spec_bind
  · exact first_extra_named_type_mismatch_loop_matches_reference
      parameter signature call 0#usize false (by simp)
  · rintro ⟨parameterAfter, actuals, index, mismatch⟩
      ⟨parameterEq, actualsEq, scanEq⟩
    simp only [Prod.fst, Prod.snd] at parameterEq actualsEq scanEq
    let scan := extraNamedMismatchScanReference call.named.val parameter
      signature 0 false
    have scanEq' : (index.val, mismatch) = scan := scanEq
    have indexEq : index.val = scan.1 := congrArg Prod.fst scanEq'
    by_cases mismatchTrue : mismatch = true
    · simp [mismatchTrue]
      have scanFoundTrue : scan.2 = true := by
        rw [← scanEq']
        exact mismatchTrue
      have scanBounds := extraNamedMismatchScanReference_true_bounds
        call.named.val parameter signature 0 scanFoundTrue
      have indexPositive : 0 < index.val := by
        rw [indexEq]
        exact scanBounds.1
      step with Std.Usize.sub_spec as ⟨actualIndex, actualIndexEq⟩ by
        simpa using indexPositive
      have scanUpper : scan.1 ≤ call.named.val.length := by
        simpa [scan] using scanBounds.2
      have scanPredLt : scan.1 - 1 < scan.1 := by omega
      have scanIndexBound : scan.1 - 1 < call.named.val.length :=
        lt_of_lt_of_le scanPredLt scanUpper
      have actualIndexBound : actualIndex.val < call.named.val.length := by
        rw [actualIndexEq, indexEq]
        exact scanIndexBound
      rw [parameterEq, actualsEq]
      step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
        exact actualIndexBound
      rw [string_clone_exact, totalIdentityClone_exact,
        totalIdentityClone_exact]
      unfold firstExtraNamedTypeMismatchReference
      change some (BindCallFull.BindingError.TypeMismatch parameter.name
          parameter.expected_type actual.value.type_tag
          (some actual.evaluation_position)) =
        if scan.2 = true then
          (call.named.val[scan.1 - 1]?).map
            (fun candidate => BindCallFull.BindingError.TypeMismatch
              parameter.name parameter.expected_type candidate.value.type_tag
              (some candidate.evaluation_position))
        else none
      rw [scanFoundTrue]
      simp only [if_true]
      rw [List.getElem?_eq_getElem scanIndexBound]
      have actualIndexEq' : actualIndex.val = scan.1 - 1 := by
        rw [actualIndexEq, indexEq]
      have actualEq' : actual = call.named.val[scan.1 - 1] := by
        simpa [actualIndexEq'] using actualEq
      simpa [actualEq']
    · have mismatchFalse := Bool.eq_false_of_not_eq_true mismatchTrue
      simp only [mismatchFalse, Bool.false_eq_true, if_false]
      unfold firstExtraNamedTypeMismatchReference
      have scanFoundFalse : scan.2 = false := by
        rw [← scanEq']
        exact mismatchFalse
      change none = if scan.2 = true then _ else none
      rw [scanFoundFalse]
      simp

def firstVariadicTypeMismatchReference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value)
    (positionalCount : Nat) : Option (BindCallFull.BindingError String) :=
  let positionalError :=
    match signature.var_args with
    | none => none
    | some parameter =>
        firstExtraPositionalTypeMismatchReference parameter call positionalCount
  match positionalError with
  | some error => some error
  | none =>
      match signature.keyword_args with
      | none => none
      | some parameter =>
          firstExtraNamedTypeMismatchReference parameter signature call

theorem first_variadic_type_mismatch_matches_reference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (call : BindCallFull.ExpandedCall String value)
    (positionalCount : Std.Usize)
    (indexBound : positionalCount.val ≤ call.positional.val.length) :
    WP.spec
      (BindCallFull.first_variadic_type_mismatch
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature call positionalCount ())
      (fun output => output =
        firstVariadicTypeMismatchReference signature call positionalCount.val) := by
  unfold BindCallFull.first_variadic_type_mismatch
  cases varArgsEq : signature.var_args with
  | none =>
      simp only [varArgsEq]
      cases keywordArgsEq : signature.keyword_args with
      | none =>
          simp [firstVariadicTypeMismatchReference, varArgsEq, keywordArgsEq]
      | some parameter =>
          simp only [Option.isNone_none, if_true, keywordArgsEq]
          apply WP.spec_mono
            (first_extra_named_type_mismatch_matches_reference
              parameter signature call)
          intro output outputEq
          simpa [firstVariadicTypeMismatchReference, varArgsEq, keywordArgsEq]
            using outputEq
  | some positionalParameter =>
      simp only [varArgsEq]
      step with first_extra_positional_type_mismatch_matches_reference as
        ⟨positionalError, positionalErrorEq⟩ by exact indexBound
      cases positionalReferenceEq : firstExtraPositionalTypeMismatchReference
          positionalParameter call positionalCount.val with
      | some error =>
          simp only [positionalReferenceEq] at positionalErrorEq
          simp [positionalErrorEq, firstVariadicTypeMismatchReference,
            varArgsEq, positionalReferenceEq]
      | none =>
          simp only [positionalReferenceEq] at positionalErrorEq
          simp only [positionalErrorEq, Option.isNone_none, if_true]
          cases keywordArgsEq : signature.keyword_args with
          | none =>
              simp [firstVariadicTypeMismatchReference, varArgsEq,
                positionalReferenceEq, keywordArgsEq]
          | some keywordParameter =>
              simp only [keywordArgsEq]
              apply WP.spec_mono
                (first_extra_named_type_mismatch_matches_reference
                  keywordParameter signature call)
              intro output outputEq
              simpa [firstVariadicTypeMismatchReference, varArgsEq,
                positionalReferenceEq, keywordArgsEq] using outputEq

theorem first_variadic_type_mismatch_matches_reference_total
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalCount : Std.Usize) :
    WP.spec
      (BindCallFull.first_variadic_type_mismatch
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature call positionalCount ())
      (fun output => output =
        firstVariadicTypeMismatchReference signature call positionalCount.val) := by
  by_cases indexBound : positionalCount.val ≤ call.positional.val.length
  · exact first_variadic_type_mismatch_matches_reference signature call
      positionalCount indexBound
  · have exhausted : call.positional.val.length ≤ positionalCount.val := by omega
    unfold BindCallFull.first_variadic_type_mismatch
    cases varArgsEq : signature.var_args with
    | none =>
        simp only [varArgsEq]
        cases keywordArgsEq : signature.keyword_args with
        | none =>
            simp [firstVariadicTypeMismatchReference, varArgsEq, keywordArgsEq]
        | some parameter =>
            simp only [Option.isNone_none, if_true, keywordArgsEq]
            apply WP.spec_mono
              (first_extra_named_type_mismatch_matches_reference
                parameter signature call)
            intro output outputEq
            simpa [firstVariadicTypeMismatchReference, varArgsEq, keywordArgsEq]
              using outputEq
    | some positionalParameter =>
        simp only [varArgsEq]
        step with first_extra_positional_type_mismatch_beyond_end as
          ⟨positionalError, positionalErrorEq⟩ by exact exhausted
        have positionalReferenceNone :
            firstExtraPositionalTypeMismatchReference positionalParameter call
              positionalCount.val = none := by
          unfold firstExtraPositionalTypeMismatchReference
          have dropped : call.positional.val.drop positionalCount.val = [] :=
            List.drop_eq_nil_iff.mpr exhausted
          simp [extraPositionalMismatchScanReference, dropped]
        simp only [positionalErrorEq, Option.isNone_none, if_true]
        cases keywordArgsEq : signature.keyword_args with
        | none =>
            simp [firstVariadicTypeMismatchReference, varArgsEq,
              positionalReferenceNone, keywordArgsEq]
        | some keywordParameter =>
            simp only [keywordArgsEq]
            apply WP.spec_mono
              (first_extra_named_type_mismatch_matches_reference
                keywordParameter signature call)
            intro output outputEq
            simpa [firstVariadicTypeMismatchReference, varArgsEq,
              positionalReferenceNone, keywordArgsEq] using outputEq

def positionalOnlyMismatchScanReference {value : Type}
    (parameters : List (BindCallFull.FormalParameter String value))
    (actuals : List (BindCallFull.PositionalActual String value))
    (remaining index : Nat) (mismatch : Bool) : Nat × Bool :=
  if mismatch then
    (index, true)
  else
    match remaining with
    | 0 => (index, false)
    | remaining + 1 =>
        match parameters, actuals with
        | parameter :: parameterTail, actual :: actualTail =>
            if parameter.expected_type == actual.value.type_tag then
              positionalOnlyMismatchScanReference parameterTail actualTail
                remaining (index + 1) false
            else
              (index + 1, true)
        | _, _ => (index, false)
termination_by remaining

@[simp]
theorem positionalOnlyMismatchScanReference_found_true {value : Type}
    (parameters : List (BindCallFull.FormalParameter String value))
    (actuals : List (BindCallFull.PositionalActual String value))
    (remaining index : Nat) :
    positionalOnlyMismatchScanReference parameters actuals remaining index true =
      (index, true) := by
  rw [positionalOnlyMismatchScanReference.eq_def]
  simp

@[simp]
theorem positionalOnlyMismatchScanReference_zero {value : Type}
    (parameters : List (BindCallFull.FormalParameter String value))
    (actuals : List (BindCallFull.PositionalActual String value))
    (index : Nat) (mismatch : Bool) :
    positionalOnlyMismatchScanReference parameters actuals 0 index mismatch =
      (index, mismatch) := by
  cases mismatch <;> cases parameters <;> cases actuals <;>
    simp [positionalOnlyMismatchScanReference.eq_1,
      positionalOnlyMismatchScanReference.eq_2]

@[simp]
theorem positionalOnlyMismatchScanReference_succ_cons_false {value : Type}
    (parameter : BindCallFull.FormalParameter String value)
    (parameterTail : List (BindCallFull.FormalParameter String value))
    (actual : BindCallFull.PositionalActual String value)
    (actualTail : List (BindCallFull.PositionalActual String value))
    (remaining index : Nat) :
    positionalOnlyMismatchScanReference (parameter :: parameterTail)
      (actual :: actualTail) (remaining + 1) index false =
        if parameter.expected_type == actual.value.type_tag then
          positionalOnlyMismatchScanReference parameterTail actualTail remaining
            (index + 1) false
        else
          (index + 1, true) := by
  simp [positionalOnlyMismatchScanReference.eq_2]

def positionalOnlyMismatchRemaining (comparableCount : Std.Usize)
    (index : Std.Usize) : Nat :=
  comparableCount.val - index.val

def positionalOnlyMismatchInvariant {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (actuals : alloc.vec.Vec (BindCallFull.PositionalActual String value))
    (comparableCount : Std.Usize) (expected : Nat × Bool)
    (state : Std.Usize × Bool) : Prop :=
  state.1.val ≤ comparableCount.val ∧
    comparableCount.val ≤ parameters.val.length ∧
    comparableCount.val ≤ actuals.val.length ∧
    positionalOnlyMismatchScanReference
      (parameters.val.drop state.1.val) (actuals.val.drop state.1.val)
      (comparableCount.val - state.1.val) state.1.val state.2 = expected

theorem first_positional_only_type_mismatch_loop_body_preserves_reference_and_decreases
    {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (actuals : alloc.vec.Vec (BindCallFull.PositionalActual String value))
    (comparableCount : Std.Usize) (expected : Nat × Bool)
    (state : Std.Usize × Bool)
    (invariant : positionalOnlyMismatchInvariant parameters actuals
      comparableCount expected state) :
    WP.spec
      (BindCallFull.first_positional_only_type_mismatch_loop.body
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters actuals () comparableCount state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => namedActualScanView output = expected
        | .cont next =>
            positionalOnlyMismatchInvariant parameters actuals
                comparableCount expected next ∧
              positionalOnlyMismatchRemaining comparableCount next.1 <
                positionalOnlyMismatchRemaining comparableCount state.1) := by
  rcases state with ⟨index, mismatch⟩
  unfold BindCallFull.first_positional_only_type_mismatch_loop.body
  unfold positionalOnlyMismatchInvariant at invariant
  unfold positionalOnlyMismatchInvariant positionalOnlyMismatchRemaining
    namedActualScanView
  change index.val ≤ comparableCount.val ∧
      comparableCount.val ≤ parameters.val.length ∧
      comparableCount.val ≤ actuals.val.length ∧
      positionalOnlyMismatchScanReference
        (parameters.val.drop index.val) (actuals.val.drop index.val)
        (comparableCount.val - index.val) index.val mismatch = expected at invariant
  by_cases indexWithin : index < comparableCount
  · simp only [indexWithin, if_true]
    by_cases alreadyMismatch : mismatch = true
    · have expectedEq : (index.val, true) = expected := by
        simpa [alreadyMismatch] using invariant.2.2.2
      simpa [alreadyMismatch] using expectedEq
    · have noMismatch := Bool.eq_false_of_not_eq_true alreadyMismatch
      simp only [noMismatch, Bool.false_eq_true, if_false]
      have parameterBound : index.val < parameters.val.length := by
        have withinNat : index.val < comparableCount.val := by simpa using indexWithin
        omega
      have actualBound : index.val < actuals.val.length := by
        have withinNat : index.val < comparableCount.val := by simpa using indexWithin
        omega
      step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
        exact parameterBound
      step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
        exact actualBound
      rw [compatibility_mismatch_string_exact]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        have comparableMachineBound := comparableCount.property
        have withinNat : index.val < comparableCount.val := by simpa using indexWithin
        omega
      have parameterDrop : parameters.val.drop index.val =
          parameters.val[index.val] :: parameters.val.drop (index.val + 1) :=
        List.drop_eq_getElem_cons parameterBound
      have actualDrop : actuals.val.drop index.val =
          actuals.val[index.val] :: actuals.val.drop (index.val + 1) :=
        List.drop_eq_getElem_cons actualBound
      have remainingPositive : 0 < comparableCount.val - index.val := by
        have withinNat : index.val < comparableCount.val := by simpa using indexWithin
        omega
      have remainingStep : comparableCount.val - index.val =
          (comparableCount.val - (index.val + 1)) + 1 := by omega
      have referenceStep := invariant.2.2.2
      rw [parameterDrop, actualDrop, remainingStep] at referenceStep
      simp only [noMismatch,
        positionalOnlyMismatchScanReference_succ_cons_false] at referenceStep
      by_cases typesEqual :
          parameters.val[index.val].expected_type =
            actuals.val[index.val].value.type_tag
      · have equalityTrue :
            (parameters.val[index.val].expected_type ==
              actuals.val[index.val].value.type_tag) = true := by
          simpa using typesEqual
        have referenceEq : positionalOnlyMismatchScanReference
            (parameters.val.drop (index.val + 1))
            (actuals.val.drop (index.val + 1))
            (comparableCount.val - (index.val + 1)) (index.val + 1) false =
              expected := by
          simpa [typesEqual] using referenceStep
        simp only [parameterEq, actualEq, equalityTrue, if_true, nextIndexEq]
        exact ⟨by omega, invariant.2.1, invariant.2.2.1,
          referenceEq, by omega⟩
      · have equalityFalse :
            (parameters.val[index.val].expected_type ==
              actuals.val[index.val].value.type_tag) = false := by
          simpa using typesEqual
        have referenceEq : (index.val + 1, true) = expected := by
          simpa [typesEqual] using referenceStep
        simp only [parameterEq, actualEq, equalityFalse, if_false,
          Bool.false_eq_true, nextIndexEq,
          positionalOnlyMismatchScanReference_found_true]
        exact ⟨by omega, invariant.2.1, invariant.2.2.1,
          referenceEq, by omega⟩
  · simp only [indexWithin, if_false]
    have atEnd : index.val = comparableCount.val := by
      have notWithin : ¬ index.val < comparableCount.val := by simpa using indexWithin
      omega
    have expectedEq := invariant.2.2.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    simpa [atEnd] using expectedEq

theorem first_positional_only_type_mismatch_loop_matches_reference
    {value : Type}
    (parameters : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (actuals : alloc.vec.Vec (BindCallFull.PositionalActual String value))
    (comparableCount index : Std.Usize) (mismatch : Bool)
    (indexBound : index.val ≤ comparableCount.val)
    (parameterBound : comparableCount.val ≤ parameters.val.length)
    (actualBound : comparableCount.val ≤ actuals.val.length) :
    WP.spec
      (BindCallFull.first_positional_only_type_mismatch_loop
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters actuals () comparableCount index mismatch)
      (fun output => namedActualScanView output =
        positionalOnlyMismatchScanReference (parameters.val.drop index.val)
          (actuals.val.drop index.val) (comparableCount.val - index.val)
          index.val mismatch) := by
  let expected := positionalOnlyMismatchScanReference
    (parameters.val.drop index.val) (actuals.val.drop index.val)
    (comparableCount.val - index.val) index.val mismatch
  have initialInvariant : positionalOnlyMismatchInvariant parameters actuals
      comparableCount expected (index, mismatch) :=
    ⟨indexBound, parameterBound, actualBound, rfl⟩
  unfold BindCallFull.first_positional_only_type_mismatch_loop
  apply loop.spec_decr_nat
      (measure := fun state =>
        positionalOnlyMismatchRemaining comparableCount state.1)
      (inv := positionalOnlyMismatchInvariant parameters actuals
        comparableCount expected)
      (post := fun output => namedActualScanView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_positional_only_type_mismatch_loop_body_preserves_reference_and_decreases
      parameters actuals comparableCount expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem positionalOnlyMismatchScanReference_true_bounds {value : Type}
    (parameters : List (BindCallFull.FormalParameter String value))
    (actuals : List (BindCallFull.PositionalActual String value))
    (remaining index : Nat)
    (parameterBound : remaining ≤ parameters.length)
    (actualBound : remaining ≤ actuals.length)
    (foundTrue :
      (positionalOnlyMismatchScanReference parameters actuals remaining
        index false).2 = true) :
    index <
        (positionalOnlyMismatchScanReference parameters actuals remaining
          index false).1 ∧
      (positionalOnlyMismatchScanReference parameters actuals remaining
          index false).1 ≤ index + remaining := by
  induction remaining generalizing parameters actuals index with
  | zero => simp at foundTrue
  | succ remaining inductionHypothesis =>
      cases parameters with
      | nil => simp at parameterBound
      | cons parameter parameterTail =>
          cases actuals with
          | nil => simp at actualBound
          | cons actual actualTail =>
              rw [positionalOnlyMismatchScanReference_succ_cons_false]
              by_cases typesEqual :
                  parameter.expected_type = actual.value.type_tag
              · have equalityTrue :
                    (parameter.expected_type == actual.value.type_tag) = true := by
                  simpa using typesEqual
                simp only [equalityTrue, if_true]
                have nextFound :
                    (positionalOnlyMismatchScanReference parameterTail actualTail
                      remaining (index + 1) false).2 = true := by
                  simpa [equalityTrue] using foundTrue
                have nextBounds := inductionHypothesis parameterTail actualTail
                  (index + 1) (by simpa using parameterBound)
                  (by simpa using actualBound) nextFound
                omega
              · have equalityFalse :
                    (parameter.expected_type == actual.value.type_tag) = false := by
                  simpa using typesEqual
                simp [equalityFalse]

def firstPositionalOnlyTypeMismatchReference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int) :
    Option (BindCallFull.BindingError String) :=
  let comparableCount :=
    Nat.min signature.positional_only.val.length call.positional.val.length
  let scan := positionalOnlyMismatchScanReference
    signature.positional_only.val call.positional.val comparableCount 0 false
  if scan.2 then
    match signature.positional_only.val[scan.1 - 1]?,
        call.positional.val[scan.1 - 1]? with
    | some parameter, some actual =>
        some (BindCallFull.BindingError.TypeMismatch parameter.name
          parameter.expected_type actual.value.type_tag
          (some actual.evaluation_position))
    | _, _ => none
  else
    none

theorem first_positional_only_type_mismatch_matches_reference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int) :
    WP.spec
      (BindCallFull.first_positional_only_type_mismatch
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature call ())
      (fun output => output =
        firstPositionalOnlyTypeMismatchReference signature call) := by
  unfold BindCallFull.first_positional_only_type_mismatch
  step as ⟨comparable, comparableEq⟩
  ·
    have comparableNat : comparable.val =
        Nat.min signature.positional_only.val.length call.positional.val.length := by
      rw [comparableEq]
      simp only [core.cmp.impls.OrdUsize.min,
        core.cmp.impls.PartialOrdUsize.lt, alloc.vec.Vec.len]
      split_ifs with lengthsLt
      · have lengthsLtNat : signature.positional_only.val.length <
            call.positional.val.length := by simpa using lengthsLt
        simpa [Nat.min_eq_left (Nat.le_of_lt lengthsLtNat)]
      · have lengthsNotLtNat : ¬signature.positional_only.val.length <
            call.positional.val.length := by simpa using lengthsLt
        simpa [Nat.min_eq_right (Nat.le_of_not_gt lengthsNotLtNat)]
    apply WP.spec_bind
    · apply first_positional_only_type_mismatch_loop_matches_reference
      · simp
      · rw [comparableNat]
        exact Nat.min_le_left _ _
      · rw [comparableNat]
        exact Nat.min_le_right _ _
    · rintro ⟨index, mismatch⟩ scanEq
      change (index.val, mismatch) =
        positionalOnlyMismatchScanReference signature.positional_only.val
          call.positional.val
          comparable.val
          0 false at scanEq
      let scan := positionalOnlyMismatchScanReference
        signature.positional_only.val call.positional.val comparable.val 0 false
      have scanEq' : (index.val, mismatch) = scan := scanEq
      by_cases mismatchTrue : mismatch = true
      · simp [mismatchTrue]
        have scanTrue : scan.2 = true := by
          rw [← scanEq']
          exact mismatchTrue
        have scanBounds := positionalOnlyMismatchScanReference_true_bounds
          signature.positional_only.val call.positional.val comparable.val 0
          (by rw [comparableNat]; exact Nat.min_le_left _ _)
          (by rw [comparableNat]; exact Nat.min_le_right _ _) scanTrue
        have indexEq : index.val = scan.1 := congrArg Prod.fst scanEq'
        have indexPositive : 0 < index.val := by
          rw [← indexEq] at scanBounds
          exact scanBounds.1
        step with Std.Usize.sub_spec as ⟨mismatchIndex, mismatchIndexEq⟩ by
          simpa using indexPositive
        have mismatchIndexNat : mismatchIndex.val = scan.1 - 1 := by
          rw [mismatchIndexEq]
          exact congrArg (fun value : Nat => value - 1)
            (congrArg Prod.fst scanEq')
        have scanUpperParameter : scan.1 ≤
            signature.positional_only.val.length := by
          have scanLeComparable : scan.1 ≤ comparable.val := by
            simpa using scanBounds.2
          have comparableLe : comparable.val ≤
              signature.positional_only.val.length := by
            rw [comparableNat]
            exact Nat.min_le_left _ _
          exact le_trans scanLeComparable comparableLe
        have scanUpperActual : scan.1 ≤ call.positional.val.length :=
          le_trans (by simpa using scanBounds.2) (by
            rw [comparableNat]
            exact Nat.min_le_right _ _)
        have parameterIndexBound : mismatchIndex.val <
            signature.positional_only.val.length := by omega
        have actualIndexBound : mismatchIndex.val < call.positional.val.length := by
          omega
        step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
          exact parameterIndexBound
        step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
          exact actualIndexBound
        rw [string_clone_exact, totalIdentityClone_exact,
          totalIdentityClone_exact]
        unfold firstPositionalOnlyTypeMismatchReference
        rw [← comparableNat]
        change some (BindCallFull.BindingError.TypeMismatch parameter.name
            parameter.expected_type actual.value.type_tag
            (some actual.evaluation_position)) =
          if scan.2 = true then _ else none
        rw [scanTrue]
        simp only [if_true]
        rw [List.getElem?_eq_getElem (by omega : scan.1 - 1 <
          signature.positional_only.val.length)]
        rw [List.getElem?_eq_getElem (by omega : scan.1 - 1 <
          call.positional.val.length)]
        simp [parameterEq, actualEq, mismatchIndexNat]
      · have mismatchFalse : mismatch = false :=
          Bool.eq_false_of_not_eq_true mismatchTrue
        simp only [mismatchFalse, Bool.false_eq_true, if_false]
        unfold firstPositionalOnlyTypeMismatchReference
        rw [← comparableNat]
        have scanFalse : scan.2 = false := by
          rw [← scanEq']
          exact mismatchFalse
        change none = if scan.2 = true then _ else none
        simp [scanFalse]

def canonicalPositionalReference
    (source residuals : List (BindCallFull.PositionalActual String Int))
    (index : Nat) : List (BindCallFull.PositionalActual String Int) :=
  residuals ++ source.drop index

def canonicalPositionalInvariant
    (source : alloc.vec.Vec (BindCallFull.PositionalActual String Int))
    (expected : List (BindCallFull.PositionalActual String Int))
    (state : alloc.vec.Vec (BindCallFull.PositionalActual String Int) ×
      Std.Usize) : Prop :=
  state.1.val.length + (source.val.length - state.2.val) ≤
      Std.Usize.max ∧
    canonicalPositionalReference source.val state.1.val state.2.val = expected

def canonicalPositionalRemaining
    (source : alloc.vec.Vec (BindCallFull.PositionalActual String Int))
    (index : Std.Usize) : Nat :=
  source.val.length - index.val

theorem positional_actual_total_clone_exact
    (actual : BindCallFull.PositionalActual String Int) :
    BindCallFull.PositionalActual.Insts.CoreCloneClone.clone
      (totalIdentityClone String) (totalIdentityClone Int) actual = .ok actual := by
  rcases actual with ⟨value, origin, evaluationPosition⟩
  rcases value with ⟨typeTag, payload⟩
  cases origin <;> cases evaluationPosition <;>
    simp [BindCallFull.PositionalActual.Insts.CoreCloneClone.clone,
      BindCallFull.TypedValue.Insts.CoreCloneClone.clone,
      BindCallFull.PositionalOrigin.Insts.CoreCloneClone.clone,
      BindCallFull.EvaluationPosition.Insts.CoreCloneClone.clone,
      totalIdentityClone_exact]

theorem canonical_environment_loop4_body_preserves_reference_and_decreases
    (source : alloc.vec.Vec (BindCallFull.PositionalActual String Int))
    (expected : List (BindCallFull.PositionalActual String Int))
    (state : alloc.vec.Vec (BindCallFull.PositionalActual String Int) ×
      Std.Usize)
    (invariant : canonicalPositionalInvariant source expected state) :
    WP.spec
      (BindCallFull.canonical_environment_loop4.body
        (totalIdentityClone String) (totalIdentityClone Int)
        source state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output.val = expected
        | .cont next =>
            canonicalPositionalInvariant source expected next ∧
              canonicalPositionalRemaining source next.2 <
                canonicalPositionalRemaining source state.2) := by
  rcases state with ⟨residuals, index⟩
  unfold BindCallFull.canonical_environment_loop4.body
  unfold canonicalPositionalInvariant canonicalPositionalReference at invariant
  unfold canonicalPositionalInvariant canonicalPositionalReference
    canonicalPositionalRemaining
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  by_cases indexWithin : index < alloc.vec.Vec.len source
  · simp only [indexWithin, if_true]
    have sourceBound : index.val < source.val.length := by
      simpa using indexWithin
    step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
      exact sourceBound
    rw [positional_actual_total_clone_exact]
    step with alloc.vec.Vec.push_spec as ⟨nextResiduals, pushEq⟩ by
      have residualBound := invariant.1
      omega
    have nextIndexBound : index.val + 1 ≤ Std.Usize.max := by
      have sourceMachineBound := source.property
      omega
    step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
      exact nextIndexBound
    have dropStep : source.val.drop index.val =
        source.val[index.val] :: source.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons sourceBound
    simp only [actualEq, pushEq, nextIndexEq]
    rw [dropStep] at invariant
    rw [List.append_cons] at invariant
    have remainingStep : source.val.length - index.val =
        (source.val.length - (index.val + 1)) + 1 := by
      omega
    simp only [List.length_append, List.length_singleton]
    exact ⟨by omega, invariant.2, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : source.val.length ≤ index.val := by
      simpa using indexWithin
    simpa [List.drop_eq_nil_iff.mpr exhausted] using invariant.2

theorem canonical_environment_loop4_matches_reference
    (source residuals : alloc.vec.Vec
      (BindCallFull.PositionalActual String Int))
    (index : Std.Usize)
    (capacityBound : residuals.val.length +
      (source.val.length - index.val) ≤
        Std.Usize.max) :
    WP.spec
      (BindCallFull.canonical_environment_loop4
        (totalIdentityClone String) (totalIdentityClone Int)
        source residuals index)
      (fun output => output.val =
        canonicalPositionalReference source.val residuals.val index.val) := by
  let expected := canonicalPositionalReference source.val residuals.val index.val
  have initialInvariant : canonicalPositionalInvariant source expected
      (residuals, index) := ⟨capacityBound, rfl⟩
  unfold BindCallFull.canonical_environment_loop4
  apply loop.spec_decr_nat
      (measure := fun state => canonicalPositionalRemaining source state.2)
      (inv := canonicalPositionalInvariant source expected)
      (post := fun (output : alloc.vec.Vec
        (BindCallFull.PositionalActual String Int)) => output.val = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (canonical_environment_loop4_body_preserves_reference_and_decreases
      source expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

def canonicalKeywordSignature {value : Type}
    (positionalOnly positional keywordOnly : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (keywordArgs : BindCallFull.FormalParameter String value) :
    BindCallFull.CallSignature String value := {
  positional_only := positionalOnly
  positional := positional
  keyword_only := keywordOnly
  var_args := none
  keyword_args := some keywordArgs
}

theorem canonicalKeywordSignature_eq
    (signature : BindCallFull.CallSignature String Int)
    (keywordArgs : BindCallFull.FormalParameter String Int)
    (varArgsEq : signature.var_args = none)
    (keywordArgsEq : signature.keyword_args = some keywordArgs) :
    canonicalKeywordSignature signature.positional_only signature.positional
      signature.keyword_only keywordArgs = signature := by
  rcases signature with ⟨positionalOnly, positional, keywordOnly, varArgs,
    keywords⟩
  simp_all [canonicalKeywordSignature]

def canonicalNamedResidualReference {value : Type}
    (signature : BindCallFull.CallSignature String value) :
    List (BindCallFull.NamedActual String value) →
      List (BindCallFull.NamedActual String value)
  | [] => []
  | actual :: tail =>
      if ordinaryNameReference signature actual.name then
        canonicalNamedResidualReference signature tail
      else
        actual :: canonicalNamedResidualReference signature tail

def canonicalNamedReference {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (source residuals : List (BindCallFull.NamedActual String value))
    (index : Nat) : List (BindCallFull.NamedActual String value) :=
  residuals ++ canonicalNamedResidualReference signature (source.drop index)

def canonicalNamedInvariant {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (source : alloc.vec.Vec (BindCallFull.NamedActual String value))
    (expected : List (BindCallFull.NamedActual String value))
    (state : alloc.vec.Vec (BindCallFull.NamedActual String value) ×
      Std.Usize) : Prop :=
  state.2.val ≤ source.val.length ∧
    state.1.val.length + (source.val.length - state.2.val) ≤
      Std.Usize.max ∧
    canonicalNamedReference signature source.val state.1.val state.2.val = expected

def canonicalNamedRemaining {value : Type}
    (source : alloc.vec.Vec (BindCallFull.NamedActual String value))
    (index : Std.Usize) : Nat :=
  source.val.length - index.val

theorem named_actual_total_clone_exact
    (actual : BindCallFull.NamedActual String Int) :
    BindCallFull.NamedActual.Insts.CoreCloneClone.clone
      (totalIdentityClone String) (totalIdentityClone Int) actual = .ok actual := by
  rcases actual with ⟨actualName, value, evaluationPosition⟩
  rcases value with ⟨typeTag, payload⟩
  cases evaluationPosition <;>
    simp [BindCallFull.NamedActual.Insts.CoreCloneClone.clone,
      BindCallFull.TypedValue.Insts.CoreCloneClone.clone,
      BindCallFull.EvaluationPosition.Insts.CoreCloneClone.clone,
      string_clone_exact, totalIdentityClone_exact]

theorem canonical_environment_loop3_body_preserves_reference_and_decreases
    (positionalOnly positional keywordOnly : alloc.vec.Vec
      (BindCallFull.FormalParameter String Int))
    (keywordArgs : BindCallFull.FormalParameter String Int)
    (source : alloc.vec.Vec (BindCallFull.NamedActual String Int))
    (expected : List (BindCallFull.NamedActual String Int))
    (state : alloc.vec.Vec (BindCallFull.NamedActual String Int) × Std.Usize)
    (invariant : canonicalNamedInvariant
      (canonicalKeywordSignature positionalOnly positional keywordOnly keywordArgs)
      source expected state) :
    WP.spec
      (BindCallFull.canonical_environment_loop3.body
        (totalIdentityClone String) (totalIdentityClone Int)
        positionalOnly positional keywordOnly keywordArgs source state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output.val = expected
        | .cont next =>
            canonicalNamedInvariant
                (canonicalKeywordSignature positionalOnly positional keywordOnly keywordArgs)
                source expected next ∧
              canonicalNamedRemaining source next.2 <
                canonicalNamedRemaining source state.2) := by
  rcases state with ⟨residuals, index⟩
  let signature := canonicalKeywordSignature positionalOnly positional keywordOnly keywordArgs
  unfold BindCallFull.canonical_environment_loop3.body
  unfold canonicalNamedInvariant canonicalNamedReference at invariant
  unfold canonicalNamedInvariant canonicalNamedReference canonicalNamedRemaining
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  by_cases indexWithin : index < alloc.vec.Vec.len source
  · simp only [indexWithin, if_true]
    have sourceBound : index.val < source.val.length := by simpa using indexWithin
    step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
      exact sourceBound
    rw [string_clone_exact]
    step with ordinary_parameter_name_matches_reference as ⟨ordinary, ordinaryEq⟩
    have ordinaryReference : ordinary =
        ordinaryNameReference signature source.val[index.val].name := by
      simpa [signature, canonicalKeywordSignature, ordinaryNameReference,
        actualEq] using ordinaryEq
    have dropStep : source.val.drop index.val =
        source.val[index.val] :: source.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons sourceBound
    have nextIndexBound : index.val + 1 ≤ Std.Usize.max := by
      have sourceMachineBound := source.property
      omega
    by_cases isOrdinary :
        ordinaryNameReference signature source.val[index.val].name = true
    · have ordinaryTrueExpanded :
          ordinaryNameReference
              (canonicalKeywordSignature positionalOnly positional keywordOnly keywordArgs)
              source.val[index.val].name = true := by
        simpa [signature] using isOrdinary
      simp only [ordinaryReference, actualEq, isOrdinary, if_true]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        exact nextIndexBound
      rw [dropStep] at invariant
      simp only [canonicalNamedResidualReference, ordinaryTrueExpanded, if_true] at invariant
      simp only [nextIndexEq]
      have remainingStep : source.val.length - index.val =
          (source.val.length - (index.val + 1)) + 1 := by omega
      exact ⟨by omega, by omega, invariant.2.2, by omega⟩
    · have ordinaryFalse : ordinaryNameReference signature source.val[index.val].name = false :=
        Bool.eq_false_of_not_eq_true isOrdinary
      have ordinaryFalseExpanded :
          ordinaryNameReference
              (canonicalKeywordSignature positionalOnly positional keywordOnly keywordArgs)
              source.val[index.val].name = false := by
        simpa [signature] using ordinaryFalse
      simp only [ordinaryReference, actualEq, ordinaryFalse,
        Bool.false_eq_true, if_false]
      rw [named_actual_total_clone_exact]
      step with alloc.vec.Vec.push_spec as ⟨nextResiduals, pushEq⟩ by
        have residualBound := invariant.2.1
        omega
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        exact nextIndexBound
      rw [dropStep] at invariant
      rw [canonicalNamedResidualReference.eq_2] at invariant
      rw [ordinaryFalseExpanded] at invariant
      simp only [Bool.false_eq_true, if_false] at invariant
      rw [List.append_cons] at invariant
      simp only [pushEq, nextIndexEq, List.length_append, List.length_singleton]
      have remainingStep : source.val.length - index.val =
          (source.val.length - (index.val + 1)) + 1 := by omega
      exact ⟨by omega, by omega, invariant.2.2, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : source.val.length ≤ index.val := by simpa using indexWithin
    have referenceEq := invariant.2.2
    simp [List.drop_eq_nil_iff.mpr exhausted, canonicalNamedResidualReference] at referenceEq
    exact referenceEq

theorem canonical_environment_loop3_matches_reference
    (positionalOnly positional keywordOnly : alloc.vec.Vec
      (BindCallFull.FormalParameter String Int))
    (keywordArgs : BindCallFull.FormalParameter String Int)
    (source residuals : alloc.vec.Vec (BindCallFull.NamedActual String Int))
    (index : Std.Usize) (indexBound : index.val ≤ source.val.length)
    (capacityBound : residuals.val.length +
      (source.val.length - index.val) ≤ Std.Usize.max) :
    WP.spec
      (BindCallFull.canonical_environment_loop3
        (totalIdentityClone String) (totalIdentityClone Int)
        positionalOnly positional keywordOnly keywordArgs source residuals index)
      (fun output => output.val = canonicalNamedReference
        (canonicalKeywordSignature positionalOnly positional keywordOnly keywordArgs)
        source.val residuals.val index.val) := by
  let signature := canonicalKeywordSignature positionalOnly positional keywordOnly keywordArgs
  let expected := canonicalNamedReference signature source.val residuals.val index.val
  have initialInvariant : canonicalNamedInvariant signature source expected
      (residuals, index) := ⟨indexBound, capacityBound, rfl⟩
  unfold BindCallFull.canonical_environment_loop3
  apply loop.spec_decr_nat
      (measure := fun state => canonicalNamedRemaining source state.2)
      (inv := canonicalNamedInvariant signature source expected)
      (post := fun (output : alloc.vec.Vec
        (BindCallFull.NamedActual String Int)) => output.val = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (canonical_environment_loop3_body_preserves_reference_and_decreases
      positionalOnly positional keywordOnly keywordArgs source expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa [signature] using flowPost

def canonicalVariadicSignature {value : Type}
    (positionalOnly positional keywordOnly : alloc.vec.Vec
      (BindCallFull.FormalParameter String value))
    (varArgs keywordArgs : BindCallFull.FormalParameter String value) :
    BindCallFull.CallSignature String value := {
  positional_only := positionalOnly
  positional := positional
  keyword_only := keywordOnly
  var_args := some varArgs
  keyword_args := some keywordArgs
}

theorem canonicalVariadicSignature_eq
    (signature : BindCallFull.CallSignature String Int)
    (varArgs keywordArgs : BindCallFull.FormalParameter String Int)
    (varArgsEq : signature.var_args = some varArgs)
    (keywordArgsEq : signature.keyword_args = some keywordArgs) :
    canonicalVariadicSignature signature.positional_only signature.positional
      signature.keyword_only varArgs keywordArgs = signature := by
  rcases signature with ⟨positionalOnly, positional, keywordOnly, variadic,
    keywords⟩
  simp_all [canonicalVariadicSignature]

theorem canonical_environment_loop5_body_preserves_reference_and_decreases
    (positionalOnly positional keywordOnly : alloc.vec.Vec
      (BindCallFull.FormalParameter String Int))
    (varArgs keywordArgs : BindCallFull.FormalParameter String Int)
    (source : alloc.vec.Vec (BindCallFull.NamedActual String Int))
    (expected : List (BindCallFull.NamedActual String Int))
    (state : alloc.vec.Vec (BindCallFull.NamedActual String Int) × Std.Usize)
    (invariant : canonicalNamedInvariant
      (canonicalVariadicSignature positionalOnly positional keywordOnly varArgs keywordArgs)
      source expected state) :
    WP.spec
      (BindCallFull.canonical_environment_loop5.body
        (totalIdentityClone String) (totalIdentityClone Int)
        positionalOnly positional keywordOnly varArgs keywordArgs
        source state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output.val = expected
        | .cont next =>
            canonicalNamedInvariant
                (canonicalVariadicSignature positionalOnly positional keywordOnly varArgs keywordArgs)
                source expected next ∧
              canonicalNamedRemaining source next.2 <
                canonicalNamedRemaining source state.2) := by
  rcases state with ⟨residuals, index⟩
  let signature := canonicalVariadicSignature
    positionalOnly positional keywordOnly varArgs keywordArgs
  unfold BindCallFull.canonical_environment_loop5.body
  unfold canonicalNamedInvariant canonicalNamedReference at invariant
  unfold canonicalNamedInvariant canonicalNamedReference canonicalNamedRemaining
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  by_cases indexWithin : index < alloc.vec.Vec.len source
  · simp only [indexWithin, if_true]
    have sourceBound : index.val < source.val.length := by simpa using indexWithin
    step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
      exact sourceBound
    rw [string_clone_exact]
    step with ordinary_parameter_name_matches_reference as ⟨ordinary, ordinaryEq⟩
    have ordinaryReference : ordinary =
        ordinaryNameReference signature source.val[index.val].name := by
      simpa [signature, canonicalVariadicSignature, ordinaryNameReference,
        actualEq] using ordinaryEq
    have dropStep : source.val.drop index.val =
        source.val[index.val] :: source.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons sourceBound
    have nextIndexBound : index.val + 1 ≤ Std.Usize.max := by
      have sourceMachineBound := source.property
      omega
    by_cases isOrdinary :
        ordinaryNameReference signature source.val[index.val].name = true
    · have ordinaryTrueExpanded :
          ordinaryNameReference
              (canonicalVariadicSignature positionalOnly positional keywordOnly
                varArgs keywordArgs)
              source.val[index.val].name = true := by
        simpa [signature] using isOrdinary
      simp only [ordinaryReference, actualEq, isOrdinary, if_true]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        exact nextIndexBound
      rw [dropStep] at invariant
      simp only [canonicalNamedResidualReference, ordinaryTrueExpanded, if_true] at invariant
      simp only [nextIndexEq]
      have remainingStep : source.val.length - index.val =
          (source.val.length - (index.val + 1)) + 1 := by omega
      exact ⟨by omega, by omega, invariant.2.2, by omega⟩
    · have ordinaryFalse : ordinaryNameReference signature source.val[index.val].name = false :=
        Bool.eq_false_of_not_eq_true isOrdinary
      have ordinaryFalseExpanded :
          ordinaryNameReference
              (canonicalVariadicSignature positionalOnly positional keywordOnly
                varArgs keywordArgs)
              source.val[index.val].name = false := by
        simpa [signature] using ordinaryFalse
      simp only [ordinaryReference, actualEq, ordinaryFalse,
        Bool.false_eq_true, if_false]
      rw [named_actual_total_clone_exact]
      step with alloc.vec.Vec.push_spec as ⟨nextResiduals, pushEq⟩ by
        have residualBound := invariant.2.1
        omega
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        exact nextIndexBound
      rw [dropStep] at invariant
      rw [canonicalNamedResidualReference.eq_2] at invariant
      rw [ordinaryFalseExpanded] at invariant
      simp only [Bool.false_eq_true, if_false] at invariant
      rw [List.append_cons] at invariant
      simp only [pushEq, nextIndexEq, List.length_append, List.length_singleton]
      have remainingStep : source.val.length - index.val =
          (source.val.length - (index.val + 1)) + 1 := by omega
      exact ⟨by omega, by omega, invariant.2.2, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : source.val.length ≤ index.val := by simpa using indexWithin
    have referenceEq := invariant.2.2
    simp [List.drop_eq_nil_iff.mpr exhausted, canonicalNamedResidualReference] at referenceEq
    exact referenceEq

theorem canonical_environment_loop5_matches_reference
    (positionalOnly positional keywordOnly : alloc.vec.Vec
      (BindCallFull.FormalParameter String Int))
    (varArgs keywordArgs : BindCallFull.FormalParameter String Int)
    (source residuals : alloc.vec.Vec (BindCallFull.NamedActual String Int))
    (index : Std.Usize) (indexBound : index.val ≤ source.val.length)
    (capacityBound : residuals.val.length +
      (source.val.length - index.val) ≤ Std.Usize.max) :
    WP.spec
      (BindCallFull.canonical_environment_loop5
        (totalIdentityClone String) (totalIdentityClone Int)
        positionalOnly positional keywordOnly varArgs keywordArgs
        source residuals index)
      (fun output => output.val = canonicalNamedReference
        (canonicalVariadicSignature positionalOnly positional keywordOnly varArgs keywordArgs)
        source.val residuals.val index.val) := by
  let signature := canonicalVariadicSignature
    positionalOnly positional keywordOnly varArgs keywordArgs
  let expected := canonicalNamedReference signature source.val residuals.val index.val
  have initialInvariant : canonicalNamedInvariant signature source expected
      (residuals, index) := ⟨indexBound, capacityBound, rfl⟩
  unfold BindCallFull.canonical_environment_loop5
  apply loop.spec_decr_nat
      (measure := fun state => canonicalNamedRemaining source state.2)
      (inv := canonicalNamedInvariant signature source expected)
      (post := fun (output : alloc.vec.Vec
        (BindCallFull.NamedActual String Int)) => output.val = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (canonical_environment_loop5_body_preserves_reference_and_decreases
      positionalOnly positional keywordOnly varArgs keywordArgs
      source expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa [signature] using flowPost

def keywordMismatchScanReference {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (actuals : alloc.vec.Vec (BindCallFull.NamedActual String value))
    (keywordIndex : Nat) (mismatch : Bool) (actualIndex : Nat) :
    Nat × Bool × Nat :=
  if mismatch then
    (keywordIndex, true, actualIndex)
  else
    match remaining with
    | [] => (keywordIndex, false, actualIndex)
    | parameter :: tail =>
        let candidate := namedActualIndexReference actuals.deref parameter.name
        match actuals.val[candidate]? with
        | none => keywordMismatchScanReference tail actuals
            (keywordIndex + 1) false actualIndex
        | some actual =>
            if parameter.expected_type == actual.value.type_tag then
              keywordMismatchScanReference tail actuals
                (keywordIndex + 1) false candidate
            else
              (keywordIndex + 1, true, candidate)
termination_by remaining.length

@[simp]
theorem keywordMismatchScanReference_found_true {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (actuals : alloc.vec.Vec (BindCallFull.NamedActual String value))
    (keywordIndex actualIndex : Nat) :
    keywordMismatchScanReference remaining actuals keywordIndex true actualIndex =
      (keywordIndex, true, actualIndex) := by
  rw [keywordMismatchScanReference.eq_def]
  simp

@[simp]
theorem keywordMismatchScanReference_empty {value : Type}
    (actuals : alloc.vec.Vec (BindCallFull.NamedActual String value))
    (keywordIndex actualIndex : Nat) (mismatch : Bool) :
    keywordMismatchScanReference [] actuals keywordIndex mismatch actualIndex =
      (keywordIndex, mismatch, actualIndex) := by
  cases mismatch <;>
    simp [keywordMismatchScanReference.eq_1, keywordMismatchScanReference.eq_2]

def keywordMismatchView
    (output : Std.Usize × Bool × Std.Usize) : Nat × Bool × Nat :=
  (output.1.val, output.2.1, output.2.2.val)

def keywordMismatchInvariant {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (actuals : alloc.vec.Vec (BindCallFull.NamedActual String value))
    (expected : Nat × Bool × Nat)
    (state : Std.Usize × Bool × Std.Usize) : Prop :=
  state.1.val ≤ signature.keyword_only.val.length ∧
    keywordMismatchScanReference
      (signature.keyword_only.val.drop state.1.val) actuals state.1.val
      state.2.1 state.2.2.val = expected

def keywordMismatchRemaining {value : Type}
    (signature : BindCallFull.CallSignature String value)
    (index : Std.Usize) : Nat :=
  signature.keyword_only.val.length - index.val

theorem first_keyword_only_type_mismatch_loop_body_preserves_reference_and_decreases
    (signature : BindCallFull.CallSignature String Int)
    (actuals : alloc.vec.Vec (BindCallFull.NamedActual String Int))
    (expected : Nat × Bool × Nat)
    (state : Std.Usize × Bool × Std.Usize)
    (invariant : keywordMismatchInvariant signature actuals expected state) :
    WP.spec
      (BindCallFull.first_keyword_only_type_mismatch_loop.body
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature actuals () state.1 state.2.1 state.2.2)
      (fun flow =>
        match flow with
        | .done output =>
            output.1 = signature.keyword_only ∧
              keywordMismatchView (output.2.1, output.2.2.1, output.2.2.2) = expected
        | .cont next =>
            keywordMismatchInvariant signature actuals expected next ∧
              keywordMismatchRemaining signature next.1 <
                keywordMismatchRemaining signature state.1) := by
  rcases state with ⟨keywordIndex, mismatch, actualIndex⟩
  unfold BindCallFull.first_keyword_only_type_mismatch_loop.body
  unfold keywordMismatchInvariant at invariant
  unfold keywordMismatchInvariant keywordMismatchRemaining keywordMismatchView
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  by_cases indexWithin : keywordIndex < alloc.vec.Vec.len signature.keyword_only
  · simp only [indexWithin, if_true]
    by_cases alreadyMismatch : mismatch = true
    · have expectedEq : (keywordIndex.val, true, actualIndex.val) = expected := by
        simpa [alreadyMismatch] using invariant.2
      simpa [alreadyMismatch] using expectedEq
    · have mismatchFalse := Bool.eq_false_of_not_eq_true alreadyMismatch
      simp only [mismatchFalse, Bool.false_eq_true, if_false]
      have parameterBound : keywordIndex.val < signature.keyword_only.val.length := by
        simpa using indexWithin
      step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
        exact parameterBound
      rw [string_clone_exact, totalIdentityClone_exact]
      step with named_actual_index_matches_reference as ⟨candidateIndex, candidateEq⟩
      by_cases candidateWithin : candidateIndex < alloc.vec.Vec.len actuals
      · simp only [candidateWithin, if_true]
        have candidateBound : candidateIndex.val < actuals.val.length := by
          simpa using candidateWithin
        step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
          exact candidateBound
        rw [compatibility_mismatch_string_exact]
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have parameterMachineBound := signature.keyword_only.property
          omega
        have parameterDrop : signature.keyword_only.val.drop keywordIndex.val =
            signature.keyword_only.val[keywordIndex.val] ::
              signature.keyword_only.val.drop (keywordIndex.val + 1) :=
          List.drop_eq_getElem_cons parameterBound
        have referenceStep := invariant.2
        rw [parameterDrop] at referenceStep
        rw [keywordMismatchScanReference.eq_2] at referenceStep
        simp only [mismatchFalse, Bool.false_eq_true, if_false] at referenceStep
        have candidateNatEq :
            namedActualIndexReference actuals.deref
              signature.keyword_only.val[keywordIndex.val].name = candidateIndex.val :=
          by simpa [parameterEq] using candidateEq.symm
        have candidateGet : actuals.val[
            namedActualIndexReference actuals.deref
              signature.keyword_only.val[keywordIndex.val].name]? =
              some actual := by
          rw [candidateNatEq]
          simpa [List.getElem?_eq_getElem candidateBound] using actualEq.symm
        simp only [candidateGet] at referenceStep
        by_cases typesEqual :
            signature.keyword_only.val[keywordIndex.val].expected_type =
              actuals.val[candidateIndex.val].value.type_tag
        · have equalityTrue :
              (signature.keyword_only.val[keywordIndex.val].expected_type ==
                actuals.val[candidateIndex.val].value.type_tag) = true := by
            simpa using typesEqual
          have referenceEq : keywordMismatchScanReference
              (signature.keyword_only.val.drop (keywordIndex.val + 1)) actuals
              (keywordIndex.val + 1) false candidateIndex.val = expected := by
            simpa [parameterEq, actualEq, typesEqual, candidateNatEq] using referenceStep
          simp only [parameterEq, actualEq, equalityTrue, if_true, nextIndexEq]
          exact ⟨by omega, referenceEq, by omega⟩
        · have equalityFalse :
              (signature.keyword_only.val[keywordIndex.val].expected_type ==
                actuals.val[candidateIndex.val].value.type_tag) = false := by
            simpa using typesEqual
          have referenceEq :
              (keywordIndex.val + 1, true, candidateIndex.val) = expected := by
            simpa [parameterEq, actualEq, typesEqual, candidateNatEq] using referenceStep
          simp only [parameterEq, actualEq, equalityFalse, if_false,
            Bool.false_eq_true, nextIndexEq,
            keywordMismatchScanReference_found_true]
          exact ⟨by omega, referenceEq, by omega⟩
      · simp only [candidateWithin, if_false]
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have parameterMachineBound := signature.keyword_only.property
          omega
        have parameterDrop : signature.keyword_only.val.drop keywordIndex.val =
            signature.keyword_only.val[keywordIndex.val] ::
              signature.keyword_only.val.drop (keywordIndex.val + 1) :=
          List.drop_eq_getElem_cons parameterBound
        have candidateExhausted : actuals.val.length ≤ candidateIndex.val := by
          simpa using candidateWithin
        have referenceStep := invariant.2
        rw [parameterDrop] at referenceStep
        rw [keywordMismatchScanReference.eq_2] at referenceStep
        simp only [mismatchFalse, Bool.false_eq_true, if_false] at referenceStep
        have candidateNatEq :
            namedActualIndexReference actuals.deref
              signature.keyword_only.val[keywordIndex.val].name = candidateIndex.val :=
          by simpa [parameterEq] using candidateEq.symm
        have candidateNone : actuals.val[
            namedActualIndexReference actuals.deref
              signature.keyword_only.val[keywordIndex.val].name]? = none := by
          rw [candidateNatEq]
          exact List.getElem?_eq_none candidateExhausted
        simp only [candidateNone] at referenceStep
        simp only [parameterEq, nextIndexEq]
        exact ⟨by omega, referenceStep, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : signature.keyword_only.val.length ≤ keywordIndex.val := by
      simpa using indexWithin
    have atEnd : keywordIndex.val = signature.keyword_only.val.length := by omega
    have expectedEq := invariant.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    exact ⟨rfl, by simpa [atEnd] using expectedEq⟩

theorem first_keyword_only_type_mismatch_loop_matches_reference
    (signature : BindCallFull.CallSignature String Int)
    (actuals : alloc.vec.Vec (BindCallFull.NamedActual String Int))
    (keywordIndex : Std.Usize) (mismatch : Bool) (actualIndex : Std.Usize)
    (indexBound : keywordIndex.val ≤ signature.keyword_only.val.length) :
    WP.spec
      (BindCallFull.first_keyword_only_type_mismatch_loop
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature actuals () keywordIndex mismatch actualIndex)
      (fun output =>
        output.1 = signature.keyword_only ∧
          keywordMismatchView (output.2.1, output.2.2.1, output.2.2.2) =
            keywordMismatchScanReference
              (signature.keyword_only.val.drop keywordIndex.val) actuals
              keywordIndex.val mismatch actualIndex.val) := by
  let expected := keywordMismatchScanReference
    (signature.keyword_only.val.drop keywordIndex.val) actuals
    keywordIndex.val mismatch actualIndex.val
  have initialInvariant : keywordMismatchInvariant signature actuals expected
      (keywordIndex, mismatch, actualIndex) := ⟨indexBound, rfl⟩
  unfold BindCallFull.first_keyword_only_type_mismatch_loop
  apply loop.spec_decr_nat
      (measure := fun state => keywordMismatchRemaining signature state.1)
      (inv := keywordMismatchInvariant signature actuals expected)
      (post := fun (output : alloc.vec.Vec
          (BindCallFull.FormalParameter String Int) × Std.Usize × Bool × Std.Usize) =>
        output.1 = signature.keyword_only ∧
        keywordMismatchView (output.2.1, output.2.2.1, output.2.2.2) = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_keyword_only_type_mismatch_loop_body_preserves_reference_and_decreases
      signature actuals expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem keywordMismatchScanReference_true_bounds {value : Type}
    (remaining : List (BindCallFull.FormalParameter String value))
    (actuals : alloc.vec.Vec (BindCallFull.NamedActual String value))
    (keywordIndex actualIndex : Nat)
    (foundTrue :
      (keywordMismatchScanReference remaining actuals keywordIndex false
        actualIndex).2.1 = true) :
    keywordIndex <
        (keywordMismatchScanReference remaining actuals keywordIndex false
          actualIndex).1 ∧
      (keywordMismatchScanReference remaining actuals keywordIndex false
          actualIndex).1 ≤ keywordIndex + remaining.length ∧
      (keywordMismatchScanReference remaining actuals keywordIndex false
          actualIndex).2.2 < actuals.val.length := by
  induction remaining generalizing keywordIndex actualIndex with
  | nil => simp at foundTrue
  | cons parameter tail inductionHypothesis =>
      rw [keywordMismatchScanReference.eq_def] at foundTrue ⊢
      simp only [Bool.false_eq_true, if_false] at foundTrue ⊢
      let candidate := namedActualIndexReference actuals.deref parameter.name
      cases candidateEq : actuals.val[candidate]? with
      | none =>
          have recursive := inductionHypothesis (keywordIndex + 1)
            actualIndex (by simpa [candidate, candidateEq] using foundTrue)
          dsimp [candidate] at recursive ⊢
          simpa [candidate, candidateEq, Nat.add_assoc] using
            ⟨by omega, by omega, recursive.2.2⟩
      | some actual =>
          have candidateBound := (List.getElem?_eq_some_iff.mp candidateEq).1
          by_cases typesEqual : parameter.expected_type = actual.value.type_tag
          · have recursive := inductionHypothesis (keywordIndex + 1)
              candidate (by simpa [candidate, candidateEq, typesEqual] using
                foundTrue)
            dsimp [candidate] at recursive ⊢
            simpa [candidate, candidateEq, typesEqual, Nat.add_assoc] using
              ⟨by omega, by omega, recursive.2.2⟩
          · simp [candidate, candidateEq, typesEqual]
            exact candidateBound

def firstKeywordOnlyTypeMismatchReference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int) :
    Option (BindCallFull.BindingError String) :=
  let scan := keywordMismatchScanReference signature.keyword_only.val
    call.named 0 false call.named.val.length
  if scan.2.1 then
    match signature.keyword_only.val[scan.1 - 1]?, call.named.val[scan.2.2]? with
    | some parameter, some actual =>
        some (BindCallFull.BindingError.TypeMismatch parameter.name
          parameter.expected_type actual.value.type_tag
          (some actual.evaluation_position))
    | _, _ => none
  else
    none

theorem first_keyword_only_type_mismatch_matches_reference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int) :
    WP.spec
      (BindCallFull.first_keyword_only_type_mismatch
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature call ())
      (fun output => output =
        firstKeywordOnlyTypeMismatchReference signature call) := by
  unfold BindCallFull.first_keyword_only_type_mismatch
  apply WP.spec_bind
  · exact first_keyword_only_type_mismatch_loop_matches_reference
      signature call.named 0#usize false (alloc.vec.Vec.len call.named) (by simp)
  · rintro ⟨parameters, keywordIndex, mismatch, actualIndex⟩ loopPost
    have parametersEq : parameters = signature.keyword_only := loopPost.1
    have scanEq : (keywordIndex.val, mismatch, actualIndex.val) =
        keywordMismatchScanReference signature.keyword_only.val call.named
          0 false call.named.val.length := by
      simpa [keywordMismatchView, alloc.vec.Vec.len, parametersEq] using loopPost.2
    let scan := keywordMismatchScanReference signature.keyword_only.val
      call.named 0 false call.named.val.length
    have scanEq' : (keywordIndex.val, mismatch, actualIndex.val) = scan := scanEq
    by_cases mismatchTrue : mismatch = true
    · simp [mismatchTrue]
      have scanTrue : scan.2.1 = true := by
        rw [← scanEq']
        exact mismatchTrue
      have scanBounds := keywordMismatchScanReference_true_bounds
        signature.keyword_only.val call.named 0 call.named.val.length scanTrue
      change 0 < scan.1 ∧ scan.1 ≤ 0 + signature.keyword_only.val.length ∧
        scan.2.2 < call.named.val.length at scanBounds
      have keywordIndexEq : keywordIndex.val = scan.1 :=
        congrArg Prod.fst scanEq'
      have actualIndexEq : actualIndex.val = scan.2.2 :=
        congrArg (fun output => output.2.2) scanEq'
      have keywordPositive : 0 < keywordIndex.val := by
        rw [keywordIndexEq]
        exact scanBounds.1
      step with Std.Usize.sub_spec as ⟨mismatchIndex, mismatchIndexEq⟩ by
        simpa using keywordPositive
      have mismatchIndexNat : mismatchIndex.val = scan.1 - 1 := by
        rw [mismatchIndexEq, keywordIndexEq]
      have parameterBound : mismatchIndex.val <
          signature.keyword_only.val.length := by
        have scanUpper : scan.1 ≤ signature.keyword_only.val.length := by
          simpa using scanBounds.2.1
        omega
      step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
        simpa [parametersEq] using parameterBound
      have namedBound : actualIndex.val < call.named.val.length := by
        rw [actualIndexEq]
        exact scanBounds.2.2
      step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
        exact namedBound
      rw [string_clone_exact, totalIdentityClone_exact,
        totalIdentityClone_exact]
      unfold firstKeywordOnlyTypeMismatchReference
      change some (BindCallFull.BindingError.TypeMismatch parameter.name
          parameter.expected_type actual.value.type_tag
          (some actual.evaluation_position)) =
        if scan.2.1 = true then
          match signature.keyword_only.val[scan.1 - 1]?,
              call.named.val[scan.2.2]? with
          | some parameter, some actual =>
              some (BindCallFull.BindingError.TypeMismatch parameter.name
                parameter.expected_type actual.value.type_tag
                (some actual.evaluation_position))
          | _, _ => none
        else none
      rw [scanTrue]
      simp only [if_true]
      rw [List.getElem?_eq_getElem (by omega : scan.1 - 1 <
        signature.keyword_only.val.length)]
      rw [List.getElem?_eq_getElem scanBounds.2.2]
      simp [parameterEq, actualEq, mismatchIndexNat, actualIndexEq, parametersEq]
    · have mismatchFalse : mismatch = false :=
        Bool.eq_false_of_not_eq_true mismatchTrue
      simp [mismatchFalse]
      unfold firstKeywordOnlyTypeMismatchReference
      have scanFalse : scan.2.1 = false := by
        rw [← scanEq']
        exact mismatchFalse
      change none = if scan.2.1 = true then _ else none
      simp [scanFalse]


def preflightRemaining {α : Type}
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter α)) : Nat :=
  iter.iter.slice.val.length - iter.iter.i

@[step]
theorem preflight_enumerate_slice_next_decreases_or_finishes
    {α : Type}
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter α))
    (indexBound : iter.iter.i ≤ iter.iter.slice.val.length)
    (countBound : iter.count.val = iter.iter.i) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter α) iter ⦃ result =>
      match result.1 with
      | none => result.2 = iter ∧ preflightRemaining iter = 0
      | some (index, item) =>
          index.val = iter.iter.i ∧
          iter.iter.slice.val[iter.iter.i]? = some item ∧
          preflightRemaining result.2 < preflightRemaining iter ∧
          preflightRemaining result.2 + 1 = preflightRemaining iter ∧
          result.2.iter.slice = iter.iter.slice ∧
          result.2.iter.i = iter.iter.i + 1 ∧
          result.2.iter.i ≤ result.2.iter.slice.val.length ∧
          result.2.count.val = result.2.iter.i ⦄ := by
  simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorSliceIter.next, preflightRemaining]
  split
  case isTrue itemAvailable =>
    step
    constructor
    · exact countBound
    constructor
    · exact List.getElem?_eq_getElem itemAvailable
    · omega
  case isFalse exhausted => simp_all

def preflightIteratorInvariant {α : Type}
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter α)) : Prop :=
  iter.iter.i ≤ iter.iter.slice.val.length ∧ iter.count.val = iter.iter.i

inductive EvaluationPositionView where
  | receiver
  | actual (sourceIndex expansionIndex : Nat)
  deriving DecidableEq, Repr

structure PositionalActualView where
  value : BindCallFull.TypedValue String Int
  origin : BindCallFull.PositionalOrigin
  evaluationPosition : EvaluationPositionView

def evaluationPositionView :
    BindCallFull.EvaluationPosition → EvaluationPositionView
  | .Receiver => .receiver
  | .Actual sourceIndex expansionIndex =>
      .actual sourceIndex.val expansionIndex.val

def positionalActualView
    (actual : BindCallFull.PositionalActual String Int) : PositionalActualView := {
  value := actual.value
  origin := actual.origin
  evaluationPosition := evaluationPositionView actual.evaluation_position
}

theorem typed_value_total_clone_exact
    (value : BindCallFull.TypedValue String Int) :
    BindCallFull.TypedValue.Insts.CoreCloneClone.clone
      (totalIdentityClone String) (totalIdentityClone Int) value = .ok value := by
  rcases value with ⟨typeTag, payload⟩
  simp [BindCallFull.TypedValue.Insts.CoreCloneClone.clone,
    totalIdentityClone_exact]

@[step]
theorem typed_value_total_clone_spec
    (value : BindCallFull.TypedValue String Int) :
    WP.spec
      (BindCallFull.TypedValue.Insts.CoreCloneClone.clone
        (totalIdentityClone String) (totalIdentityClone Int) value)
      (fun output => output = value) := by
  rw [typed_value_total_clone_exact]
  simp [WP.spec, WP.theta, WP.wp_return]

def fixedStarViewsFrom (sourceIndex expansionIndex : Nat) :
    List (BindCallFull.TypedValue String Int) → List PositionalActualView
  | [] => []
  | value :: remaining =>
      {
        value := value
        origin := .FixedStar
        evaluationPosition := .actual sourceIndex expansionIndex
      } :: fixedStarViewsFrom sourceIndex (expansionIndex + 1) remaining

theorem fixedStarViewsFrom_append
    (sourceIndex expansionIndex : Nat)
    (left right : List (BindCallFull.TypedValue String Int)) :
    fixedStarViewsFrom sourceIndex expansionIndex (left ++ right) =
      fixedStarViewsFrom sourceIndex expansionIndex left ++
        fixedStarViewsFrom sourceIndex (expansionIndex + left.length) right := by
  induction left generalizing expansionIndex with
  | nil => simp [fixedStarViewsFrom]
  | cons value remaining inductionHypothesis =>
      simp [fixedStarViewsFrom, inductionHypothesis]
      rw [Nat.add_comm remaining.length 1]
      simp [Nat.add_assoc]

@[simp]
theorem fixedStarViewsFrom_length
    (sourceIndex expansionIndex : Nat)
    (values : List (BindCallFull.TypedValue String Int)) :
    (fixedStarViewsFrom sourceIndex expansionIndex values).length =
      values.length := by
  induction values generalizing expansionIndex with
  | nil => simp [fixedStarViewsFrom]
  | cons value remaining inductionHypothesis =>
      simp [fixedStarViewsFrom, inductionHypothesis]

def fixedStarRecordInvariant
    (itemIndex : Std.Usize)
    (initialViews : List PositionalActualView)
    (sourceValues : List (BindCallFull.TypedValue String Int))
    (state : core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter (BindCallFull.TypedValue String Int)) ×
      alloc.vec.Vec (BindCallFull.PositionalActual String Int)) : Prop :=
  preflightIteratorInvariant state.1 ∧
    state.1.iter.slice.val = sourceValues ∧
    state.2.val.length + preflightRemaining state.1 ≤
      BindCallFull.USIZE_CAPACITY.val ∧
    state.2.val.map positionalActualView =
      initialViews ++
        fixedStarViewsFrom itemIndex.val 0 (sourceValues.take state.1.iter.i)

theorem expand_actual_items_fixed_star_loop_body_preserves_records_and_decreases
    (itemIndex : Std.Usize)
    (initialViews : List PositionalActualView)
    (sourceValues : List (BindCallFull.TypedValue String Int))
    (state : core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter (BindCallFull.TypedValue String Int)) ×
      alloc.vec.Vec (BindCallFull.PositionalActual String Int))
    (invariant : fixedStarRecordInvariant itemIndex initialViews sourceValues state) :
    WP.spec
      (BindCallFull.expand_actual_items_with_allocator_loop0_loop0.body
        (totalIdentityClone String) (totalIdentityClone Int)
        itemIndex state.1 state.2)
      (fun flow =>
        match flow with
        | .done output =>
            output.val.map positionalActualView =
              initialViews ++ fixedStarViewsFrom itemIndex.val 0 sourceValues
        | .cont next =>
            fixedStarRecordInvariant itemIndex initialViews sourceValues next ∧
              preflightRemaining next.1 < preflightRemaining state.1) := by
  rcases state with ⟨iter, positional⟩
  unfold BindCallFull.expand_actual_items_with_allocator_loop0_loop0.body
  unfold fixedStarRecordInvariant preflightIteratorInvariant at invariant ⊢
  step with preflight_enumerate_slice_next_decreases_or_finishes
  cases o with
  | none =>
      rcases o_post with ⟨sameState, exhaustedRemaining⟩
      have exhausted : sourceValues.length ≤ iter.iter.i := by
        unfold preflightRemaining at exhaustedRemaining
        simp_all
        exact Nat.sub_eq_zero_iff_le.mp exhaustedRemaining
      simp_all [List.take_of_length_le exhausted]
  | some pair =>
      rcases pair with ⟨expansionIndex, input⟩
      rcases o_post with
        ⟨returnedIndex, itemAt, decreases, exactDecrease, sameSlice,
          nextIndex, nextIndexBound, nextCountBound⟩
      step with typed_value_total_clone_spec as ⟨cloned, clonePost⟩
      step with alloc.vec.Vec.push_spec as ⟨nextPositional, pushPost⟩ by
        have maximumFits : BindCallFull.USIZE_CAPACITY.val <
            Std.Usize.max := by simp [BindCallFull.USIZE_CAPACITY]
        omega
      obtain ⟨inputBound, inputAt⟩ := getElem?_eq_some_iff.mp itemAt
      have sourceEq : iter.iter.slice.val = sourceValues := invariant.2.1
      have sourceBound : iter.iter.i < sourceValues.length := by
        simpa [sourceEq] using inputBound
      have takeStep := List.take_succ_eq_append_getElem
        (l := sourceValues) (i := iter.iter.i) sourceBound
      have takeLength : (sourceValues.take iter.iter.i).length = iter.iter.i := by
        simp [Nat.le_of_lt sourceBound]
      have sourceItemAt : sourceValues[iter.iter.i]? = some input := by
        simpa [sourceEq] using itemAt
      have sourceInput : sourceValues[iter.iter.i] = input := by
        simpa only [List.getElem?_eq_getElem sourceBound, Option.some.injEq]
          using sourceItemAt
      simp_all [preflightRemaining, positionalActualView, evaluationPositionView,
        fixedStarViewsFrom, fixedStarViewsFrom_append, takeStep, takeLength,
        sourceInput, List.map_append]
      omega

theorem expand_actual_items_fixed_star_loop_matches_reference
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter (BindCallFull.TypedValue String Int)))
    (positional : alloc.vec.Vec (BindCallFull.PositionalActual String Int))
    (itemIndex : Std.Usize)
    (initialViews : List PositionalActualView)
    (sourceValues : List (BindCallFull.TypedValue String Int))
    (invariant : fixedStarRecordInvariant itemIndex initialViews sourceValues
      (iter, positional)) :
    WP.spec
      (BindCallFull.expand_actual_items_with_allocator_loop0_loop0
        (totalIdentityClone String) (totalIdentityClone Int)
        iter positional itemIndex)
      (fun output => output.val.map positionalActualView =
        initialViews ++ fixedStarViewsFrom itemIndex.val 0 sourceValues) := by
  unfold BindCallFull.expand_actual_items_with_allocator_loop0_loop0
  apply loop.spec_decr_nat
      (measure := fun state => preflightRemaining state.1)
      (inv := fixedStarRecordInvariant itemIndex initialViews sourceValues)
      (post := fun (output : alloc.vec.Vec
          (BindCallFull.PositionalActual String Int)) =>
        output.val.map positionalActualView =
        initialViews ++ fixedStarViewsFrom itemIndex.val 0 sourceValues)
      (hInv := invariant)
  intro state stateInvariant
  rcases state with ⟨stateIter, statePositional⟩
  apply WP.spec_mono
    (expand_actual_items_fixed_star_loop_body_preserves_records_and_decreases
      itemIndex initialViews sourceValues (stateIter, statePositional)
      stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

def ordinaryActualMismatchReference
    (parameter : BindCallFull.FormalParameter String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalIndex : Nat) : Bool × Nat × Bool :=
  match call.positional.val[positionalIndex]? with
  | some actual =>
      (if parameter.expected_type == actual.value.type_tag then false else true,
        positionalIndex, false)
  | none =>
      let namedIndex := namedActualIndexReference call.named.deref parameter.name
      match call.named.val[namedIndex]? with
      | some actual =>
          (if parameter.expected_type == actual.value.type_tag then false else true,
            namedIndex, true)
      | none => (false, 0, false)

def ordinaryActualMismatchView
    (output : Bool × Std.Usize × Bool) : Bool × Nat × Bool :=
  (output.1, output.2.1.val, output.2.2)

theorem ordinary_actual_mismatch_matches_reference
    (parameter : BindCallFull.FormalParameter String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalIndex : Std.Usize) :
    WP.spec
      (BindCallFull.ordinary_actual_mismatch
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameter call positionalIndex ())
      (fun output => ordinaryActualMismatchView output =
        ordinaryActualMismatchReference parameter call positionalIndex.val) := by
  unfold BindCallFull.ordinary_actual_mismatch
  step with named_actual_index_matches_reference as ⟨namedIndex, namedIndexEq⟩
  by_cases positionalWithin : positionalIndex < alloc.vec.Vec.len call.positional
  · simp only [positionalWithin, if_true]
    have positionalBound : positionalIndex.val < call.positional.val.length := by
      simpa using positionalWithin
    step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
      exact positionalBound
    rw [compatibility_mismatch_string_exact]
    unfold ordinaryActualMismatchView ordinaryActualMismatchReference
    simp only [Prod.fst, Prod.snd]
    rw [List.getElem?_eq_getElem positionalBound]
    simp only [actualEq]
    by_cases typesEqual : parameter.expected_type =
        call.positional.val[positionalIndex.val].value.type_tag <;>
      simp [typesEqual]
  · simp only [positionalWithin, if_false]
    by_cases namedWithin : namedIndex < alloc.vec.Vec.len call.named
    · simp only [namedWithin, if_true]
      have namedBound : namedIndex.val < call.named.val.length := by
        simpa using namedWithin
      step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
        exact namedBound
      rw [compatibility_mismatch_string_exact]
      have positionalExhausted : call.positional.val.length ≤ positionalIndex.val := by
        simpa using positionalWithin
      have namedNatEq :
          namedActualIndexReference call.named.deref parameter.name = namedIndex.val :=
        namedIndexEq.symm
      unfold ordinaryActualMismatchView ordinaryActualMismatchReference
      simp only [Prod.fst, Prod.snd]
      rw [List.getElem?_eq_none positionalExhausted]
      rw [namedNatEq, List.getElem?_eq_getElem namedBound]
      simp only [actualEq]
      by_cases typesEqual : parameter.expected_type =
          call.named.val[namedIndex.val].value.type_tag <;>
        simp [typesEqual]
    · simp only [namedWithin, if_false]
      have positionalExhausted : call.positional.val.length ≤ positionalIndex.val := by
        simpa using positionalWithin
      have namedExhausted : call.named.val.length ≤ namedIndex.val := by
        simpa using namedWithin
      have namedNatEq :
          namedActualIndexReference call.named.deref parameter.name = namedIndex.val :=
        namedIndexEq.symm
      unfold ordinaryActualMismatchView ordinaryActualMismatchReference
      simp only [Prod.fst, Prod.snd]
      rw [List.getElem?_eq_none positionalExhausted]
      rw [namedNatEq, List.getElem?_eq_none namedExhausted]
      simp [WP.spec, WP.theta, WP.wp_return]

def ordinaryMismatchScanReference
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOffset parameterIndex : Nat)
    (mismatch : Bool) (actualIndex : Nat) (suppliedByName : Bool) :
    Nat × Bool × Nat × Bool :=
  if mismatch then
    (parameterIndex, true, actualIndex, suppliedByName)
  else
    match remaining with
    | [] => (parameterIndex, false, actualIndex, suppliedByName)
    | parameter :: tail =>
        let result := ordinaryActualMismatchReference parameter call
          (positionalOffset + parameterIndex)
        ordinaryMismatchScanReference tail call positionalOffset
          (parameterIndex + 1) result.1 result.2.1 result.2.2
termination_by remaining.length

@[simp]
theorem ordinaryMismatchScanReference_found_true
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOffset parameterIndex actualIndex : Nat)
    (suppliedByName : Bool) :
    ordinaryMismatchScanReference remaining call positionalOffset parameterIndex
      true actualIndex suppliedByName =
        (parameterIndex, true, actualIndex, suppliedByName) := by
  rw [ordinaryMismatchScanReference.eq_def]
  simp

@[simp]
theorem ordinaryMismatchScanReference_empty
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOffset parameterIndex actualIndex : Nat)
    (mismatch suppliedByName : Bool) :
    ordinaryMismatchScanReference [] call positionalOffset parameterIndex
      mismatch actualIndex suppliedByName =
        (parameterIndex, mismatch, actualIndex, suppliedByName) := by
  cases mismatch <;>
    simp [ordinaryMismatchScanReference.eq_def]

def ordinaryMismatchView
    (output : Std.Usize × Bool × Std.Usize × Bool) :
    Nat × Bool × Nat × Bool :=
  (output.1, output.2.1, output.2.2.1, output.2.2.2)

def ordinaryMismatchInvariant
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOffset : Std.Usize)
    (expected : Nat × Bool × Nat × Bool)
    (state : Std.Usize × Bool × Std.Usize × Bool) : Prop :=
  state.1.val ≤ parameters.val.length ∧
    positionalOffset.val + parameters.val.length ≤ Std.Usize.max ∧
    ordinaryMismatchScanReference (parameters.val.drop state.1.val) call
      positionalOffset.val state.1.val state.2.1 state.2.2.1.val
      state.2.2.2 = expected

def ordinaryMismatchRemaining
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (index : Std.Usize) : Nat :=
  parameters.val.length - index.val

theorem first_ordinary_type_mismatch_loop_body_preserves_reference_and_decreases
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOffset : Std.Usize)
    (expected : Nat × Bool × Nat × Bool)
    (state : Std.Usize × Bool × Std.Usize × Bool)
    (invariant : ordinaryMismatchInvariant parameters call positionalOffset
      expected state) :
    WP.spec
      (BindCallFull.first_ordinary_type_mismatch_loop.body
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters call () positionalOffset state.1 state.2.1 state.2.2.1
        state.2.2.2)
      (fun flow =>
        match flow with
        | .done output => ordinaryMismatchView output = expected
        | .cont next =>
            ordinaryMismatchInvariant parameters call positionalOffset
                expected next ∧
              ordinaryMismatchRemaining parameters next.1 <
                ordinaryMismatchRemaining parameters state.1) := by
  rcases state with ⟨parameterIndex, mismatch, actualIndex, suppliedByName⟩
  unfold BindCallFull.first_ordinary_type_mismatch_loop.body
  unfold ordinaryMismatchInvariant at invariant
  unfold ordinaryMismatchInvariant ordinaryMismatchRemaining ordinaryMismatchView
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  by_cases indexWithin : parameterIndex < alloc.vec.Vec.len parameters
  · simp only [indexWithin, if_true]
    by_cases alreadyMismatch : mismatch = true
    · have expectedEq :
          (parameterIndex.val, true, actualIndex.val, suppliedByName) = expected := by
        simpa [alreadyMismatch] using invariant.2.2
      simpa [alreadyMismatch] using expectedEq
    · have mismatchFalse := Bool.eq_false_of_not_eq_true alreadyMismatch
      simp only [mismatchFalse, Bool.false_eq_true, if_false]
      have parameterBound : parameterIndex.val < parameters.val.length := by
        simpa using indexWithin
      step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
        exact parameterBound
      step with Std.Usize.add_spec as ⟨positionalIndex, positionalIndexEq⟩ by
        omega
      step with ordinary_actual_mismatch_matches_reference as
        ⟨actualMismatch, actualOutputIndex, actualSupplied, actualMismatchEq⟩
      step with Std.Usize.add_spec as ⟨nextParameterIndex, nextParameterIndexEq⟩ by
        have parameterMachineBound := parameters.property
        omega
      have parameterDrop : parameters.val.drop parameterIndex.val =
          parameters.val[parameterIndex.val] ::
            parameters.val.drop (parameterIndex.val + 1) :=
        List.drop_eq_getElem_cons parameterBound
      have referenceStep := invariant.2.2
      rw [parameterDrop] at referenceStep
      rw [ordinaryMismatchScanReference.eq_2] at referenceStep
      simp only [mismatchFalse, Bool.false_eq_true, if_false] at referenceStep
      have mismatchReference :
          ordinaryActualMismatchView
            (actualMismatch, actualOutputIndex, actualSupplied) =
          ordinaryActualMismatchReference parameters.val[parameterIndex.val]
            call (positionalOffset.val + parameterIndex.val) := by
        simpa [parameterEq, positionalIndexEq] using actualMismatchEq
      change (actualMismatch, actualOutputIndex.val, actualSupplied) =
        ordinaryActualMismatchReference parameters.val[parameterIndex.val]
          call (positionalOffset.val + parameterIndex.val) at mismatchReference
      have mismatchBoolEq := congrArg Prod.fst mismatchReference
      have mismatchIndexEq := congrArg (fun output => output.2.1) mismatchReference
      have mismatchSuppliedEq := congrArg (fun output => output.2.2) mismatchReference
      rw [← mismatchBoolEq, ← mismatchIndexEq, ← mismatchSuppliedEq] at referenceStep
      simp only [nextParameterIndexEq]
      refine ⟨by omega, invariant.2.1, ?_, by omega⟩
      exact referenceStep
  · simp only [indexWithin, if_false]
    have exhausted : parameters.val.length ≤ parameterIndex.val := by
      simpa using indexWithin
    have atEnd : parameterIndex.val = parameters.val.length := by omega
    have expectedEq := invariant.2.2
    rw [atEnd] at expectedEq
    simp at expectedEq
    simpa [atEnd] using expectedEq

theorem first_ordinary_type_mismatch_loop_matches_reference
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOffset parameterIndex : Std.Usize)
    (mismatch : Bool) (actualIndex : Std.Usize) (suppliedByName : Bool)
    (indexBound : parameterIndex.val ≤ parameters.val.length)
    (offsetBound : positionalOffset.val + parameters.val.length ≤ Std.Usize.max) :
    WP.spec
      (BindCallFull.first_ordinary_type_mismatch_loop
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        parameters call () positionalOffset parameterIndex mismatch actualIndex
        suppliedByName)
      (fun output => ordinaryMismatchView output =
        ordinaryMismatchScanReference (parameters.val.drop parameterIndex.val)
          call positionalOffset.val parameterIndex.val mismatch actualIndex.val
          suppliedByName) := by
  let expected := ordinaryMismatchScanReference
    (parameters.val.drop parameterIndex.val) call positionalOffset.val
    parameterIndex.val mismatch actualIndex.val suppliedByName
  have initialInvariant : ordinaryMismatchInvariant parameters call
      positionalOffset expected
      (parameterIndex, mismatch, actualIndex, suppliedByName) :=
    ⟨indexBound, offsetBound, rfl⟩
  unfold BindCallFull.first_ordinary_type_mismatch_loop
  apply loop.spec_decr_nat
      (measure := fun state => ordinaryMismatchRemaining parameters state.1)
      (inv := ordinaryMismatchInvariant parameters call positionalOffset expected)
      (post := fun (output : Std.Usize × Bool × Std.Usize × Bool) =>
        ordinaryMismatchView output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (first_ordinary_type_mismatch_loop_body_preserves_reference_and_decreases
      parameters call positionalOffset expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem ordinaryActualMismatchReference_true_bound
    (parameter : BindCallFull.FormalParameter String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalIndex : Nat)
    (foundTrue :
      (ordinaryActualMismatchReference parameter call positionalIndex).1 = true) :
    if (ordinaryActualMismatchReference parameter call positionalIndex).2.2 then
      (ordinaryActualMismatchReference parameter call positionalIndex).2.1 <
        call.named.val.length
    else
      (ordinaryActualMismatchReference parameter call positionalIndex).2.1 <
        call.positional.val.length := by
  unfold ordinaryActualMismatchReference at foundTrue ⊢
  cases positionalEq : call.positional.val[positionalIndex]? with
  | some actual =>
      have positionalBound := (List.getElem?_eq_some_iff.mp positionalEq).1
      simp [positionalEq] at foundTrue ⊢
      exact positionalBound
  | none =>
      simp only [positionalEq]
      let namedIndex := namedActualIndexReference call.named.deref parameter.name
      cases namedEq : call.named.val[namedIndex]? with
      | none => simp [positionalEq, namedIndex, namedEq] at foundTrue
      | some actual =>
          have namedBound := (List.getElem?_eq_some_iff.mp namedEq).1
          simp [namedEq] at foundTrue ⊢
          exact namedBound

theorem ordinaryMismatchScanReference_true_bounds
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOffset parameterIndex actualIndex : Nat)
    (suppliedByName : Bool)
    (foundTrue :
      (ordinaryMismatchScanReference remaining call positionalOffset
        parameterIndex false actualIndex suppliedByName).2.1 = true) :
    parameterIndex <
        (ordinaryMismatchScanReference remaining call positionalOffset
          parameterIndex false actualIndex suppliedByName).1 ∧
      (ordinaryMismatchScanReference remaining call positionalOffset
          parameterIndex false actualIndex suppliedByName).1 ≤
        parameterIndex + remaining.length ∧
      (if (ordinaryMismatchScanReference remaining call positionalOffset
            parameterIndex false actualIndex suppliedByName).2.2.2 then
          (ordinaryMismatchScanReference remaining call positionalOffset
            parameterIndex false actualIndex suppliedByName).2.2.1 <
              call.named.val.length
        else
          (ordinaryMismatchScanReference remaining call positionalOffset
            parameterIndex false actualIndex suppliedByName).2.2.1 <
              call.positional.val.length) := by
  induction remaining generalizing parameterIndex actualIndex suppliedByName with
  | nil => simp at foundTrue
  | cons parameter tail inductionHypothesis =>
      rw [ordinaryMismatchScanReference.eq_def] at foundTrue ⊢
      simp only [Bool.false_eq_true, if_false] at foundTrue ⊢
      let result := ordinaryActualMismatchReference parameter call
        (positionalOffset + parameterIndex)
      by_cases resultTrue : result.1 = true
      · simp [result, resultTrue]
        exact ordinaryActualMismatchReference_true_bound parameter call
          (positionalOffset + parameterIndex) resultTrue
      · have resultFalse : result.1 = false :=
          Bool.eq_false_of_not_eq_true resultTrue
        have nextFound :
            (ordinaryMismatchScanReference tail call positionalOffset
              (parameterIndex + 1) false result.2.1 result.2.2).2.1 = true := by
          simpa only [result, resultFalse] using foundTrue
        have recursive := inductionHypothesis (parameterIndex + 1)
          result.2.1 result.2.2 nextFound
        simp only [result, resultFalse]
        dsimp [result] at recursive ⊢
        constructor
        · omega
        constructor
        · omega
        · exact recursive.2.2

def firstOrdinaryTypeMismatchReference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int) :
    Option (BindCallFull.BindingError String) :=
  let scan := ordinaryMismatchScanReference signature.positional.val call
    signature.positional_only.val.length 0 false 0 false
  if scan.2.1 then
    match signature.positional.val[scan.1 - 1]? with
    | none => none
    | some parameter =>
        if scan.2.2.2 then
          call.named.val[scan.2.2.1]?.map (fun actual =>
            BindCallFull.BindingError.TypeMismatch parameter.name
              parameter.expected_type actual.value.type_tag
              (some actual.evaluation_position))
        else
          call.positional.val[scan.2.2.1]?.map (fun actual =>
            BindCallFull.BindingError.TypeMismatch parameter.name
              parameter.expected_type actual.value.type_tag
              (some actual.evaluation_position))
  else
    none

theorem first_ordinary_type_mismatch_matches_reference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (offsetBound : signature.positional_only.val.length +
      signature.positional.val.length ≤ Std.Usize.max) :
    WP.spec
      (BindCallFull.first_ordinary_type_mismatch
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature call ())
      (fun output => output = firstOrdinaryTypeMismatchReference signature call) := by
  unfold BindCallFull.first_ordinary_type_mismatch
  apply WP.spec_bind
  · exact first_ordinary_type_mismatch_loop_matches_reference
      signature.positional call (alloc.vec.Vec.len signature.positional_only)
      0#usize false 0#usize false (by simp)
      (by simpa [alloc.vec.Vec.len] using offsetBound)
  · rintro ⟨parameterIndex, mismatch, actualIndex, suppliedByName⟩ scanEq
    change (parameterIndex.val, mismatch, actualIndex.val, suppliedByName) =
      ordinaryMismatchScanReference signature.positional.val call
        signature.positional_only.val.length 0 false 0 false at scanEq
    let scan := ordinaryMismatchScanReference signature.positional.val call
      signature.positional_only.val.length 0 false 0 false
    have scanEq' :
        (parameterIndex.val, mismatch, actualIndex.val, suppliedByName) = scan :=
      scanEq
    by_cases mismatchTrue : mismatch = true
    · simp [mismatchTrue]
      have scanTrue : scan.2.1 = true := by
        rw [← scanEq']
        exact mismatchTrue
      have scanBounds := ordinaryMismatchScanReference_true_bounds
        signature.positional.val call signature.positional_only.val.length
        0 0 false scanTrue
      change 0 < scan.1 ∧ scan.1 ≤ 0 + signature.positional.val.length ∧
        (if scan.2.2.2 = true then
          scan.2.2.1 < call.named.val.length
        else
          scan.2.2.1 < call.positional.val.length) at scanBounds
      have parameterIndexEq : parameterIndex.val = scan.1 :=
        congrArg Prod.fst scanEq'
      have actualIndexEq : actualIndex.val = scan.2.2.1 :=
        congrArg (fun output => output.2.2.1) scanEq'
      have suppliedEq : suppliedByName = scan.2.2.2 :=
        congrArg (fun output => output.2.2.2) scanEq'
      have parameterPositive : 0 < parameterIndex.val := by
        rw [parameterIndexEq]
        exact scanBounds.1
      step with Std.Usize.sub_spec as ⟨mismatchIndex, mismatchIndexEq⟩ by
        simpa using parameterPositive
      have mismatchIndexNat : mismatchIndex.val = scan.1 - 1 := by
        rw [mismatchIndexEq, parameterIndexEq]
      have parameterBound : mismatchIndex.val <
          signature.positional.val.length := by
        have scanUpper : scan.1 ≤ signature.positional.val.length := by
          simpa using scanBounds.2.1
        omega
      step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
        exact parameterBound
      by_cases suppliedTrue : suppliedByName = true
      · simp [suppliedTrue]
        have scanSuppliedTrue : scan.2.2.2 = true := by
          rw [← suppliedEq]
          exact suppliedTrue
        have namedBound : actualIndex.val < call.named.val.length := by
          rw [actualIndexEq]
          simpa [scanSuppliedTrue] using scanBounds.2.2
        step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
          exact namedBound
        rw [string_clone_exact, totalIdentityClone_exact,
          totalIdentityClone_exact]
        unfold firstOrdinaryTypeMismatchReference
        change some (BindCallFull.BindingError.TypeMismatch parameter.name
            parameter.expected_type actual.value.type_tag
            (some actual.evaluation_position)) =
          if scan.2.1 = true then
            match signature.positional.val[scan.1 - 1]? with
            | none => none
            | some parameter =>
                if scan.2.2.2 = true then
                  call.named.val[scan.2.2.1]?.map (fun actual =>
                    BindCallFull.BindingError.TypeMismatch parameter.name
                      parameter.expected_type actual.value.type_tag
                      (some actual.evaluation_position))
                else
                  call.positional.val[scan.2.2.1]?.map (fun actual =>
                    BindCallFull.BindingError.TypeMismatch parameter.name
                      parameter.expected_type actual.value.type_tag
                      (some actual.evaluation_position))
          else none
        rw [scanTrue]
        simp only [if_true]
        rw [List.getElem?_eq_getElem (by omega : scan.1 - 1 <
          signature.positional.val.length)]
        simp only [parameterEq, mismatchIndexNat, scanSuppliedTrue, if_true]
        rw [List.getElem?_eq_getElem (by simpa [actualIndexEq] using
          namedBound)]
        simp [actualEq, actualIndexEq]
      · have suppliedFalse : suppliedByName = false :=
          Bool.eq_false_of_not_eq_true suppliedTrue
        simp [suppliedFalse]
        have scanSuppliedFalse : scan.2.2.2 = false := by
          rw [← suppliedEq]
          exact suppliedFalse
        have positionalBound : actualIndex.val < call.positional.val.length := by
          rw [actualIndexEq]
          simpa [scanSuppliedFalse] using scanBounds.2.2
        step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
          exact positionalBound
        rw [string_clone_exact, totalIdentityClone_exact,
          totalIdentityClone_exact]
        unfold firstOrdinaryTypeMismatchReference
        change some (BindCallFull.BindingError.TypeMismatch parameter.name
            parameter.expected_type actual.value.type_tag
            (some actual.evaluation_position)) =
          if scan.2.1 = true then
            match signature.positional.val[scan.1 - 1]? with
            | none => none
            | some parameter =>
                if scan.2.2.2 = true then
                  call.named.val[scan.2.2.1]?.map (fun actual =>
                    BindCallFull.BindingError.TypeMismatch parameter.name
                      parameter.expected_type actual.value.type_tag
                      (some actual.evaluation_position))
                else
                  call.positional.val[scan.2.2.1]?.map (fun actual =>
                    BindCallFull.BindingError.TypeMismatch parameter.name
                      parameter.expected_type actual.value.type_tag
                      (some actual.evaluation_position))
          else none
        rw [scanTrue]
        simp only [if_true]
        rw [List.getElem?_eq_getElem (by omega : scan.1 - 1 <
          signature.positional.val.length)]
        simp only [parameterEq, mismatchIndexNat, scanSuppliedFalse,
          Bool.false_eq_true, if_false]
        rw [List.getElem?_eq_getElem (by simpa [actualIndexEq] using
          positionalBound)]
        simp [actualEq, actualIndexEq]
    · have mismatchFalse : mismatch = false :=
        Bool.eq_false_of_not_eq_true mismatchTrue
      simp [mismatchFalse]
      unfold firstOrdinaryTypeMismatchReference
      have scanFalse : scan.2.1 = false := by
        rw [← scanEq']
        exact mismatchFalse
      change none = if scan.2.1 = true then _ else none
      simp [scanFalse]

def validateMismatchProgram
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalCount : Std.Usize) :
    Result (core.result.Result Unit (BindCallFull.BindingError String)) := do
  let missing ← BindCallFull.first_missing_required_argument
    (totalIdentityClone String) signature call
  match missing with
  | none =>
      let positionalOnly ← BindCallFull.first_positional_only_type_mismatch
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature call ()
      match positionalOnly with
      | none =>
          let ordinary ← BindCallFull.first_ordinary_type_mismatch
            (totalIdentityClone String)
            (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
              totalStringEq)
            signature call ()
          match ordinary with
          | none =>
              let keywordOnly ← BindCallFull.first_keyword_only_type_mismatch
                (totalIdentityClone String)
                (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
                  totalStringEq)
                signature call ()
              match keywordOnly with
              | none =>
                  let variadic ← BindCallFull.first_variadic_type_mismatch
                    (totalIdentityClone String)
                    (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
                      totalStringEq)
                    signature call positionalCount ()
                  match variadic with
                  | none => ok (.Ok ())
                  | some error => ok (.Err error)
              | some error => ok (.Err error)
          | some error => ok (.Err error)
      | some error => ok (.Err error)
  | some error => ok (.Err error)

def validateMismatchReference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalCount : Nat) :
    core.result.Result Unit (BindCallFull.BindingError String) :=
  match firstMissingRequiredArgumentReference signature call with
  | some error => .Err error
  | none =>
      match firstPositionalOnlyTypeMismatchReference signature call with
      | some error => .Err error
      | none =>
          match firstOrdinaryTypeMismatchReference signature call with
          | some error => .Err error
          | none =>
              match firstKeywordOnlyTypeMismatchReference signature call with
              | some error => .Err error
              | none =>
                  match firstVariadicTypeMismatchReference signature call
                      positionalCount with
                  | some error => .Err error
                  | none => .Ok ()

theorem validateMismatchProgram_matches_reference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalCount : Std.Usize)
    (offsetBound : signature.positional_only.val.length +
      signature.positional.val.length ≤ Std.Usize.max) :
    WP.spec (validateMismatchProgram signature call positionalCount)
      (fun output => output = validateMismatchReference signature call
        positionalCount.val) := by
  unfold validateMismatchProgram
  step with first_missing_required_argument_matches_reference as
    ⟨missing, missingEq⟩ by exact offsetBound
  cases missingReferenceEq : firstMissingRequiredArgumentReference signature call with
  | some error =>
      simp only [missingReferenceEq] at missingEq
      simp [missingEq, validateMismatchReference, missingReferenceEq,
        WP.spec, WP.theta, WP.wp_return]
  | none =>
      simp only [missingReferenceEq] at missingEq
      simp only [missingEq]
      step with first_positional_only_type_mismatch_matches_reference as
        ⟨positionalOnly, positionalOnlyEq⟩
      cases positionalOnlyReferenceEq :
          firstPositionalOnlyTypeMismatchReference signature call with
      | some error =>
          simp only [positionalOnlyReferenceEq] at positionalOnlyEq
          simp [positionalOnlyEq, validateMismatchReference,
            missingReferenceEq, positionalOnlyReferenceEq,
            WP.spec, WP.theta, WP.wp_return]
      | none =>
          simp only [positionalOnlyReferenceEq] at positionalOnlyEq
          simp only [positionalOnlyEq]
          step with first_ordinary_type_mismatch_matches_reference as
            ⟨ordinary, ordinaryEq⟩ by exact offsetBound
          cases ordinaryReferenceEq : firstOrdinaryTypeMismatchReference
              signature call with
          | some error =>
              simp only [ordinaryReferenceEq] at ordinaryEq
              simp [ordinaryEq, validateMismatchReference,
                missingReferenceEq, positionalOnlyReferenceEq,
                ordinaryReferenceEq, WP.spec, WP.theta, WP.wp_return]
          | none =>
              simp only [ordinaryReferenceEq] at ordinaryEq
              simp only [ordinaryEq]
              step with first_keyword_only_type_mismatch_matches_reference as
                ⟨keywordOnly, keywordOnlyEq⟩
              cases keywordOnlyReferenceEq :
                  firstKeywordOnlyTypeMismatchReference signature call with
              | some error =>
                  simp only [keywordOnlyReferenceEq] at keywordOnlyEq
                  simp [keywordOnlyEq, validateMismatchReference,
                    missingReferenceEq, positionalOnlyReferenceEq,
                    ordinaryReferenceEq, keywordOnlyReferenceEq,
                    WP.spec, WP.theta, WP.wp_return]
              | none =>
                  simp only [keywordOnlyReferenceEq] at keywordOnlyEq
                  simp only [keywordOnlyEq]
                  step with first_variadic_type_mismatch_matches_reference_total as
                    ⟨variadic, variadicEq⟩
                  cases variadicReferenceEq : firstVariadicTypeMismatchReference
                      signature call positionalCount.val with
                  | some error =>
                      simp only [variadicReferenceEq] at variadicEq
                      simp [variadicEq, validateMismatchReference,
                        missingReferenceEq, positionalOnlyReferenceEq,
                        ordinaryReferenceEq, keywordOnlyReferenceEq,
                        variadicReferenceEq, WP.spec, WP.theta, WP.wp_return]
                  | none =>
                      simp only [variadicReferenceEq] at variadicEq
                      simp [variadicEq, validateMismatchReference,
                        missingReferenceEq, positionalOnlyReferenceEq,
                        ordinaryReferenceEq, keywordOnlyReferenceEq,
                        variadicReferenceEq, WP.spec, WP.theta, WP.wp_return]

macro "solve_validate_mismatch_alpha" : tactic => `(tactic| (
  rw [Aeneas.Std.bind_eq_iff]
  intro missing missingEq
  cases missing with
  | some error => rfl
  | none =>
      rw [Aeneas.Std.bind_eq_iff]
      intro positionalOnly positionalOnlyEq
      cases positionalOnly with
      | some error => rfl
      | none =>
          rw [Aeneas.Std.bind_eq_iff]
          intro ordinary ordinaryEq
          cases ordinary with
          | some error => rfl
          | none =>
              rw [Aeneas.Std.bind_eq_iff]
              intro keywordOnly keywordOnlyEq
              cases keywordOnly with
              | some error => rfl
              | none =>
                  rw [Aeneas.Std.bind_eq_iff]
                  intro variadic variadicEq
                  cases variadic <;> rfl))
def validateCallTailProgram
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalCount : Std.Usize) :
    Result (core.result.Result Unit (BindCallFull.BindingError String)) := do
  let named := alloc.vec.Vec.deref call.named
  let unexpectedKeyword ←
    BindCallFull.first_unexpected_keyword named signature
  let noKeywordArgs := signature.keyword_args.isNone
  if noKeywordArgs then
    let namedCount := alloc.vec.Vec.len call.named
    if unexpectedKeyword < namedCount then
      let actual ← call.named.index_usize unexpectedKeyword
      let clonedName ←
        alloc.string.String.Insts.CoreCloneClone.clone actual.name
      ok (.Err (.UnexpectedKeyword clonedName))
    else do
      let missing ← BindCallFull.first_missing_required_argument
        (totalIdentityClone String) signature call
      match missing with
      | none => do
          let positionalOnly ←
            BindCallFull.first_positional_only_type_mismatch
              (totalIdentityClone String)
              (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
                totalStringEq)
              signature call ()
          match positionalOnly with
          | none => do
              let ordinary ← BindCallFull.first_ordinary_type_mismatch
                (totalIdentityClone String)
                (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
                  totalStringEq)
                signature call ()
              match ordinary with
              | none => do
                  let keywordOnly ←
                    BindCallFull.first_keyword_only_type_mismatch
                      (totalIdentityClone String)
                      (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
                        totalStringEq)
                      signature call ()
                  match keywordOnly with
                  | none => do
                      let variadic ←
                        BindCallFull.first_variadic_type_mismatch
                          (totalIdentityClone String)
                          (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
                            totalStringEq)
                          signature call positionalCount ()
                      match variadic with
                      | none => ok (.Ok ())
                      | some error => ok (.Err error)
                  | some error => ok (.Err error)
              | some error => ok (.Err error)
          | some error => ok (.Err error)
      | some error => ok (.Err error)
  else do
    let missing ← BindCallFull.first_missing_required_argument
      (totalIdentityClone String) signature call
    match missing with
    | none => do
        let positionalOnly ←
          BindCallFull.first_positional_only_type_mismatch
            (totalIdentityClone String)
            (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
              totalStringEq)
            signature call ()
        match positionalOnly with
        | none => do
            let ordinary ← BindCallFull.first_ordinary_type_mismatch
              (totalIdentityClone String)
              (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
                totalStringEq)
              signature call ()
            match ordinary with
            | none => do
                let keywordOnly ←
                  BindCallFull.first_keyword_only_type_mismatch
                    (totalIdentityClone String)
                    (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
                      totalStringEq)
                    signature call ()
                match keywordOnly with
                | none => do
                    let variadic ←
                      BindCallFull.first_variadic_type_mismatch
                        (totalIdentityClone String)
                        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
                          totalStringEq)
                        signature call positionalCount ()
                    match variadic with
                    | none => ok (.Ok ())
                    | some error => ok (.Err error)
                | some error => ok (.Err error)
            | some error => ok (.Err error)
        | some error => ok (.Err error)
    | some error => ok (.Err error)

def validateCallTailReference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalCount : Nat) :
    core.result.Result Unit (BindCallFull.BindingError String) :=
  let unexpected := firstUnexpectedKeywordReference call.named.deref signature
  if signature.keyword_args.isNone then
    if unexpected < call.named.val.length then
      match call.named.val[unexpected]? with
      | some actual => .Err (.UnexpectedKeyword actual.name)
      | none => validateMismatchReference signature call positionalCount
    else
      validateMismatchReference signature call positionalCount
  else
    validateMismatchReference signature call positionalCount

theorem validateCallTailProgram_matches_reference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalCount : Std.Usize)
    (offsetBound : signature.positional_only.val.length +
      signature.positional.val.length ≤ Std.Usize.max) :
    WP.spec (validateCallTailProgram signature call positionalCount)
      (fun output => output = validateCallTailReference signature call
        positionalCount.val) := by
  unfold validateCallTailProgram
  step with first_unexpected_keyword_matches_reference as
    ⟨unexpected, unexpectedEq⟩
  cases keywordArgsEq : signature.keyword_args with
  | none =>
      simp only [keywordArgsEq, Option.isNone_none, if_true]
      by_cases unexpectedWithin : unexpected < alloc.vec.Vec.len call.named
      · simp only [unexpectedWithin, if_true]
        have unexpectedBound : unexpected.val < call.named.val.length := by
          simpa [alloc.vec.Vec.len] using unexpectedWithin
        step with alloc.vec.Vec.index_usize_spec as ⟨actual, actualEq⟩ by
          exact unexpectedBound
        rw [string_clone_exact]
        unfold validateCallTailReference
        rw [← unexpectedEq]
        simp only [keywordArgsEq, Option.isNone_none, if_true]
        rw [if_pos unexpectedBound]
        rw [List.getElem?_eq_getElem unexpectedBound]
        simp [actualEq, unexpectedEq, WP.spec, WP.theta, WP.wp_return]
      · simp only [unexpectedWithin, if_false]
        have referenceNotWithin :
            ¬firstUnexpectedKeywordReference call.named.deref signature <
              call.named.val.length := by
          simpa [unexpectedEq, alloc.vec.Vec.len] using unexpectedWithin
        apply WP.spec_mono
          (validateMismatchProgram_matches_reference signature call
            positionalCount offsetBound)
        intro output outputEq
        simpa [validateCallTailReference, keywordArgsEq, referenceNotWithin]
          using outputEq
  | some keywordParameter =>
      simp only [keywordArgsEq, Option.isNone_some, if_false]
      apply WP.spec_mono
        (validateMismatchProgram_matches_reference signature call
          positionalCount offsetBound)
      intro output outputEq
      simpa [validateCallTailReference, keywordArgsEq] using outputEq

def signaturePositionalCount
    (signature : BindCallFull.CallSignature String Int) : Std.Usize :=
  core.num.Usize.saturating_add
    (alloc.vec.Vec.len signature.positional_only)
    (alloc.vec.Vec.len signature.positional)

def validateCallReference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int) :
    core.result.Result Unit (BindCallFull.BindingError String) :=
  match duplicateNamedOuterReference call.named.val call.named.val 0 none with
  | some duplicateName => .Err (.DuplicateNamedArgument duplicateName)
  | none =>
      match firstDuplicateBindingReference signature call with
      | some error => .Err error
      | none =>
          let positionalCount := signaturePositionalCount signature
          if call.positional.val.length > positionalCount.val then
            if signature.var_args.isNone then
              .Err (.TooManyPositionals positionalCount
                (alloc.vec.Vec.len call.positional))
            else
              validateCallTailReference signature call positionalCount.val
          else validateCallTailReference signature call positionalCount.val

set_option maxRecDepth 10000 in
theorem validate_call_matches_exact_reference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (offsetBound : signature.positional_only.val.length +
      signature.positional.val.length ≤ Std.Usize.max) :
    WP.spec
      (BindCallFull.validate_call
        (totalIdentityClone String)
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        signature call (signaturePositionalCount signature) ())
      (fun output => output = validateCallReference signature call) := by
  unfold BindCallFull.validate_call
  step with first_duplicate_named_actual_matches_reference as
    ⟨duplicateNamed, duplicateNamedEq⟩
  cases duplicateNamedReferenceEq :
      duplicateNamedOuterReference call.named.val call.named.val 0 none with
  | some duplicateName =>
      have duplicateNamedValue : duplicateNamed = some duplicateName :=
        duplicateNamedEq.trans duplicateNamedReferenceEq
      rw [duplicateNamedValue]
      simp [validateCallReference,
        duplicateNamedReferenceEq, WP.spec, WP.theta, WP.wp_return]
  | none =>
      have duplicateNamedValue : duplicateNamed = none :=
        duplicateNamedEq.trans duplicateNamedReferenceEq
      rw [duplicateNamedValue]
      step with first_duplicate_binding_matches_reference as
        ⟨duplicateBinding, duplicateBindingEq⟩ by exact offsetBound
      cases duplicateBindingReferenceEq : firstDuplicateBindingReference
          signature call with
      | some error =>
          have duplicateBindingValue : duplicateBinding = some error :=
            duplicateBindingEq.trans duplicateBindingReferenceEq
          simp [duplicateBindingValue, validateCallReference,
            duplicateNamedReferenceEq, duplicateBindingReferenceEq,
            WP.spec, WP.theta, WP.wp_return]
      | none =>
          have duplicateBindingValue : duplicateBinding = none :=
            duplicateBindingEq.trans duplicateBindingReferenceEq
          rw [duplicateBindingValue]
          let positionalCount := signaturePositionalCount signature
          have positionalCountIdentity : positionalCount =
              signaturePositionalCount signature := rfl
          by_cases tooMany : alloc.vec.Vec.len call.positional > positionalCount
          · rw [if_pos tooMany]
            cases varArgsEq : signature.var_args with
            | none =>
                simp only [Option.isNone_none, if_true]
                unfold validateCallReference
                rw [duplicateNamedReferenceEq, duplicateBindingReferenceEq]
                simp only
                rw [← positionalCountIdentity]
                have tooManyNat : call.positional.val.length > positionalCount.val := by
                  simpa [alloc.vec.Vec.len] using tooMany
                rw [if_pos tooManyNat]
                simp [varArgsEq, positionalCountIdentity,
                  WP.spec, WP.theta, WP.wp_return]
            | some varParameter =>
                simp only [Option.isNone_some, Bool.false_eq_true, if_false]
                have tailSpec := validateCallTailProgram_matches_reference
                  signature call positionalCount offsetBound
                have tailSpec' : WP.spec
                    (validateCallTailProgram signature call positionalCount)
                    (fun output => output =
                      validateCallReference signature call) := by
                  apply WP.spec_mono tailSpec
                  intro output outputEq
                  unfold validateCallReference
                  rw [duplicateNamedReferenceEq,
                    duplicateBindingReferenceEq]
                  simp only
                  rw [← positionalCountIdentity]
                  have tooManyNat : call.positional.val.length >
                      positionalCount.val := by
                    simpa [alloc.vec.Vec.len] using tooMany
                  rw [if_pos tooManyNat]
                  simp [varArgsEq, outputEq]
                unfold validateCallTailProgram at tailSpec'
                convert tailSpec' using 1
                dsimp only
                rw [Aeneas.Std.bind_eq_iff]
                intro unexpected unexpectedEq
                cases hKeywordArgs : signature.keyword_args with
                | none =>
                    simp only [hKeywordArgs, Option.isNone_none, if_true]
                    by_cases unexpectedWithin :
                        unexpected < alloc.vec.Vec.len call.named
                    · simp only [unexpectedWithin, if_true]
                    · simp only [unexpectedWithin, if_false]
                      solve_validate_mismatch_alpha
                | some keywordArgs =>
                    simp only [hKeywordArgs, Option.isNone_some,
                      Bool.false_eq_true, if_false]
                    solve_validate_mismatch_alpha
          · rw [if_neg tooMany]
            have tailSpec := validateCallTailProgram_matches_reference
              signature call positionalCount offsetBound
            have tailSpec' : WP.spec
                (validateCallTailProgram signature call positionalCount)
                (fun output => output =
                  validateCallReference signature call) := by
              apply WP.spec_mono tailSpec
              intro output outputEq
              unfold validateCallReference
              rw [duplicateNamedReferenceEq, duplicateBindingReferenceEq]
              simp only
              rw [← positionalCountIdentity]
              have notTooManyNat : ¬call.positional.val.length >
                  positionalCount.val := by
                simpa [alloc.vec.Vec.len] using tooMany
              rw [if_neg notTooManyNat]
              exact outputEq
            unfold validateCallTailProgram at tailSpec'
            convert tailSpec' using 1
            dsimp only
            rw [Aeneas.Std.bind_eq_iff]
            intro unexpected unexpectedEq
            cases hKeywordArgs : signature.keyword_args with
            | none =>
                simp only [hKeywordArgs, Option.isNone_none, if_true]
                by_cases unexpectedWithin :
                    unexpected < alloc.vec.Vec.len call.named
                · simp only [unexpectedWithin, if_true]
                · simp only [unexpectedWithin, if_false]
                  solve_validate_mismatch_alpha
            | some keywordArgs =>
                simp only [hKeywordArgs, Option.isNone_some,
                  Bool.false_eq_true, if_false]
                solve_validate_mismatch_alpha

theorem formal_parameter_total_clone_exact
    (parameter : BindCallFull.FormalParameter String Int) :
    BindCallFull.FormalParameter.Insts.CoreCloneClone.clone
      (totalIdentityClone String) (totalIdentityClone Int) parameter =
        .ok parameter := by
  rcases parameter with ⟨parameterName, expectedType, defaultValue⟩
  cases defaultValue with
  | none =>
      simp [BindCallFull.FormalParameter.Insts.CoreCloneClone.clone,
        core.option.Option.Insts.CoreCloneClone.clone,
        string_clone_exact, totalIdentityClone_exact,
        BindCallFull.TypedValue.Insts.CoreCloneClone]
  | some defaultValue =>
      rcases defaultValue with ⟨typeTag, payload⟩
      simp [BindCallFull.FormalParameter.Insts.CoreCloneClone.clone,
        core.option.Option.Insts.CoreCloneClone.clone,
        BindCallFull.TypedValue.Insts.CoreCloneClone.clone,
        BindCallFull.TypedValue.Insts.CoreCloneClone,
        string_clone_exact, totalIdentityClone_exact]

@[step]
theorem formal_parameter_total_clone_spec
    (parameter : BindCallFull.FormalParameter String Int) :
    WP.spec
      (BindCallFull.FormalParameter.Insts.CoreCloneClone.clone
        (totalIdentityClone String) (totalIdentityClone Int) parameter)
      (fun output => output = parameter) := by
  rw [formal_parameter_total_clone_exact]
  simp [WP.spec, WP.theta, WP.wp_return]

@[step]
theorem positional_actual_total_clone_spec
    (actual : BindCallFull.PositionalActual String Int) :
    WP.spec
      (BindCallFull.PositionalActual.Insts.CoreCloneClone.clone
        (totalIdentityClone String) (totalIdentityClone Int) actual)
      (fun output => output = actual) := by
  rw [positional_actual_total_clone_exact]
  simp [WP.spec, WP.theta, WP.wp_return]

def canonicalPositionalOnlyStep
    (parameter : BindCallFull.FormalParameter String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (index : Nat)
    (cells : List (BindCallFull.BindingCell String Int))
    (constructionError : Option (BindCallFull.BindingError String)) :
    List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String) :=
  match constructionError with
  | some error => (cells, some error)
  | none =>
      match call.positional.val[index]? with
      | some actual =>
          (cells ++ [{
            parameter := parameter
            kind := .PositionalOnly
            argument := .SuppliedPositional actual
          }], none)
      | none =>
          match parameter.default_value with
          | some defaultValue =>
              (cells ++ [{
                parameter := parameter
                kind := .PositionalOnly
                argument := .Defaulted defaultValue
              }], none)
          | none =>
              (cells, some (.MissingRequiredArgument parameter.name))

def canonicalPositionalOnlyReference
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (index : Nat)
    (cells : List (BindCallFull.BindingCell String Int))
    (constructionError : Option (BindCallFull.BindingError String)) :
    List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String) :=
  match remaining with
  | [] => (cells, constructionError)
  | parameter :: tail =>
      let next := canonicalPositionalOnlyStep parameter call index cells
        constructionError
      canonicalPositionalOnlyReference tail call (index + 1) next.1 next.2
termination_by remaining.length

def canonicalPositionalOnlyInvariant
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (initialCall : BindCallFull.ExpandedCall String Int)
    (expected : List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String))
    (state : BindCallFull.ExpandedCall String Int ×
      alloc.vec.Vec (BindCallFull.BindingCell String Int) × Std.Usize ×
      Option (BindCallFull.BindingError String)) : Prop :=
  state.1 = initialCall ∧
    state.2.2.1.val ≤ parameters.val.length ∧
    state.2.1.val.length +
        (parameters.val.length - state.2.2.1.val) ≤
      BindCallFull.USIZE_CAPACITY.val ∧
    canonicalPositionalOnlyReference
      (parameters.val.drop state.2.2.1.val) initialCall state.2.2.1.val
      state.2.1.val state.2.2.2 = expected

def canonicalPositionalOnlyRemaining
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (index : Std.Usize) : Nat :=
  parameters.val.length - index.val

theorem canonical_environment_loop0_body_preserves_reference_and_decreases
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (initialCall : BindCallFull.ExpandedCall String Int)
    (expected : List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String))
    (state : BindCallFull.ExpandedCall String Int ×
      alloc.vec.Vec (BindCallFull.BindingCell String Int) × Std.Usize ×
      Option (BindCallFull.BindingError String))
    (invariant : canonicalPositionalOnlyInvariant parameters initialCall
      expected state) :
    WP.spec
      (BindCallFull.canonical_environment_loop0.body
        (totalIdentityClone String) (totalIdentityClone Int)
        parameters state.1 state.2.1 state.2.2.1 state.2.2.2)
      (fun flow =>
        match flow with
        | .done output =>
            output.1 = initialCall ∧
              (output.2.1.val, output.2.2) = expected
        | .cont next =>
            canonicalPositionalOnlyInvariant parameters initialCall expected
                next ∧
              canonicalPositionalOnlyRemaining parameters next.2.2.1 <
                canonicalPositionalOnlyRemaining parameters state.2.2.1) := by
  rcases state with ⟨call, cells, index, constructionError⟩
  unfold BindCallFull.canonical_environment_loop0.body
  unfold canonicalPositionalOnlyInvariant at invariant
  unfold canonicalPositionalOnlyInvariant canonicalPositionalOnlyRemaining
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  rw [invariant.1]
  by_cases indexWithin : index < alloc.vec.Vec.len parameters
  · simp only [indexWithin, if_true]
    have parameterBound : index.val < parameters.val.length := by
      simpa using indexWithin
    step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
      exact parameterBound
    cases constructionError with
    | some error =>
        simp only [Option.isNone, Bool.false_eq_true, if_false]
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have parameterMachineBound := parameters.property
          omega
        have parameterDrop : parameters.val.drop index.val =
            parameters.val[index.val] :: parameters.val.drop (index.val + 1) :=
          List.drop_eq_getElem_cons parameterBound
        have referenceStep := invariant.2.2.2
        rw [parameterDrop] at referenceStep
        rw [canonicalPositionalOnlyReference.eq_2] at referenceStep
        rw [← parameterEq] at referenceStep
        simp only [canonicalPositionalOnlyStep] at referenceStep
        simp only [nextIndexEq]
        have remainingStep : parameters.val.length - index.val =
            (parameters.val.length - (index.val + 1)) + 1 := by omega
        exact ⟨by omega, by omega, referenceStep, by omega⟩
    | none =>
        simp only [Option.isNone, if_true]
        simp only [core.slice.Slice.get,
          core.slice.index.SliceIndexUsizeSlice,
          core.slice.index.Usize.get]
        cases positionalEq : initialCall.positional.val[index.val]? with
        | none =>
            simp only [alloc.vec.Vec.deref, Slice.getElem?_Usize_eq,
              positionalEq, bind_ok]
            cases defaultEq : parameter.default_value with
            | none =>
                simp only [defaultEq, bind_ok, string_clone_exact]
                step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
                  have parameterMachineBound := parameters.property
                  omega
                have parameterDrop : parameters.val.drop index.val =
                    parameters.val[index.val] ::
                      parameters.val.drop (index.val + 1) :=
                  List.drop_eq_getElem_cons parameterBound
                have referenceStep := invariant.2.2.2
                rw [parameterDrop] at referenceStep
                rw [canonicalPositionalOnlyReference.eq_2] at referenceStep
                rw [← parameterEq] at referenceStep
                simp only [canonicalPositionalOnlyStep, positionalEq, defaultEq]
                  at referenceStep
                simp only [nextIndexEq]
                exact ⟨by omega, by omega, referenceStep, by omega⟩
            | some defaultValue =>
                simp only [defaultEq, bind_ok, typed_value_total_clone_exact,
                  formal_parameter_total_clone_exact]
                have parameterRebuild :
                    ({ parameter with default_value := some defaultValue } :
                      BindCallFull.FormalParameter String Int) = parameter := by
                  rcases parameter with ⟨parameterName, expectedType,
                    parameterDefault⟩
                  simp_all
                step with alloc.vec.Vec.push_spec as ⟨nextCells, pushEq⟩ by
                  have maximumFits : BindCallFull.USIZE_CAPACITY.val <
                      Std.Usize.max := by
                    simp [BindCallFull.USIZE_CAPACITY]
                  omega
                step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
                  have parameterMachineBound := parameters.property
                  omega
                have parameterDrop : parameters.val.drop index.val =
                    parameters.val[index.val] ::
                      parameters.val.drop (index.val + 1) :=
                  List.drop_eq_getElem_cons parameterBound
                have referenceStep := invariant.2.2.2
                rw [parameterDrop] at referenceStep
                rw [canonicalPositionalOnlyReference.eq_2] at referenceStep
                rw [← parameterEq] at referenceStep
                simp only [canonicalPositionalOnlyStep, positionalEq, defaultEq]
                  at referenceStep
                simp only [parameterRebuild, pushEq, nextIndexEq,
                  List.length_append, List.length_singleton]
                have remainingStep : parameters.val.length - index.val =
                    (parameters.val.length - (index.val + 1)) + 1 := by omega
                exact ⟨by omega, by omega, referenceStep, by omega⟩
        | some actual =>
            simp only [alloc.vec.Vec.deref, Slice.getElem?_Usize_eq,
              positionalEq, bind_ok, positional_actual_total_clone_exact,
              formal_parameter_total_clone_exact]
            step with alloc.vec.Vec.push_spec as ⟨nextCells, pushEq⟩ by
              have maximumFits : BindCallFull.USIZE_CAPACITY.val <
                  Std.Usize.max := by simp [BindCallFull.USIZE_CAPACITY]
              omega
            step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
              have parameterMachineBound := parameters.property
              omega
            have parameterDrop : parameters.val.drop index.val =
                parameters.val[index.val] :: parameters.val.drop (index.val + 1) :=
              List.drop_eq_getElem_cons parameterBound
            have positionalInput : initialCall.positional.val[index.val]? =
                some actual := positionalEq
            have referenceStep := invariant.2.2.2
            rw [parameterDrop] at referenceStep
            rw [canonicalPositionalOnlyReference.eq_2] at referenceStep
            rw [← parameterEq] at referenceStep
            simp only [canonicalPositionalOnlyStep, positionalInput] at referenceStep
            simp only [pushEq, nextIndexEq,
              List.length_append, List.length_singleton]
            have remainingStep : parameters.val.length - index.val =
                (parameters.val.length - (index.val + 1)) + 1 := by omega
            exact ⟨by omega, by omega, referenceStep, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : parameters.val.length ≤ index.val := by simpa using indexWithin
    have atEnd : index.val = parameters.val.length := by omega
    have referenceEq := invariant.2.2.2
    rw [atEnd] at referenceEq
    simp [canonicalPositionalOnlyReference] at referenceEq
    exact ⟨rfl, referenceEq⟩

theorem canonical_environment_loop0_matches_reference
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (cells : alloc.vec.Vec (BindCallFull.BindingCell String Int))
    (index : Std.Usize)
    (constructionError : Option (BindCallFull.BindingError String))
    (indexBound : index.val ≤ parameters.val.length)
    (capacityBound : cells.val.length +
        (parameters.val.length - index.val) ≤
      BindCallFull.USIZE_CAPACITY.val) :
    WP.spec
      (BindCallFull.canonical_environment_loop0
        (totalIdentityClone String) (totalIdentityClone Int)
        parameters call cells index constructionError)
      (fun output =>
        output.1 = call ∧
          (output.2.1.val, output.2.2) =
            canonicalPositionalOnlyReference
              (parameters.val.drop index.val) call index.val cells.val
              constructionError) := by
  let expected := canonicalPositionalOnlyReference
    (parameters.val.drop index.val) call index.val cells.val constructionError
  have initialInvariant : canonicalPositionalOnlyInvariant parameters call
      expected (call, cells, index, constructionError) :=
    ⟨rfl, indexBound, capacityBound, rfl⟩
  change WP.spec _ (fun (output :
      BindCallFull.ExpandedCall String Int ×
        alloc.vec.Vec (BindCallFull.BindingCell String Int) ×
        Option (BindCallFull.BindingError String)) =>
    output.1 = call ∧ (output.2.1.val, output.2.2) = expected)
  unfold BindCallFull.canonical_environment_loop0
  apply loop.spec_decr_nat
      (measure := fun state =>
        canonicalPositionalOnlyRemaining parameters state.2.2.1)
      (inv := canonicalPositionalOnlyInvariant parameters call expected)
      (post := fun (output :
          BindCallFull.ExpandedCall String Int ×
            alloc.vec.Vec (BindCallFull.BindingCell String Int) ×
            Option (BindCallFull.BindingError String)) =>
        output.1 = call ∧ (output.2.1.val, output.2.2) = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (canonical_environment_loop0_body_preserves_reference_and_decreases
      parameters call expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem named_actual_total_clone_spec
    (actual : BindCallFull.NamedActual String Int) :
    WP.spec
      (BindCallFull.NamedActual.Insts.CoreCloneClone.clone
        (totalIdentityClone String) (totalIdentityClone Int) actual)
      (fun output => output = actual) := by
  rw [named_actual_total_clone_exact]
  simp [WP.spec, WP.theta, WP.wp_return]

def canonicalOrdinaryStep
    (parameter : BindCallFull.FormalParameter String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (absoluteIndex : Nat)
    (cells : List (BindCallFull.BindingCell String Int))
    (constructionError : Option (BindCallFull.BindingError String)) :
    List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String) :=
  match constructionError with
  | some error => (cells, some error)
  | none =>
      let argument :=
        match call.positional.val[absoluteIndex]? with
        | some actual => some (BindCallFull.BoundArgument.SuppliedPositional actual)
        | none =>
            match findNamedActualReference
                (alloc.vec.Vec.deref call.named) parameter.name with
            | some actual => some (BindCallFull.BoundArgument.SuppliedNamed actual)
            | none => parameter.default_value.map BindCallFull.BoundArgument.Defaulted
      match argument with
      | some argument =>
          (cells ++ [{
            parameter := parameter
            kind := .Positional
            argument := argument
          }], none)
      | none =>
          (cells, some (BindCallFull.BindingError.MissingRequiredArgument
            parameter.name))

def canonicalOrdinaryReference
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOffset parameterIndex : Nat)
    (cells : List (BindCallFull.BindingCell String Int))
    (constructionError : Option (BindCallFull.BindingError String)) :
    List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String) :=
  match remaining with
  | [] => (cells, constructionError)
  | parameter :: tail =>
      let next := canonicalOrdinaryStep parameter call
        (positionalOffset + parameterIndex) cells constructionError
      canonicalOrdinaryReference tail call positionalOffset
        (parameterIndex + 1) next.1 next.2
termination_by remaining.length

def canonicalOrdinaryInvariant
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (positionalOffset : Std.Usize)
    (initialCall : BindCallFull.ExpandedCall String Int)
    (expected : List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String))
    (state : BindCallFull.ExpandedCall String Int ×
      alloc.vec.Vec (BindCallFull.BindingCell String Int) × Std.Usize ×
      Option (BindCallFull.BindingError String)) : Prop :=
  state.1 = initialCall ∧
    state.2.2.1.val ≤ parameters.val.length ∧
    positionalOffset.val + parameters.val.length ≤ Std.Usize.max ∧
    state.2.1.val.length +
        (parameters.val.length - state.2.2.1.val) ≤
      BindCallFull.USIZE_CAPACITY.val ∧
    canonicalOrdinaryReference
      (parameters.val.drop state.2.2.1.val) initialCall positionalOffset.val
      state.2.2.1.val state.2.1.val state.2.2.2 = expected

def canonicalOrdinaryRemaining
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (parameterIndex : Std.Usize) : Nat :=
  parameters.val.length - parameterIndex.val

theorem canonical_environment_loop1_body_preserves_reference_and_decreases
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (positionalOffset : Std.Usize)
    (initialCall : BindCallFull.ExpandedCall String Int)
    (expected : List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String))
    (state : BindCallFull.ExpandedCall String Int ×
      alloc.vec.Vec (BindCallFull.BindingCell String Int) × Std.Usize ×
      Option (BindCallFull.BindingError String))
    (invariant : canonicalOrdinaryInvariant parameters positionalOffset
      initialCall expected state) :
    WP.spec
      (BindCallFull.canonical_environment_loop1.body
        (totalIdentityClone String) (totalIdentityClone Int)
        parameters positionalOffset state.1 state.2.1 state.2.2.1
        state.2.2.2)
      (fun flow =>
        match flow with
        | .done output =>
            output.1 = initialCall ∧
              (output.2.1.val, output.2.2) = expected
        | .cont next =>
            canonicalOrdinaryInvariant parameters positionalOffset initialCall
                expected next ∧
              canonicalOrdinaryRemaining parameters next.2.2.1 <
                canonicalOrdinaryRemaining parameters state.2.2.1) := by
  rcases state with ⟨call, cells, parameterIndex, constructionError⟩
  unfold BindCallFull.canonical_environment_loop1.body
  unfold canonicalOrdinaryInvariant at invariant
  unfold canonicalOrdinaryInvariant canonicalOrdinaryRemaining
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  rw [invariant.1]
  by_cases indexWithin : parameterIndex < alloc.vec.Vec.len parameters
  · simp only [indexWithin, if_true]
    have parameterBound : parameterIndex.val < parameters.val.length := by
      simpa using indexWithin
    step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
      exact parameterBound
    step with Std.Usize.add_spec as ⟨absoluteIndex, absoluteIndexEq⟩ by
      omega
    cases constructionError with
    | some error =>
        simp only [Option.isNone, Bool.false_eq_true, if_false]
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have parameterMachineBound := parameters.property
          omega
        have parameterDrop : parameters.val.drop parameterIndex.val =
            parameters.val[parameterIndex.val] ::
              parameters.val.drop (parameterIndex.val + 1) :=
          List.drop_eq_getElem_cons parameterBound
        have referenceStep := invariant.2.2.2.2
        rw [parameterDrop] at referenceStep
        rw [canonicalOrdinaryReference.eq_2] at referenceStep
        rw [← parameterEq] at referenceStep
        simp only [canonicalOrdinaryStep] at referenceStep
        simp only [nextIndexEq]
        exact ⟨by omega, invariant.2.2.1, by omega, referenceStep, by omega⟩
    | none =>
        simp only [Option.isNone, if_true]
        simp only [core.slice.Slice.get, core.slice.index.Usize.get]
        cases positionalEq :
            (initialCall.positional.val)[absoluteIndex.val]? with
        | some positionalActual =>
            simp only [alloc.vec.Vec.deref, Slice.getElem?_Usize_eq,
              positionalEq, bind_ok, positional_actual_total_clone_exact,
              formal_parameter_total_clone_exact]
            step with alloc.vec.Vec.push_spec as ⟨nextCells, pushEq⟩ by
              have maximumFits : BindCallFull.USIZE_CAPACITY.val <
                  Std.Usize.max := by simp [BindCallFull.USIZE_CAPACITY]
              omega
            step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
              have parameterMachineBound := parameters.property
              omega
            have parameterDrop : parameters.val.drop parameterIndex.val =
                parameters.val[parameterIndex.val] ::
                  parameters.val.drop (parameterIndex.val + 1) :=
              List.drop_eq_getElem_cons parameterBound
            have referenceStep := invariant.2.2.2.2
            rw [parameterDrop] at referenceStep
            rw [canonicalOrdinaryReference.eq_2] at referenceStep
            rw [← parameterEq] at referenceStep
            have positionalInput :
                (initialCall.positional.val)[positionalOffset.val +
                    parameterIndex.val]? = some positionalActual := by
              simpa [absoluteIndexEq] using positionalEq
            simp only [canonicalOrdinaryStep, positionalInput] at referenceStep
            simp only [pushEq, nextIndexEq, List.length_append,
              List.length_singleton]
            exact ⟨by omega, invariant.2.2.1, by omega, referenceStep, by omega⟩
        | none =>
            simp only [alloc.vec.Vec.deref, Slice.getElem?_Usize_eq,
              positionalEq, bind_ok]
            step with find_named_actual_matches_reference as
              ⟨namedActual, namedActualEq⟩
            cases namedEq : findNamedActualReference
                (alloc.vec.Vec.deref initialCall.named) parameter.name with
            | some actual =>
                have namedActualValue : namedActual = some actual := by
                  rw [namedActualEq]
                  exact namedEq
                simp only [namedActualValue, bind_ok,
                  named_actual_total_clone_exact,
                  formal_parameter_total_clone_exact]
                step with alloc.vec.Vec.push_spec as ⟨nextCells, pushEq⟩ by
                  have maximumFits : BindCallFull.USIZE_CAPACITY.val <
                      Std.Usize.max := by
                    simp [BindCallFull.USIZE_CAPACITY]
                  omega
                step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
                  have parameterMachineBound := parameters.property
                  omega
                have parameterDrop : parameters.val.drop parameterIndex.val =
                    parameters.val[parameterIndex.val] ::
                      parameters.val.drop (parameterIndex.val + 1) :=
                  List.drop_eq_getElem_cons parameterBound
                have referenceStep := invariant.2.2.2.2
                rw [parameterDrop] at referenceStep
                rw [canonicalOrdinaryReference.eq_2] at referenceStep
                rw [← parameterEq] at referenceStep
                have positionalInput :
                    (initialCall.positional.val)[positionalOffset.val +
                        parameterIndex.val]? = none := by
                  simpa [absoluteIndexEq] using positionalEq
                simp only [canonicalOrdinaryStep, positionalInput, namedEq]
                  at referenceStep
                simp only [pushEq, nextIndexEq, List.length_append,
                  List.length_singleton]
                exact ⟨by omega, invariant.2.2.1, by omega, referenceStep,
                  by omega⟩
            | none =>
                have namedActualValue : namedActual = none := by
                  rw [namedActualEq]
                  exact namedEq
                simp only [namedActualValue, bind_ok]
                cases defaultEq : parameter.default_value with
                | none =>
                    simp only [defaultEq, bind_ok, string_clone_exact]
                    step with Std.Usize.add_spec as
                      ⟨nextIndex, nextIndexEq⟩ by
                      have parameterMachineBound := parameters.property
                      omega
                    have parameterDrop :
                        parameters.val.drop parameterIndex.val =
                          parameters.val[parameterIndex.val] ::
                            parameters.val.drop (parameterIndex.val + 1) :=
                      List.drop_eq_getElem_cons parameterBound
                    have referenceStep := invariant.2.2.2.2
                    rw [parameterDrop] at referenceStep
                    rw [canonicalOrdinaryReference.eq_2] at referenceStep
                    rw [← parameterEq] at referenceStep
                    have positionalInput :
                        (initialCall.positional.val)[positionalOffset.val +
                            parameterIndex.val]? = none := by
                      simpa [absoluteIndexEq] using positionalEq
                    simp only [canonicalOrdinaryStep, positionalInput, namedEq,
                      defaultEq, Option.map] at referenceStep
                    simp only [nextIndexEq]
                    exact ⟨by omega, invariant.2.2.1, by omega,
                      referenceStep, by omega⟩
                | some defaultValue =>
                    simp only [defaultEq, bind_ok,
                      typed_value_total_clone_exact,
                      formal_parameter_total_clone_exact]
                    have parameterRebuild :
                        ({ parameter with default_value := some defaultValue } :
                          BindCallFull.FormalParameter String Int) =
                          parameter := by
                      rcases parameter with ⟨parameterName, expectedType,
                        parameterDefault⟩
                      simp_all
                    step with alloc.vec.Vec.push_spec as
                      ⟨nextCells, pushEq⟩ by
                      have maximumFits :
                          BindCallFull.USIZE_CAPACITY.val <
                            Std.Usize.max := by
                        simp [BindCallFull.USIZE_CAPACITY]
                      omega
                    step with Std.Usize.add_spec as
                      ⟨nextIndex, nextIndexEq⟩ by
                      have parameterMachineBound := parameters.property
                      omega
                    have parameterDrop :
                        parameters.val.drop parameterIndex.val =
                          parameters.val[parameterIndex.val] ::
                            parameters.val.drop (parameterIndex.val + 1) :=
                      List.drop_eq_getElem_cons parameterBound
                    have referenceStep := invariant.2.2.2.2
                    rw [parameterDrop] at referenceStep
                    rw [canonicalOrdinaryReference.eq_2] at referenceStep
                    rw [← parameterEq] at referenceStep
                    have positionalInput :
                        (initialCall.positional.val)[positionalOffset.val +
                            parameterIndex.val]? = none := by
                      simpa [absoluteIndexEq] using positionalEq
                    simp only [canonicalOrdinaryStep, positionalInput, namedEq,
                      defaultEq, Option.map] at referenceStep
                    simp only [parameterRebuild, pushEq, nextIndexEq,
                      List.length_append, List.length_singleton]
                    exact ⟨by omega, invariant.2.2.1, by omega,
                      referenceStep, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : parameters.val.length ≤ parameterIndex.val := by
      simpa using indexWithin
    have atEnd : parameterIndex.val = parameters.val.length := by omega
    have referenceEq := invariant.2.2.2.2
    rw [atEnd] at referenceEq
    simp [canonicalOrdinaryReference] at referenceEq
    exact ⟨rfl, referenceEq⟩

theorem canonical_environment_loop1_matches_reference
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (positionalOffset : Std.Usize)
    (call : BindCallFull.ExpandedCall String Int)
    (cells : alloc.vec.Vec (BindCallFull.BindingCell String Int))
    (parameterIndex : Std.Usize)
    (constructionError : Option (BindCallFull.BindingError String))
    (indexBound : parameterIndex.val ≤ parameters.val.length)
    (offsetBound : positionalOffset.val + parameters.val.length ≤
      Std.Usize.max)
    (capacityBound : cells.val.length +
        (parameters.val.length - parameterIndex.val) ≤
      BindCallFull.USIZE_CAPACITY.val) :
    WP.spec
      (BindCallFull.canonical_environment_loop1
        (totalIdentityClone String) (totalIdentityClone Int)
        parameters call cells positionalOffset parameterIndex constructionError)
      (fun output =>
        output.1 = call ∧
          (output.2.1.val, output.2.2) =
            canonicalOrdinaryReference
              (parameters.val.drop parameterIndex.val) call
              positionalOffset.val parameterIndex.val cells.val
              constructionError) := by
  let expected := canonicalOrdinaryReference
    (parameters.val.drop parameterIndex.val) call positionalOffset.val
    parameterIndex.val cells.val constructionError
  have initialInvariant : canonicalOrdinaryInvariant parameters
      positionalOffset call expected
      (call, cells, parameterIndex, constructionError) :=
    ⟨rfl, indexBound, offsetBound, capacityBound, rfl⟩
  change WP.spec _ (fun (output :
      BindCallFull.ExpandedCall String Int ×
        alloc.vec.Vec (BindCallFull.BindingCell String Int) ×
        Option (BindCallFull.BindingError String)) =>
    output.1 = call ∧ (output.2.1.val, output.2.2) = expected)
  unfold BindCallFull.canonical_environment_loop1
  apply loop.spec_decr_nat
      (measure := fun state =>
        canonicalOrdinaryRemaining parameters state.2.2.1)
      (inv := canonicalOrdinaryInvariant parameters positionalOffset call
        expected)
      (post := fun (output :
          BindCallFull.ExpandedCall String Int ×
            alloc.vec.Vec (BindCallFull.BindingCell String Int) ×
            Option (BindCallFull.BindingError String)) =>
        output.1 = call ∧ (output.2.1.val, output.2.2) = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (canonical_environment_loop1_body_preserves_reference_and_decreases
      parameters positionalOffset call expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

def canonicalKeywordOnlyStep
    (parameter : BindCallFull.FormalParameter String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (cells : List (BindCallFull.BindingCell String Int))
    (constructionError : Option (BindCallFull.BindingError String)) :
    List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String) :=
  match constructionError with
  | some error => (cells, some error)
  | none =>
      let argument :=
        match findNamedActualReference
            (alloc.vec.Vec.deref call.named) parameter.name with
        | some actual => some (BindCallFull.BoundArgument.SuppliedNamed actual)
        | none => parameter.default_value.map BindCallFull.BoundArgument.Defaulted
      match argument with
      | some argument =>
          (cells ++ [{
            parameter := parameter
            kind := .KeywordOnly
            argument := argument
          }], none)
      | none =>
          (cells, some (BindCallFull.BindingError.MissingRequiredArgument
            parameter.name))

def canonicalKeywordOnlyReference
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (cells : List (BindCallFull.BindingCell String Int))
    (constructionError : Option (BindCallFull.BindingError String)) :
    List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String) :=
  match remaining with
  | [] => (cells, constructionError)
  | parameter :: tail =>
      let next := canonicalKeywordOnlyStep parameter call cells constructionError
      canonicalKeywordOnlyReference tail call next.1 next.2
termination_by remaining.length

def canonicalKeywordOnlyInvariant
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (initialCall : BindCallFull.ExpandedCall String Int)
    (expected : List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String))
    (state : BindCallFull.ExpandedCall String Int ×
      alloc.vec.Vec (BindCallFull.BindingCell String Int) × Std.Usize ×
      Option (BindCallFull.BindingError String)) : Prop :=
  state.1 = initialCall ∧
    state.2.2.1.val ≤ parameters.val.length ∧
    state.2.1.val.length +
        (parameters.val.length - state.2.2.1.val) ≤
      BindCallFull.USIZE_CAPACITY.val ∧
    canonicalKeywordOnlyReference
      (parameters.val.drop state.2.2.1.val) initialCall state.2.1.val
      state.2.2.2 = expected

def canonicalKeywordOnlyRemaining
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (keywordIndex : Std.Usize) : Nat :=
  parameters.val.length - keywordIndex.val

theorem canonical_environment_loop2_body_preserves_reference_and_decreases
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (initialCall : BindCallFull.ExpandedCall String Int)
    (expected : List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String))
    (state : BindCallFull.ExpandedCall String Int ×
      alloc.vec.Vec (BindCallFull.BindingCell String Int) × Std.Usize ×
      Option (BindCallFull.BindingError String))
    (invariant : canonicalKeywordOnlyInvariant parameters initialCall expected
      state) :
    WP.spec
      (BindCallFull.canonical_environment_loop2.body
        (totalIdentityClone String) (totalIdentityClone Int)
        parameters state.1 state.2.1 state.2.2.1 state.2.2.2)
      (fun flow =>
        match flow with
        | .done output =>
            output.1 = initialCall ∧
              (output.2.1.val, output.2.2) = expected
        | .cont next =>
            canonicalKeywordOnlyInvariant parameters initialCall expected
                next ∧
              canonicalKeywordOnlyRemaining parameters next.2.2.1 <
                canonicalKeywordOnlyRemaining parameters state.2.2.1) := by
  rcases state with ⟨call, cells, keywordIndex, constructionError⟩
  unfold BindCallFull.canonical_environment_loop2.body
  unfold canonicalKeywordOnlyInvariant at invariant
  unfold canonicalKeywordOnlyInvariant canonicalKeywordOnlyRemaining
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  rw [invariant.1]
  by_cases indexWithin : keywordIndex < alloc.vec.Vec.len parameters
  · simp only [indexWithin, if_true]
    have parameterBound : keywordIndex.val < parameters.val.length := by
      simpa using indexWithin
    step with alloc.vec.Vec.index_usize_spec as ⟨parameter, parameterEq⟩ by
      exact parameterBound
    cases constructionError with
    | some error =>
        simp only [Option.isNone, Bool.false_eq_true, if_false]
        step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
          have parameterMachineBound := parameters.property
          omega
        have parameterDrop : parameters.val.drop keywordIndex.val =
            parameters.val[keywordIndex.val] ::
              parameters.val.drop (keywordIndex.val + 1) :=
          List.drop_eq_getElem_cons parameterBound
        have referenceStep := invariant.2.2.2
        rw [parameterDrop] at referenceStep
        rw [canonicalKeywordOnlyReference.eq_2] at referenceStep
        rw [← parameterEq] at referenceStep
        simp only [canonicalKeywordOnlyStep] at referenceStep
        simp only [nextIndexEq]
        exact ⟨by omega, by omega, referenceStep, by omega⟩
    | none =>
        simp only [Option.isNone, if_true, alloc.vec.Vec.deref]
        step with find_named_actual_matches_reference as
          ⟨namedActual, namedActualEq⟩
        cases namedEq : findNamedActualReference
            (alloc.vec.Vec.deref initialCall.named) parameter.name with
        | some actual =>
            have namedActualValue : namedActual = some actual := by
              rw [namedActualEq]
              exact namedEq
            have parameterIdentity :
                ({ parameter with default_value := parameter.default_value } :
                  BindCallFull.FormalParameter String Int) = parameter := by
              rcases parameter with ⟨parameterName, expectedType,
                parameterDefault⟩
              rfl
            simp only [namedActualValue, bind_ok,
              named_actual_total_clone_exact, parameterIdentity,
              formal_parameter_total_clone_exact]
            step with alloc.vec.Vec.push_spec as ⟨nextCells, pushEq⟩ by
              have maximumFits : BindCallFull.USIZE_CAPACITY.val <
                  Std.Usize.max := by simp [BindCallFull.USIZE_CAPACITY]
              omega
            step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
              have parameterMachineBound := parameters.property
              omega
            have parameterDrop : parameters.val.drop keywordIndex.val =
                parameters.val[keywordIndex.val] ::
                  parameters.val.drop (keywordIndex.val + 1) :=
              List.drop_eq_getElem_cons parameterBound
            have referenceStep := invariant.2.2.2
            rw [parameterDrop] at referenceStep
            rw [canonicalKeywordOnlyReference.eq_2] at referenceStep
            rw [← parameterEq] at referenceStep
            simp only [canonicalKeywordOnlyStep, namedEq] at referenceStep
            simp only [pushEq, nextIndexEq, List.length_append,
              List.length_singleton]
            exact ⟨by omega, by omega, referenceStep, by omega⟩
        | none =>
            have namedActualValue : namedActual = none := by
              rw [namedActualEq]
              exact namedEq
            simp only [namedActualValue, bind_ok]
            cases defaultEq : parameter.default_value with
            | none =>
                simp only [defaultEq, bind_ok, string_clone_exact]
                step with Std.Usize.add_spec as
                  ⟨nextIndex, nextIndexEq⟩ by
                  have parameterMachineBound := parameters.property
                  omega
                have parameterDrop : parameters.val.drop keywordIndex.val =
                    parameters.val[keywordIndex.val] ::
                      parameters.val.drop (keywordIndex.val + 1) :=
                  List.drop_eq_getElem_cons parameterBound
                have referenceStep := invariant.2.2.2
                rw [parameterDrop] at referenceStep
                rw [canonicalKeywordOnlyReference.eq_2] at referenceStep
                rw [← parameterEq] at referenceStep
                simp only [canonicalKeywordOnlyStep, namedEq, defaultEq,
                  Option.map] at referenceStep
                simp only [nextIndexEq]
                exact ⟨by omega, by omega, referenceStep, by omega⟩
            | some defaultValue =>
                simp only [defaultEq, bind_ok, typed_value_total_clone_exact]
                have parameterRebuild :
                    ({ parameter with default_value := some defaultValue } :
                      BindCallFull.FormalParameter String Int) = parameter := by
                  rcases parameter with ⟨parameterName, expectedType,
                    parameterDefault⟩
                  simp_all
                simp only [parameterRebuild,
                  formal_parameter_total_clone_exact]
                step with alloc.vec.Vec.push_spec as
                  ⟨nextCells, pushEq⟩ by
                  have maximumFits :
                      BindCallFull.USIZE_CAPACITY.val <
                        Std.Usize.max := by
                    simp [BindCallFull.USIZE_CAPACITY]
                  omega
                step with Std.Usize.add_spec as
                  ⟨nextIndex, nextIndexEq⟩ by
                  have parameterMachineBound := parameters.property
                  omega
                have parameterDrop : parameters.val.drop keywordIndex.val =
                    parameters.val[keywordIndex.val] ::
                      parameters.val.drop (keywordIndex.val + 1) :=
                  List.drop_eq_getElem_cons parameterBound
                have referenceStep := invariant.2.2.2
                rw [parameterDrop] at referenceStep
                rw [canonicalKeywordOnlyReference.eq_2] at referenceStep
                rw [← parameterEq] at referenceStep
                simp only [canonicalKeywordOnlyStep, namedEq, defaultEq,
                  Option.map] at referenceStep
                simp only [parameterRebuild, pushEq, nextIndexEq,
                  List.length_append, List.length_singleton]
                exact ⟨by omega, by omega, referenceStep, by omega⟩
  · simp only [indexWithin, if_false]
    have exhausted : parameters.val.length ≤ keywordIndex.val := by
      simpa using indexWithin
    have atEnd : keywordIndex.val = parameters.val.length := by omega
    have referenceEq := invariant.2.2.2
    rw [atEnd] at referenceEq
    simp [canonicalKeywordOnlyReference] at referenceEq
    exact ⟨rfl, referenceEq⟩

theorem canonical_environment_loop2_matches_reference
    (parameters : alloc.vec.Vec (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (cells : alloc.vec.Vec (BindCallFull.BindingCell String Int))
    (keywordIndex : Std.Usize)
    (constructionError : Option (BindCallFull.BindingError String))
    (indexBound : keywordIndex.val ≤ parameters.val.length)
    (capacityBound : cells.val.length +
        (parameters.val.length - keywordIndex.val) ≤
      BindCallFull.USIZE_CAPACITY.val) :
    WP.spec
      (BindCallFull.canonical_environment_loop2
        (totalIdentityClone String) (totalIdentityClone Int)
        parameters call cells keywordIndex constructionError)
      (fun output =>
        output.1 = call ∧
          (output.2.1.val, output.2.2) =
            canonicalKeywordOnlyReference
              (parameters.val.drop keywordIndex.val) call cells.val
              constructionError) := by
  let expected := canonicalKeywordOnlyReference
    (parameters.val.drop keywordIndex.val) call cells.val constructionError
  have initialInvariant : canonicalKeywordOnlyInvariant parameters call expected
      (call, cells, keywordIndex, constructionError) :=
    ⟨rfl, indexBound, capacityBound, rfl⟩
  change WP.spec _ (fun (output :
      BindCallFull.ExpandedCall String Int ×
        alloc.vec.Vec (BindCallFull.BindingCell String Int) ×
        Option (BindCallFull.BindingError String)) =>
    output.1 = call ∧ (output.2.1.val, output.2.2) = expected)
  unfold BindCallFull.canonical_environment_loop2
  apply loop.spec_decr_nat
      (measure := fun state =>
        canonicalKeywordOnlyRemaining parameters state.2.2.1)
      (inv := canonicalKeywordOnlyInvariant parameters call expected)
      (post := fun (output :
          BindCallFull.ExpandedCall String Int ×
            alloc.vec.Vec (BindCallFull.BindingCell String Int) ×
            Option (BindCallFull.BindingError String)) =>
        output.1 = call ∧ (output.2.1.val, output.2.2) = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (canonical_environment_loop2_body_preserves_reference_and_decreases
      parameters call expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

def outerActualContribution
    (item : BindCallFull.ActualItem String Int) : Nat :=
  match item with
  | .Positional _ => 1
  | .Named _ _ => 1
  | .FixedStar values => values.val.length
  | .DynamicStar => 0
  | .KeywordMapping => 0

def outerRemainingContribution
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter (BindCallFull.ActualItem String Int))) : Nat :=
  ((iter.iter.slice.val.drop iter.iter.i).map outerActualContribution).sum

@[step]
theorem outer_enumerate_actual_next_preserves_contribution
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter (BindCallFull.ActualItem String Int)))
    (indexBound : iter.iter.i ≤ iter.iter.slice.val.length)
    (countBound : iter.count.val = iter.iter.i) :
    WP.spec
      (core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter
          (BindCallFull.ActualItem String Int)) iter)
      (fun result =>
        match result.1 with
        | none =>
            result.2 = iter ∧ outerRemainingContribution iter = 0 ∧
              preflightRemaining iter = 0
        | some (index, item) =>
            index.val = iter.iter.i ∧
              iter.iter.slice.val[iter.iter.i]? = some item ∧
              outerRemainingContribution result.2 +
                  outerActualContribution item =
                outerRemainingContribution iter ∧
              preflightRemaining result.2 + 1 = preflightRemaining iter ∧
              result.2.iter.slice = iter.iter.slice ∧
              result.2.iter.i = iter.iter.i + 1 ∧
              result.2.iter.i ≤ result.2.iter.slice.val.length ∧
              result.2.count.val = result.2.iter.i) := by
  simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorSliceIter.next, outerRemainingContribution,
    outerActualContribution, preflightRemaining]
  split
  case isTrue itemAvailable =>
    step
    constructor
    · exact countBound
    constructor
    · exact List.getElem?_eq_getElem itemAvailable
    constructor
    · have mappedIndexBound : iter.iter.i <
          (iter.iter.slice.val.map outerActualContribution).length := by
        simp_all
      have itemEq := Slice.getElem_Nat_eq
        iter.iter.slice iter.iter.i (by omega)
      generalize hItem : iter.iter.slice[iter.iter.i] = item
      cases item <;>
        simp_all only [List.drop_eq_getElem_cons mappedIndexBound,
          List.sum_cons, List.getElem_map, outerActualContribution]
      all_goals rw [← itemEq]
      all_goals simp [Nat.add_comm, outerActualContribution]
    · omega
  case isFalse exhausted => simp_all

structure NamedActualView where
  «name» : String
  value : BindCallFull.TypedValue String Int
  evaluationPosition : EvaluationPositionView

inductive EvaluationEventView where
  | receiver
  | positional (itemIndex : Nat)
  | named (itemIndex : Nat) (argumentName : String)
  | fixedStar (itemIndex elementCount : Nat)

inductive OuterExpansionErrorView where
  | dynamicStarUnsupported (itemIndex : Nat)
  | keywordMappingUnsupported (itemIndex : Nat)
  | other (error : BindCallFull.BindingError String)

structure ExpansionBuffersView where
  positional : List PositionalActualView
  named : List NamedActualView
  evaluationOrder : List EvaluationEventView
  error : Option OuterExpansionErrorView

def namedActualView
    (actual : BindCallFull.NamedActual String Int) : NamedActualView := {
  «name» := actual.name
  value := actual.value
  evaluationPosition := evaluationPositionView actual.evaluation_position
}

def evaluationEventView :
    BindCallFull.EvaluationEvent → EvaluationEventView
  | .Receiver => .receiver
  | .Positional itemIndex => .positional itemIndex.val
  | .Named itemIndex argumentName => .named itemIndex.val argumentName
  | .FixedStar itemIndex elementCount =>
      .fixedStar itemIndex.val elementCount.val

def outerExpansionErrorView
    (error : BindCallFull.BindingError String) : OuterExpansionErrorView :=
  match error with
  | .DynamicStarUnsupported itemIndex =>
      .dynamicStarUnsupported itemIndex.val
  | .KeywordMappingUnsupported itemIndex =>
      .keywordMappingUnsupported itemIndex.val
  | other => .other other

def expansionBuffersView
    (positional : alloc.vec.Vec
      (BindCallFull.PositionalActual String Int))
    (named : alloc.vec.Vec (BindCallFull.NamedActual String Int))
    (evaluationOrder : alloc.vec.Vec BindCallFull.EvaluationEvent)
    (error : Option (BindCallFull.BindingError String)) :
    ExpansionBuffersView := {
  positional := positional.val.map positionalActualView
  named := named.val.map namedActualView
  evaluationOrder := evaluationOrder.val.map evaluationEventView
  error := error.map outerExpansionErrorView
}

def outerExpansionStep
    (itemIndex : Nat)
    (item : BindCallFull.ActualItem String Int)
    (state : ExpansionBuffersView) : ExpansionBuffersView :=
  match state.error with
  | some _ => state
  | none =>
      match item with
      | .Positional value => {
          state with
          positional := state.positional ++ [{
            value := value
            origin := .Explicit
            evaluationPosition := .actual itemIndex 0
          }]
          evaluationOrder := state.evaluationOrder ++ [.positional itemIndex]
        }
      | .Named argumentName value => {
          state with
          named := state.named ++ [{
            «name» := argumentName
            value := value
            evaluationPosition := .actual itemIndex 0
          }]
          evaluationOrder := state.evaluationOrder ++
            [.named itemIndex argumentName]
        }
      | .FixedStar values => {
          state with
          positional := state.positional ++
            fixedStarViewsFrom itemIndex 0 values.val
          evaluationOrder := state.evaluationOrder ++
            [.fixedStar itemIndex values.val.length]
        }
      | .DynamicStar => {
          state with error := some (.dynamicStarUnsupported itemIndex)
        }
      | .KeywordMapping => {
          state with error := some (.keywordMappingUnsupported itemIndex)
        }

def outerExpansionReference
    (itemIndex : Nat)
    (remaining : List (BindCallFull.ActualItem String Int))
    (state : ExpansionBuffersView) : ExpansionBuffersView :=
  match remaining with
  | [] => state
  | item :: tail =>
      match state.error with
      | some _ => state
      | none =>
          outerExpansionReference (itemIndex + 1) tail
            (outerExpansionStep itemIndex item state)
termination_by remaining.length

@[simp]
theorem outerExpansionReference_some_error
    (itemIndex : Nat)
    (remaining : List (BindCallFull.ActualItem String Int))
    (positional : List PositionalActualView)
    (named : List NamedActualView)
    (evaluationOrder : List EvaluationEventView)
    (error : OuterExpansionErrorView) :
    outerExpansionReference itemIndex remaining {
      positional := positional
      named := named
      evaluationOrder := evaluationOrder
      error := some error
    } = {
      positional := positional
      named := named
      evaluationOrder := evaluationOrder
      error := some error
    } := by
  cases remaining <;> simp [outerExpansionReference]

structure OuterExpansionInvariant
    (sourceItems : List (BindCallFull.ActualItem String Int))
    (expected : ExpansionBuffersView)
    (state : core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter (BindCallFull.ActualItem String Int)) ×
      alloc.vec.Vec (BindCallFull.PositionalActual String Int) ×
      alloc.vec.Vec (BindCallFull.NamedActual String Int) ×
      alloc.vec.Vec BindCallFull.EvaluationEvent ×
      Option (BindCallFull.BindingError String)) : Prop where
  iterator : preflightIteratorInvariant state.1
  source : state.1.iter.slice.val = sourceItems
  positionalNamedCapacity :
    state.2.1.val.length + state.2.2.1.val.length +
      outerRemainingContribution state.1 ≤
        BindCallFull.USIZE_CAPACITY.val
  evaluationCapacity :
    state.2.2.2.1.val.length + preflightRemaining state.1 ≤
      BindCallFull.USIZE_CAPACITY.val
  reference :
    outerExpansionReference state.1.iter.i
      (sourceItems.drop state.1.iter.i)
      (expansionBuffersView state.2.1 state.2.2.1 state.2.2.2.1
        state.2.2.2.2) = expected

theorem expand_actual_items_outer_loop_body_preserves_reference_and_decreases
    (sourceItems : List (BindCallFull.ActualItem String Int))
    (expected : ExpansionBuffersView)
    (state : core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter (BindCallFull.ActualItem String Int)) ×
      alloc.vec.Vec (BindCallFull.PositionalActual String Int) ×
      alloc.vec.Vec (BindCallFull.NamedActual String Int) ×
      alloc.vec.Vec BindCallFull.EvaluationEvent ×
      Option (BindCallFull.BindingError String))
    (invariant : OuterExpansionInvariant sourceItems expected state) :
    WP.spec
      (BindCallFull.expand_actual_items_with_allocator_loop0.body
        (totalIdentityClone String) (totalIdentityClone Int)
        state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2)
      (fun flow =>
        match flow with
        | .done output =>
            expansionBuffersView output.1 output.2.1 output.2.2.1
              output.2.2.2 = expected
        | .cont next =>
            OuterExpansionInvariant sourceItems expected next ∧
              preflightRemaining next.1 < preflightRemaining state.1) := by
  rcases state with
    ⟨iter, positional, named, evaluationOrder, expansionError⟩
  have iteratorInvariant := invariant.iterator
  have sourceEq := invariant.source
  have positionalNamedCapacity := invariant.positionalNamedCapacity
  have evaluationCapacity := invariant.evaluationCapacity
  have referenceEq := invariant.reference
  change preflightIteratorInvariant iter at iteratorInvariant
  change iter.iter.slice.val = sourceItems at sourceEq
  change positional.val.length + named.val.length +
      outerRemainingContribution iter ≤
    BindCallFull.USIZE_CAPACITY.val at positionalNamedCapacity
  change evaluationOrder.val.length + preflightRemaining iter ≤
    BindCallFull.USIZE_CAPACITY.val at evaluationCapacity
  change outerExpansionReference iter.iter.i
      (sourceItems.drop iter.iter.i)
      (expansionBuffersView positional named evaluationOrder expansionError) =
    expected at referenceEq
  unfold BindCallFull.expand_actual_items_with_allocator_loop0.body
  unfold preflightIteratorInvariant at iteratorInvariant
  step with outer_enumerate_actual_next_preserves_contribution
  cases o with
  | none =>
      rcases o_post with
        ⟨sameState, noContribution, noRemaining⟩
      have exhausted : sourceItems.length ≤ iter.iter.i := by
        unfold preflightRemaining at noRemaining
        rw [sourceEq] at noRemaining
        exact Nat.sub_eq_zero_iff_le.mp noRemaining
      have dropped : sourceItems.drop iter.iter.i = [] :=
        List.drop_eq_nil_iff.mpr exhausted
      simpa [expansionBuffersView, outerExpansionReference, dropped]
        using referenceEq
  | some pair =>
      rcases pair with ⟨itemIndex, item⟩
      rcases o_post with
        ⟨returnedIndex, itemAt, contributionStep, exactDecrease, sameSlice,
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
      cases expansionError with
      | some error =>
          simp only [Option.isNone, Bool.false_eq_true, if_false]
          constructor
          · refine {
              iterator := ?_, source := ?_, positionalNamedCapacity := ?_,
              evaluationCapacity := ?_, reference := ?_
            }
            · unfold preflightIteratorInvariant
              exact ⟨nextIndexBound, nextCountBound⟩
            · rw [sameSlice]
              exact sourceEq
            · change positional.val.length + named.val.length +
                  outerRemainingContribution iter1 ≤
                BindCallFull.USIZE_CAPACITY.val
              omega
            · change evaluationOrder.val.length +
                  preflightRemaining iter1 ≤
                BindCallFull.USIZE_CAPACITY.val
              omega
            · simpa [dropStep, outerExpansionReference,
                expansionBuffersView] using referenceEq
          · change preflightRemaining iter1 < preflightRemaining iter
            omega
      | none =>
          simp only [Option.isNone, if_true]
          cases item with
          | Positional value =>
              simp only [typed_value_total_clone_exact]
              step with alloc.vec.Vec.push_spec as
                ⟨nextEvaluationOrder, evaluationPushEq⟩ by omega
              step with alloc.vec.Vec.push_spec as
                ⟨nextPositional, positionalPushEq⟩ by
                  simp [BindCallFull.USIZE_CAPACITY,
                    outerActualContribution] at positionalNamedCapacity contributionStep
                  omega
              constructor
              · refine {
                  iterator := ?_, source := ?_, positionalNamedCapacity := ?_,
                  evaluationCapacity := ?_, reference := ?_
                }
                · unfold preflightIteratorInvariant
                  exact ⟨nextIndexBound, nextCountBound⟩
                · rw [sameSlice]
                  exact sourceEq
                · simp only [outerActualContribution] at contributionStep
                  simp [positionalPushEq]
                  omega
                · simp [evaluationPushEq]
                  omega
                · rw [dropStep] at referenceEq
                  simpa [outerExpansionReference, outerExpansionStep,
                    expansionBuffersView, positionalActualView,
                    evaluationPositionView, evaluationEventView,
                    positionalPushEq, evaluationPushEq,
                    returnedIndex, nextIndex, List.map_append] using referenceEq
              · change preflightRemaining iter1 < preflightRemaining iter
                omega
          | Named argumentName value =>
              simp only [Prod.rec, string_clone_exact]
              step with alloc.vec.Vec.push_spec as
                ⟨nextEvaluationOrder, evaluationPushEq⟩ by omega
              step with typed_value_total_clone_spec as
                ⟨clonedValue, valueCloneEq⟩
              step with alloc.vec.Vec.push_spec as
                ⟨nextNamed, namedPushEq⟩ by
                  simp [BindCallFull.USIZE_CAPACITY,
                    outerActualContribution] at positionalNamedCapacity contributionStep
                  omega
              constructor
              · refine {
                  iterator := ?_, source := ?_, positionalNamedCapacity := ?_,
                  evaluationCapacity := ?_, reference := ?_
                }
                · unfold preflightIteratorInvariant
                  exact ⟨nextIndexBound, nextCountBound⟩
                · rw [sameSlice]
                  exact sourceEq
                · simp only [outerActualContribution] at contributionStep
                  simp [namedPushEq]
                  omega
                · simp [evaluationPushEq]
                  omega
                · rw [dropStep] at referenceEq
                  simpa [outerExpansionReference, outerExpansionStep,
                    expansionBuffersView, namedActualView,
                    evaluationPositionView, evaluationEventView, namedPushEq,
                    evaluationPushEq, valueCloneEq, returnedIndex, nextIndex,
                    List.map_append] using referenceEq
              · change preflightRemaining iter1 < preflightRemaining iter
                omega
          | FixedStar values =>
              simp only [alloc.vec.Vec.len]
              step with alloc.vec.Vec.push_spec as
                ⟨nextEvaluationOrder, evaluationPushEq⟩ by omega
              simp [core.slice.Slice.iter]
              step
              have fixedInvariant : fixedStarRecordInvariant itemIndex
                  (positional.val.map positionalActualView) values.val
                  (iter2, positional) := by
                unfold fixedStarRecordInvariant
                refine ⟨?_, ?_, ?_, ?_⟩
                · unfold preflightIteratorInvariant
                  rw [iter2_post1, iter2_post2]
                  simp
                · rw [iter2_post1]
                  simp [alloc.vec.Vec.deref]
                · unfold preflightRemaining
                  rw [iter2_post1]
                  simp [alloc.vec.Vec.deref]
                  simp only [outerActualContribution] at contributionStep
                  omega
                · rw [iter2_post1]
                  simp [fixedStarViewsFrom]
              step with expand_actual_items_fixed_star_loop_matches_reference
                as ⟨nextPositional, nextPositionalViews⟩ by
                  exact fixedInvariant
              have nextPositionalLength : nextPositional.val.length =
                  positional.val.length + values.val.length := by
                have viewLengths := congrArg List.length nextPositionalViews
                simpa using viewLengths
              constructor
              · refine {
                  iterator := ?_, source := ?_, positionalNamedCapacity := ?_,
                  evaluationCapacity := ?_, reference := ?_
                }
                · unfold preflightIteratorInvariant
                  exact ⟨nextIndexBound, nextCountBound⟩
                · rw [sameSlice]
                  exact sourceEq
                · simp only [outerActualContribution] at contributionStep
                  change nextPositional.val.length + named.val.length +
                      outerRemainingContribution iter1 ≤
                    BindCallFull.USIZE_CAPACITY.val
                  rw [nextPositionalLength]
                  omega
                · simp [evaluationPushEq]
                  omega
                · rw [dropStep] at referenceEq
                  simpa [outerExpansionReference, outerExpansionStep,
                    expansionBuffersView, nextPositionalViews,
                    evaluationEventView, evaluationPushEq, returnedIndex,
                    nextIndex,
                    List.map_append] using referenceEq
              · change preflightRemaining iter1 < preflightRemaining iter
                omega
          | DynamicStar =>
              constructor
              · refine {
                  iterator := ?_, source := ?_, positionalNamedCapacity := ?_,
                  evaluationCapacity := ?_, reference := ?_
                }
                · unfold preflightIteratorInvariant
                  exact ⟨nextIndexBound, nextCountBound⟩
                · rw [sameSlice]
                  exact sourceEq
                · simp only [outerActualContribution] at contributionStep
                  change positional.val.length + named.val.length +
                      outerRemainingContribution iter1 ≤
                    BindCallFull.USIZE_CAPACITY.val
                  omega
                · change evaluationOrder.val.length +
                      preflightRemaining iter1 ≤
                    BindCallFull.USIZE_CAPACITY.val
                  omega
                · rw [dropStep] at referenceEq
                  simpa [outerExpansionReference, outerExpansionStep,
                    expansionBuffersView, outerExpansionErrorView,
                    returnedIndex, nextIndex] using referenceEq
              · change preflightRemaining iter1 < preflightRemaining iter
                omega
          | KeywordMapping =>
              constructor
              · refine {
                  iterator := ?_, source := ?_, positionalNamedCapacity := ?_,
                  evaluationCapacity := ?_, reference := ?_
                }
                · unfold preflightIteratorInvariant
                  exact ⟨nextIndexBound, nextCountBound⟩
                · rw [sameSlice]
                  exact sourceEq
                · simp only [outerActualContribution] at contributionStep
                  change positional.val.length + named.val.length +
                      outerRemainingContribution iter1 ≤
                    BindCallFull.USIZE_CAPACITY.val
                  omega
                · change evaluationOrder.val.length +
                      preflightRemaining iter1 ≤
                    BindCallFull.USIZE_CAPACITY.val
                  omega
                · rw [dropStep] at referenceEq
                  simpa [outerExpansionReference, outerExpansionStep,
                    expansionBuffersView, outerExpansionErrorView,
                    returnedIndex, nextIndex] using referenceEq
              · change preflightRemaining iter1 < preflightRemaining iter
                omega

theorem expand_actual_items_outer_loop_matches_reference
    (sourceItems : List (BindCallFull.ActualItem String Int))
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter (BindCallFull.ActualItem String Int)))
    (positional : alloc.vec.Vec
      (BindCallFull.PositionalActual String Int))
    (named : alloc.vec.Vec (BindCallFull.NamedActual String Int))
    (evaluationOrder : alloc.vec.Vec BindCallFull.EvaluationEvent)
    (expansionError : Option (BindCallFull.BindingError String))
    (iteratorInvariant : preflightIteratorInvariant iter)
    (sourceEq : iter.iter.slice.val = sourceItems)
    (positionalNamedCapacity :
      positional.val.length + named.val.length +
        outerRemainingContribution iter ≤
          BindCallFull.USIZE_CAPACITY.val)
    (evaluationCapacity :
      evaluationOrder.val.length + preflightRemaining iter ≤
        BindCallFull.USIZE_CAPACITY.val) :
    WP.spec
      (BindCallFull.expand_actual_items_with_allocator_loop0
        (totalIdentityClone String) (totalIdentityClone Int)
        iter positional named evaluationOrder expansionError)
      (fun output =>
        expansionBuffersView output.1 output.2.1 output.2.2.1 output.2.2.2 =
          outerExpansionReference iter.iter.i
            (sourceItems.drop iter.iter.i)
            (expansionBuffersView positional named evaluationOrder
              expansionError)) := by
  let expected := outerExpansionReference iter.iter.i
    (sourceItems.drop iter.iter.i)
    (expansionBuffersView positional named evaluationOrder expansionError)
  have initialInvariant : OuterExpansionInvariant sourceItems expected
      (iter, positional, named, evaluationOrder, expansionError) := {
    iterator := iteratorInvariant
    source := sourceEq
    positionalNamedCapacity := positionalNamedCapacity
    evaluationCapacity := evaluationCapacity
    reference := rfl
  }
  change WP.spec _ (fun (output :
      alloc.vec.Vec (BindCallFull.PositionalActual String Int) ×
        alloc.vec.Vec (BindCallFull.NamedActual String Int) ×
        alloc.vec.Vec BindCallFull.EvaluationEvent ×
        Option (BindCallFull.BindingError String)) =>
    expansionBuffersView output.1 output.2.1 output.2.2.1 output.2.2.2 =
      expected)
  unfold BindCallFull.expand_actual_items_with_allocator_loop0
  apply loop.spec_decr_nat
      (measure := fun state => preflightRemaining state.1)
      (inv := OuterExpansionInvariant sourceItems expected)
      (post := fun (output :
          alloc.vec.Vec (BindCallFull.PositionalActual String Int) ×
            alloc.vec.Vec (BindCallFull.NamedActual String Int) ×
            alloc.vec.Vec BindCallFull.EvaluationEvent ×
            Option (BindCallFull.BindingError String)) =>
        expansionBuffersView output.1 output.2.1 output.2.2.1
          output.2.2.2 = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (expand_actual_items_outer_loop_body_preserves_reference_and_decreases
      sourceItems expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost


inductive BoundArgumentView where
  | suppliedPositional : BindCallFull.PositionalActual String Int → BoundArgumentView
  | suppliedNamed : BindCallFull.NamedActual String Int → BoundArgumentView
  | defaulted : BindCallFull.TypedValue String Int → BoundArgumentView
  | residualPositionals : List (BindCallFull.PositionalActual String Int) →
      BoundArgumentView
  | residualKeywords : List (BindCallFull.NamedActual String Int) →
      BoundArgumentView

structure BindingCellView where
  parameter : BindCallFull.FormalParameter String Int
  kind : BindCallFull.ParameterKind
  argument : BoundArgumentView

def boundArgumentView : BindCallFull.BoundArgument String Int → BoundArgumentView
  | .SuppliedPositional actual => .suppliedPositional actual
  | .SuppliedNamed actual => .suppliedNamed actual
  | .Defaulted value => .defaulted value
  | .ResidualPositionals actuals => .residualPositionals actuals.val
  | .ResidualKeywords actuals => .residualKeywords actuals.val

def bindingCellView (cell : BindCallFull.BindingCell String Int) :
    BindingCellView :=
  ⟨cell.parameter, cell.kind, boundArgumentView cell.argument⟩

def bindingEnvironmentView
    (environment : BindCallFull.BindingEnvironment String Int) :
    List BindingCellView × List BindCallFull.EvaluationEvent :=
  (environment.cells.val.map bindingCellView, environment.evaluation_order.val)

def bindingResultView :
    core.result.Result (BindCallFull.BindingEnvironment String Int)
        (BindCallFull.BindingError String) →
      core.result.Result (List BindingCellView × List BindCallFull.EvaluationEvent)
        (BindCallFull.BindingError String)
  | .Ok environment => .Ok (bindingEnvironmentView environment)
  | .Err error => .Err error

def canonicalBaseReference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int) :
    List (BindCallFull.BindingCell String Int) ×
      Option (BindCallFull.BindingError String) :=
  let positionalOnly := canonicalPositionalOnlyReference
    signature.positional_only.val call 0 [] none
  let ordinary := canonicalOrdinaryReference signature.positional.val call
    signature.positional_only.val.length 0 positionalOnly.1 positionalOnly.2
  canonicalKeywordOnlyReference signature.keyword_only.val call ordinary.1
    ordinary.2

def canonicalEnvironmentReference
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int) :
    core.result.Result
      (List BindingCellView × List BindCallFull.EvaluationEvent)
      (BindCallFull.BindingError String) :=
  let base := canonicalBaseReference signature call
  match base.2 with
  | some error => .Err error
  | none =>
      let cells := base.1.map bindingCellView
      match signature.var_args with
      | none =>
          match signature.keyword_args with
          | none => .Ok (cells, call.evaluation_order.val)
          | some keywordArgs =>
              let residuals := canonicalNamedReference
                (canonicalKeywordSignature signature.positional_only
                  signature.positional signature.keyword_only keywordArgs)
                call.named.val [] 0
              .Ok (cells ++ [⟨keywordArgs, .KeywordArgs,
                .residualKeywords residuals⟩], call.evaluation_order.val)
      | some varArgs =>
          let residualStart := signature.positional_only.val.length +
            signature.positional.val.length
          let residuals := canonicalPositionalReference call.positional.val []
            residualStart
          let withVarargs := cells ++ [⟨varArgs, .VarArgs,
            .residualPositionals residuals⟩]
          match signature.keyword_args with
          | none => .Ok (withVarargs, call.evaluation_order.val)
          | some keywordArgs =>
              let residualKeywords := canonicalNamedReference
                (canonicalVariadicSignature signature.positional_only
                  signature.positional signature.keyword_only varArgs keywordArgs)
                call.named.val [] 0
              .Ok (withVarargs ++ [⟨keywordArgs, .KeywordArgs,
                .residualKeywords residualKeywords⟩],
                call.evaluation_order.val)


theorem canonicalPositionalOnlyReference_length
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (index : Nat)
    (cells : List (BindCallFull.BindingCell String Int))
    (constructionError : Option (BindCallFull.BindingError String)) :
    (canonicalPositionalOnlyReference remaining call index cells
      constructionError).1.length ≤ cells.length + remaining.length := by
  induction remaining generalizing index cells constructionError with
  | nil => simp [canonicalPositionalOnlyReference]
  | cons parameter tail inductionHypothesis =>
      simp only [canonicalPositionalOnlyReference]
      let next := canonicalPositionalOnlyStep parameter call index cells
        constructionError
      calc
        (canonicalPositionalOnlyReference tail call (index + 1) next.1
            next.2).1.length ≤ next.1.length + tail.length :=
          inductionHypothesis (index + 1) next.1 next.2
        _ ≤ cells.length + (parameter :: tail).length := by
          have stepLength : next.1.length ≤ cells.length + 1 := by
            cases constructionError with
            | some error => simp [next, canonicalPositionalOnlyStep]
            | none =>
                cases actualEq : call.positional.val[index]? with
                | some actual =>
                    simp [next, canonicalPositionalOnlyStep, actualEq]
                | none =>
                    cases defaultEq : parameter.default_value with
                    | some defaultValue =>
                        simp [next, canonicalPositionalOnlyStep, actualEq,
                          defaultEq]
                    | none =>
                        simp [next, canonicalPositionalOnlyStep, actualEq,
                          defaultEq]
          simp only [List.length_cons]
          omega

theorem canonicalOrdinaryReference_length
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOffset parameterIndex : Nat)
    (cells : List (BindCallFull.BindingCell String Int))
    (constructionError : Option (BindCallFull.BindingError String)) :
    (canonicalOrdinaryReference remaining call positionalOffset parameterIndex
      cells constructionError).1.length ≤ cells.length + remaining.length := by
  induction remaining generalizing parameterIndex cells constructionError with
  | nil => simp [canonicalOrdinaryReference]
  | cons parameter tail inductionHypothesis =>
      simp only [canonicalOrdinaryReference]
      let next := canonicalOrdinaryStep parameter call
        (positionalOffset + parameterIndex) cells constructionError
      calc
        (canonicalOrdinaryReference tail call positionalOffset
            (parameterIndex + 1) next.1 next.2).1.length ≤
            next.1.length + tail.length :=
          inductionHypothesis (parameterIndex + 1) next.1 next.2
        _ ≤ cells.length + (parameter :: tail).length := by
          have stepLength : next.1.length ≤ cells.length + 1 := by
            cases constructionError with
            | some error => simp [next, canonicalOrdinaryStep]
            | none =>
                let argument : Option
                    (BindCallFull.BoundArgument String Int) :=
                  match call.positional.val[positionalOffset + parameterIndex]? with
                  | some actual => some (.SuppliedPositional actual)
                  | none =>
                      match findNamedActualReference call.named.deref
                          parameter.name with
                      | some actual => some (.SuppliedNamed actual)
                      | none => parameter.default_value.map .Defaulted
                change (match argument with
                  | some argument => (cells ++ [({
                      parameter := parameter
                      kind := .Positional
                      argument := argument } :
                        BindCallFull.BindingCell String Int)], none)
                  | none => (cells, some
                    (BindCallFull.BindingError.MissingRequiredArgument
                      parameter.name))).1.length ≤ cells.length + 1
                cases argument <;> simp
          simp only [List.length_cons]
          omega

theorem canonicalKeywordOnlyReference_length
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (cells : List (BindCallFull.BindingCell String Int))
    (constructionError : Option (BindCallFull.BindingError String)) :
    (canonicalKeywordOnlyReference remaining call cells
      constructionError).1.length ≤ cells.length + remaining.length := by
  induction remaining generalizing cells constructionError with
  | nil => simp [canonicalKeywordOnlyReference]
  | cons parameter tail inductionHypothesis =>
      simp only [canonicalKeywordOnlyReference]
      let next := canonicalKeywordOnlyStep parameter call cells constructionError
      calc
        (canonicalKeywordOnlyReference tail call next.1 next.2).1.length ≤
            next.1.length + tail.length :=
          inductionHypothesis next.1 next.2
        _ ≤ cells.length + (parameter :: tail).length := by
          have stepLength : next.1.length ≤ cells.length + 1 := by
            cases constructionError with
            | some error => simp [next, canonicalKeywordOnlyStep]
            | none =>
                let argument : Option
                    (BindCallFull.BoundArgument String Int) :=
                  match findNamedActualReference call.named.deref
                      parameter.name with
                  | some actual => some (.SuppliedNamed actual)
                  | none => parameter.default_value.map .Defaulted
                change (match argument with
                  | some argument => (cells ++ [({
                      parameter := parameter
                      kind := .KeywordOnly
                      argument := argument } :
                        BindCallFull.BindingCell String Int)], none)
                  | none => (cells, some
                    (BindCallFull.BindingError.MissingRequiredArgument
                      parameter.name))).1.length ≤ cells.length + 1
                cases argument <;> simp
          simp only [List.length_cons]
          omega

theorem canonicalOrdinaryReference_preserves_error
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOffset parameterIndex : Nat)
    (cells : List (BindCallFull.BindingCell String Int))
    (error : BindCallFull.BindingError String) :
    canonicalOrdinaryReference remaining call positionalOffset parameterIndex
      cells (some error) = (cells, some error) := by
  induction remaining generalizing parameterIndex cells with
  | nil => simp [canonicalOrdinaryReference]
  | cons parameter tail inductionHypothesis =>
      simp [canonicalOrdinaryReference, canonicalOrdinaryStep,
        inductionHypothesis]

theorem canonicalKeywordOnlyReference_preserves_error
    (remaining : List (BindCallFull.FormalParameter String Int))
    (call : BindCallFull.ExpandedCall String Int)
    (cells : List (BindCallFull.BindingCell String Int))
    (error : BindCallFull.BindingError String) :
    canonicalKeywordOnlyReference remaining call cells (some error) =
      (cells, some error) := by
  induction remaining generalizing cells with
  | nil => simp [canonicalKeywordOnlyReference]
  | cons parameter tail inductionHypothesis =>
      simp [canonicalKeywordOnlyReference, canonicalKeywordOnlyStep,
        inductionHypothesis]

theorem canonicalEnvironmentReference_after_ordinary_error
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOnlyCells ordinaryCells :
      List (BindCallFull.BindingCell String Int))
    (error : BindCallFull.BindingError String)
    (positionalOnlyEq :
      canonicalPositionalOnlyReference signature.positional_only.val call 0
        [] none = (positionalOnlyCells, none))
    (ordinaryEq : canonicalOrdinaryReference signature.positional.val call
      signature.positional_only.val.length 0 positionalOnlyCells none =
        (ordinaryCells, some error)) :
    canonicalEnvironmentReference signature call = .Err error := by
  unfold canonicalEnvironmentReference canonicalBaseReference
  rw [positionalOnlyEq]
  dsimp only
  rw [ordinaryEq]
  simp [canonicalKeywordOnlyReference_preserves_error]

theorem canonicalEnvironmentReference_after_positional_only_error
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOnlyCells : List (BindCallFull.BindingCell String Int))
    (error : BindCallFull.BindingError String)
    (positionalOnlyEq :
      canonicalPositionalOnlyReference signature.positional_only.val call 0
        [] none = (positionalOnlyCells, some error)) :
    canonicalEnvironmentReference signature call = .Err error := by
  unfold canonicalEnvironmentReference canonicalBaseReference
  rw [positionalOnlyEq]
  dsimp only
  rw [canonicalOrdinaryReference_preserves_error]
  rw [canonicalKeywordOnlyReference_preserves_error]

theorem canonicalEnvironmentReference_after_keyword_error
    (signature : BindCallFull.CallSignature String Int)
    (call : BindCallFull.ExpandedCall String Int)
    (positionalOnlyCells ordinaryCells keywordCells :
      List (BindCallFull.BindingCell String Int))
    (error : BindCallFull.BindingError String)
    (positionalOnlyEq :
      canonicalPositionalOnlyReference signature.positional_only.val call 0
        [] none = (positionalOnlyCells, none))
    (ordinaryEq : canonicalOrdinaryReference signature.positional.val call
      signature.positional_only.val.length 0 positionalOnlyCells none =
        (ordinaryCells, none))
    (keywordEq : canonicalKeywordOnlyReference signature.keyword_only.val call
      ordinaryCells none = (keywordCells, some error)) :
    canonicalEnvironmentReference signature call = .Err error := by
  unfold canonicalEnvironmentReference canonicalBaseReference
  rw [positionalOnlyEq]
  dsimp only
  rw [ordinaryEq]
  dsimp only
  rw [keywordEq]


end BindCallFull.Proofs
