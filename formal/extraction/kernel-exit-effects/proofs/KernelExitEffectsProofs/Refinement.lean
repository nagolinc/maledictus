import KernelExitEffects

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace KernelExitEffects.Proofs

theorem iteratorAnyStringExact
    (iter : core.slice.iter.Iter String)
    (expected : String) :
    exists finalIter,
      iteratorAny
          check_exit_effects.closure.Insts.CoreOpsFunctionFnMutTupleSharedStringBool
          iter expected =
        .ok ((iter.slice.val.drop iter.i).any (fun value => value == expected), finalIter) := by
  rw [iteratorAny]
  by_cases within : iter.i < iter.slice.len
  · rw [dif_pos within]
    have withinValues : iter.i < iter.slice.val.length := by simpa using within
    simp only [check_exit_effects.closure.Insts.CoreOpsFunctionFnMutTupleSharedStringBool,
      check_exit_effects.closure.Insts.CoreOpsFunctionFnOnceTupleSharedStringBool,
      check_exit_effects.closure.Insts.CoreOpsFunctionFnMutTupleSharedStringBool.call_mut,
      alloc.string.String.Insts.CoreCmpPartialEqString.eq, bind_tc_ok]
    by_cases isMatch : iter.slice.val[iter.i] == expected
    · refine ⟨{ iter with i := iter.i + 1 }, ?_⟩
      simp only [isMatch]
      rw [List.drop_eq_getElem_cons withinValues]
      have itemEq : iter.slice.val[iter.i] = expected := by simpa using isMatch
      simp [itemEq]
    · obtain ⟨finalIter, recursive⟩ :=
        iteratorAnyStringExact ({ iter with i := iter.i + 1 }) expected
      refine ⟨finalIter, ?_⟩
      simp only [isMatch]
      change
        iteratorAny
            check_exit_effects.closure.Insts.CoreOpsFunctionFnMutTupleSharedStringBool
            ({ iter with i := iter.i + 1 }) expected = _
      rw [recursive]
      rw [List.drop_eq_getElem_cons withinValues]
      simp only [List.any, isMatch, Bool.false_or]
  · rw [dif_neg within]
    refine ⟨iter, ?_⟩
    have exhausted : iter.slice.val.length <= iter.i := by
      simpa using Nat.le_of_not_gt within
    simp [List.drop_eq_nil_of_le exhausted]
termination_by iter.slice.val.length - iter.i
decreasing_by omega

def checkExitEffectsRemaining :
    List ExitEffect → List String → core.result.Result Unit KernelFailure
  | [], _ => .Ok ()
  | .Return _ :: tail, allowed => checkExitEffectsRemaining tail allowed
  | .Raise exceptionType :: tail, allowed =>
      if allowed.any (fun allowedType => allowedType == exceptionType) then
        checkExitEffectsRemaining tail allowed
      else
        .Err (.UnexpectedException exceptionType)
  | .Unknown reason :: _, _ => .Err (.UnknownEffect reason)

def checkExitEffectsReference
    (effects : List ExitEffect) (allowed : List String) :
    core.result.Result Unit KernelFailure :=
  if effects.isEmpty then .Err .NoEffects
  else checkExitEffectsRemaining effects allowed

def checkExitEffectsMeasure (iter : core.slice.iter.Iter ExitEffect) : Nat :=
  iter.slice.val.length - iter.i

def checkExitEffectStep
    (allowed : Slice String) (effect : ExitEffect)
    (next : core.slice.iter.Iter ExitEffect) :
    Result (ControlFlow (core.slice.iter.Iter ExitEffect)
      (core.result.Result Unit KernelFailure)) :=
  match effect with
  | .Return _ => .ok (cont next)
  | .Raise exceptionType => do
      let allowedIter ← core.slice.Slice.iter allowed
      let (isAllowed, _) ←
        core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
          check_exit_effects.closure.Insts.CoreOpsFunctionFnMutTupleSharedStringBool
          allowedIter exceptionType
      if isAllowed then .ok (cont next)
      else do
        let cloned ← alloc.string.String.Insts.CoreCloneClone.clone exceptionType
        .ok (done (.Err (.UnexpectedException cloned)))
  | .Unknown reason => do
      let cloned ← alloc.string.String.Insts.CoreCloneClone.clone reason
      .ok (done (.Err (.UnknownEffect cloned)))

theorem check_exit_effect_exact
    (allowed : Slice String) (effect : ExitEffect) (tail : List ExitEffect)
    (next current : core.slice.iter.Iter ExitEffect)
    (expected : core.result.Result Unit KernelFailure)
    (nextExact :
      checkExitEffectsRemaining (next.slice.val.drop next.i) allowed.val =
        checkExitEffectsRemaining tail allowed.val)
    (decreases : checkExitEffectsMeasure next < checkExitEffectsMeasure current)
    (invariant : checkExitEffectsRemaining (effect :: tail) allowed.val = expected) :
    WP.spec (checkExitEffectStep allowed effect next)
      (fun flow =>
        match flow with
        | .done output => output = expected
        | .cont continued =>
            checkExitEffectsRemaining
                (continued.slice.val.drop continued.i) allowed.val = expected ∧
              checkExitEffectsMeasure continued < checkExitEffectsMeasure current) := by
  cases effect with
  | Return typeName =>
      rw [checkExitEffectStep]
      simp only [checkExitEffectsRemaining] at invariant
      simp [nextExact, invariant, decreases]
  | Raise exceptionType =>
      rw [checkExitEffectStep]
      obtain ⟨finalIter, anyExact⟩ :=
        iteratorAnyStringExact ({ slice := allowed, i := 0 }) exceptionType
      simp only [core.slice.Slice.iter, bind_tc_ok]
      rw [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any,
        anyExact]
      simp only [bind_tc_ok, List.drop_zero]
      by_cases allowedException :
          allowed.val.any (fun allowedType => allowedType == exceptionType)
      · simp only [checkExitEffectsRemaining, allowedException, if_true] at invariant ⊢
        exact ⟨nextExact.trans invariant, decreases⟩
      · simp only [checkExitEffectsRemaining, allowedException] at invariant ⊢
        simpa [alloc.string.String.Insts.CoreCloneClone.clone] using invariant
  | Unknown reason =>
      rw [checkExitEffectStep]
      simp only [checkExitEffectsRemaining] at invariant
      simpa [alloc.string.String.Insts.CoreCloneClone.clone] using invariant

theorem check_exit_effects_body_exact
    (allowed : Slice String) (iter : core.slice.iter.Iter ExitEffect)
    (expected : core.result.Result Unit KernelFailure)
    (invariant :
      checkExitEffectsRemaining (iter.slice.val.drop iter.i) allowed.val = expected) :
    WP.spec (check_exit_effects_loop.body allowed iter) (fun flow =>
      match flow with
      | .done output => output = expected
      | .cont next =>
          checkExitEffectsRemaining (next.slice.val.drop next.i) allowed.val = expected ∧
            checkExitEffectsMeasure next < checkExitEffectsMeasure iter) := by
  rw [check_exit_effects_loop.body.eq_def]
  by_cases within : iter.i < iter.slice.len
  · have withinValues : iter.i < iter.slice.val.length := by simpa using within
    have nextStep :
        core.slice.iter.IteratorSliceIter.next iter =
          .ok (some iter.slice.val[iter.i], { iter with i := iter.i + 1 }) := by
      unfold core.slice.iter.IteratorSliceIter.next
      rw [dif_pos within]
      congr 3
    rw [nextStep]
    simp only [bind_tc_ok]
    have dropStep :
        iter.slice.val.drop iter.i =
          iter.slice.val[iter.i] :: iter.slice.val.drop (iter.i + 1) :=
      List.drop_eq_getElem_cons withinValues
    change WP.spec
      (checkExitEffectStep allowed iter.slice.val[iter.i]
        ({ iter with i := iter.i + 1 })) _
    apply check_exit_effect_exact allowed iter.slice.val[iter.i]
      (iter.slice.val.drop (iter.i + 1)) ({ iter with i := iter.i + 1 })
      iter expected
    · rfl
    · simp [checkExitEffectsMeasure]
      omega
    · rw [← dropStep]
      exact invariant
  · have exhausted : iter.slice.val.length ≤ iter.i := by
      simpa using Nat.le_of_not_gt within
    have nextStep :
        core.slice.iter.IteratorSliceIter.next iter = .ok (none, iter) := by
      unfold core.slice.iter.IteratorSliceIter.next
      simp [exhausted]
    rw [nextStep]
    rw [List.drop_eq_nil_of_le exhausted] at invariant
    simpa [checkExitEffectsRemaining] using invariant

theorem result_eq_ok_of_spec_eq {T : Type} (result : Result T) (expected : T)
    (spec : WP.spec result (fun output => output = expected)) :
    result = .ok expected := by
  cases result <;> simp_all [WP.spec, WP.theta, WP.wp_return]

theorem check_exit_effects_loop_exact
    (iter : core.slice.iter.Iter ExitEffect) (allowed : Slice String) :
    check_exit_effects_loop iter allowed =
      .ok (checkExitEffectsRemaining (iter.slice.val.drop iter.i) allowed.val) := by
  let expected := checkExitEffectsRemaining (iter.slice.val.drop iter.i) allowed.val
  have initialInvariant :
      checkExitEffectsRemaining (iter.slice.val.drop iter.i) allowed.val = expected := rfl
  have loopSpec :
      WP.spec (check_exit_effects_loop iter allowed) (fun output => output = expected) := by
    unfold check_exit_effects_loop
    apply loop.spec_decr_nat
        (measure := checkExitEffectsMeasure)
        (inv := fun current =>
          checkExitEffectsRemaining (current.slice.val.drop current.i) allowed.val =
            expected)
        (post := fun output => output = expected)
        (hInv := initialInvariant)
    intro current invariant
    apply WP.spec_mono
      (check_exit_effects_body_exact allowed current expected invariant)
    intro flow flowExact
    cases flow <;> simpa using flowExact
  exact result_eq_ok_of_spec_eq _ _ loopSpec

/-- Exact all-input refinement of the extracted production entrypoint. The list reference
preserves source order, so its result identifies the first disallowed `Raise` or first
`Unknown`, while accepting returns and explicitly allowed exception types. -/
theorem check_exit_effects_all_inputs_exact
    (effects : Slice ExitEffect) (allowed : Slice String) :
    check_exit_effects effects allowed =
      .ok (checkExitEffectsReference effects.val allowed.val) := by
  rw [check_exit_effects]
  by_cases empty : effects.val = []
  · simp [core.slice.Slice.is_empty, empty, checkExitEffectsReference]
  · have nonempty : effects.val.isEmpty = false := by simpa using empty
    have lengthNe : effects.val.length ≠ 0 := by
      intro lengthZero
      apply empty
      exact List.eq_nil_of_length_eq_zero lengthZero
    simp [core.slice.Slice.is_empty, lengthNe,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
      check_exit_effects_loop_exact, checkExitEffectsReference, nonempty]

end KernelExitEffects.Proofs
