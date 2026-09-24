import VcTermSortProofs.TerminationMeasure
import VcTermSortProofs.ConcreteLoops

open Aeneas Aeneas.Std Result ControlFlow Error

namespace VcTermSort.Proofs

/-- A generated Aeneas computation has reached a concrete Rust return or
    failure rather than the bottom element introduced by `partial_fixpoint`. -/
def Terminates {T : Type} (result : Result T) : Prop := result ≠ .div

attribute [local simp] sort_clone_exact string_clone_refines box_as_ref_refines

theorem term_sort_bool_terminates (value : Bool) :
    Terminates (VcTermSort.Term.sort_typed (.Bool value)) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [Terminates]

theorem term_sort_int_terminates (value : Std.I64) :
    Terminates (VcTermSort.Term.sort_typed (.Int value)) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [Terminates]

theorem term_sort_string_terminates (value : String) :
    Terminates (VcTermSort.Term.sort_typed (.String value)) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [Terminates]

theorem term_sort_bytes_terminates (value : List Std.U8) :
    Terminates (VcTermSort.Term.sort_typed (.Bytes value)) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [Terminates]

theorem term_sort_range_terminates (value : List Std.I64) :
    Terminates (VcTermSort.Term.sort_typed (.Range value)) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [Terminates]

theorem term_sort_unit_terminates :
    Terminates (VcTermSort.Term.sort_typed .Unit) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [Terminates]

theorem term_sort_null_reference_terminates :
    Terminates (VcTermSort.Term.sort_typed .NullReference) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [Terminates]

theorem term_sort_nominal_reference_terminates
    (className objectName : String) :
    Terminates (VcTermSort.Term.sort_typed (.NominalReference className objectName)) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [Terminates, alloc.string.String.is_empty,
    Str.Insts.AllocBorrowToOwnedString.to_owned]
  split <;> simp

theorem term_sort_class_literal_terminates (className : String) :
    Terminates (VcTermSort.Term.sort_typed (.ClassLiteral className)) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [Terminates, alloc.string.String.is_empty,
    Str.Insts.AllocBorrowToOwnedString.to_owned]
  split <;> simp

theorem term_sort_permission_mask_valid_terminates
    (mask : Std.U32) (field : String) :
    Terminates (VcTermSort.Term.sort_typed (.PermissionMaskValid mask field)) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [Terminates, alloc.string.String.is_empty,
    Str.Insts.AllocBorrowToOwnedString.to_owned]
  split <;> simp

/-- `require_sort` cannot introduce divergence once the recursive sort of its
    operand is known to terminate. This isolates the generated partial
    fixpoint at the common unary/binary recursive-call boundary. -/
theorem require_sort_terminates_of_term_sort_terminates
    (term : VcTermSort.Term) (expected : VcTermSort.Sort)
    (context : VcTermSort.SortContext)
    (childTerminates : Terminates (VcTermSort.Term.sort_typed term)) :
    Terminates (VcTermSort.require_sort term expected context) := by
  rw [VcTermSort.require_sort.eq_def]
  cases observed : VcTermSort.Term.sort_typed term with
  | div => simp [Terminates, observed] at childTerminates
  | fail error => simp [Terminates]
  | ok result =>
      cases result with
      | Err error =>
          simp [Terminates,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok actual =>
          simp [Terminates, core.result.Result.Insts.CoreOpsTry.branch]
          rw [VcTermSort.sortPartialEqModel actual expected]
          simp [
            core.fmt.rt.Argument.new_display,
            core.fmt.rt.Argument.new_debug,
            core.fmt.Arguments.new,
            alloc.fmt.format,
            core.hint.must_use]
          split <;> simp_all

/-- The generated `?` propagation around a successful unit check is total
    whenever that check is total. -/
theorem require_sort_then_ok_terminates
    (required : Result (core.result.Result Unit VcTermSort.SortError))
    (requiredTerminates : Terminates required)
    (success : VcTermSort.Sort) :
    Terminates (do
      let r ← required
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (core.result.Result.Ok success)
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual) := by
  cases observed : required with
  | div => simp [Terminates, observed] at requiredTerminates
  | fail error => simp [Terminates]
  | ok result =>
      cases result <;>
        simp [Terminates,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- The generated left-to-right `?` chain for two recursive sort checks cannot
    diverge once both checks are known to terminate. Failure of the first
    check still short-circuits the second exactly as in production Rust. -/
theorem require_two_sorts_then_ok_terminates
    (first second : Result (core.result.Result Unit VcTermSort.SortError))
    (firstTerminates : Terminates first)
    (secondTerminates : Terminates second)
    (success : VcTermSort.Sort) :
    Terminates (do
      let r ← first
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
          let r1 ← second
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (core.result.Result.Ok success)
          | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual) := by
  cases firstObserved : first with
  | div => simp [Terminates, firstObserved] at firstTerminates
  | fail error => simp [Terminates]
  | ok firstResult =>
      cases firstResult with
      | Err error =>
          simp [Terminates,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok value =>
          cases secondObserved : second with
          | div => simp [Terminates, secondObserved] at secondTerminates
          | fail error =>
              simp [Terminates, core.result.Result.Insts.CoreOpsTry.branch]
          | ok secondResult =>
              cases secondResult <;>
                simp [Terminates, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Exact termination rule for the generated lowering of Rust's `?`: once the
    checked computation and every successful continuation terminate, the
    whole first-error-preserving chain terminates. -/
theorem result_try_then_terminates
    {A B : Type}
    (checked : Result (core.result.Result A VcTermSort.SortError))
    (continuation : A → Result (core.result.Result B VcTermSort.SortError))
    (checkedTerminates : Terminates checked)
    (continuationTerminates : ∀ value, Terminates (continuation value)) :
    Terminates (do
      let r ← checked
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue value => continuation value
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            B (core.convert.FromSame VcTermSort.SortError) residual) := by
  cases checkedObserved : checked with
  | div => simp [Terminates, checkedObserved] at checkedTerminates
  | fail error => simp [Terminates]
  | ok result =>
      cases result with
      | Err error =>
          simp [Terminates,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok value =>
          simpa [core.result.Result.Insts.CoreOpsTry.branch] using
            continuationTerminates value

theorem result_bind_terminates
    {A B : Type} (input : Result A) (continuation : A → Result B)
    (inputTerminates : Terminates input)
    (continuationTerminates : ∀ value, Terminates (continuation value)) :
    Terminates (do
      let value ← input
      continuation value) := by
  cases observed : input with
  | div => simp [Terminates, observed] at inputTerminates
  | fail error => simp [Terminates, observed]
  | ok value => simpa [observed] using continuationTerminates value

theorem result_bind_terminates_of_observed_output
    {A B : Type} (input : Result A) (continuation : A → Result B)
    (inputTerminates : Terminates input)
    (outputTerminates : ∀ value, input = .ok value →
      Terminates (continuation value)) :
    Terminates (do
      let value ← input
      continuation value) := by
  cases observed : input with
  | div => simp [Terminates, observed] at inputTerminates
  | fail error => simp [Terminates, observed]
  | ok value => simpa [observed] using outputTerminates value observed

theorem result_try_then_ok_unit_terminates
    (checked : Result (core.result.Result Unit VcTermSort.SortError))
    (checkedTerminates : Terminates checked) :
    Terminates (do
      let r ← checked
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (core.result.Result.Ok ())
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame VcTermSort.SortError) residual) := by
  cases observed : checked with
  | div => simp [Terminates, observed] at checkedTerminates
  | fail error => simp [Terminates]
  | ok result =>
      cases result <;>
        simp [Terminates,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- The generated structural sort clone is a concrete, total source boundary. -/
theorem sort_clone_terminates (sort : VcTermSort.Sort) :
    Terminates (VcTermSort.Sort.Insts.CoreCloneClone.clone sort) := by
  rw [sort_clone_exact]
  simp [Terminates]

theorem sort_clone_then_result_ok_terminates (sort : VcTermSort.Sort) :
    Terminates (do
      let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone sort
      ok (core.result.Result.Ok cloned :
        core.result.Result VcTermSort.Sort VcTermSort.SortError)) := by
  rw [sort_clone_exact]
  simp [Terminates]

/-- A structured diagnostic carrying one exact cloned sort is total. -/
theorem sort_clone_then_result_error_terminates
    {A : Type}
    (sort : VcTermSort.Sort)
    (makeError : VcTermSort.Sort → VcTermSort.SortError) :
    Terminates (do
      let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone sort
      ok (core.result.Result.Err (makeError cloned) :
        core.result.Result A VcTermSort.SortError)) := by
  rw [sort_clone_exact]
  simp [Terminates]

/-- A structured diagnostic carrying two exact cloned sorts is total. -/
theorem two_sort_clones_then_result_error_terminates
    {A : Type}
    (first second : VcTermSort.Sort)
    (makeError : VcTermSort.Sort → VcTermSort.Sort → VcTermSort.SortError) :
    Terminates (do
      let firstClone ← VcTermSort.Sort.Insts.CoreCloneClone.clone first
      let secondClone ← VcTermSort.Sort.Insts.CoreCloneClone.clone second
      ok (core.result.Result.Err (makeError firstClone secondClone) :
        core.result.Result A VcTermSort.SortError)) := by
  rw [sort_clone_exact, sort_clone_exact]
  simp [Terminates]

theorem sort_partial_eq_terminates
    (left right : VcTermSort.Sort) :
    Terminates
      (VcTermSort.Sort.Insts.CoreCmpPartialEqSort.eq left right) := by
  unfold Terminates
  rw [sort_partial_eq_result_refines_compiler_derive]
  simp

theorem u32_shared_gt_terminates (left right : Std.U32) :
    Terminates
      (Shared1A.Insts.CoreCmpPartialOrdShared0B.gt core.cmp.PartialOrdU32
        left right) := by
  rw [shared_gt_refines]
  simp [Terminates]

theorem sort_ne_terminates (left right : VcTermSort.Sort) :
    Terminates
      (core.cmp.PartialEq.ne.trait_default
        VcTermSort.Sort.Insts.CoreCmpPartialEqSort left right) := by
  simp only [Terminates, core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default]
  rw [VcTermSort.sortPartialEqModel]
  simp

/-- A fuel-normalized extracted loop cannot diverge when its invariant makes
    each body call total, continuations preserve the invariant, and the source
    measure strictly decreases. -/
theorem run_loop_fuel_terminates_of_invariant
    {State Output : Type}
    (body : State → Result (ControlFlow State Output))
    (invariant : State → Prop) (measure : State → Nat)
    (bodyTerminates : ∀ state, invariant state → Terminates (body state))
    (preserves : ∀ state next, invariant state →
      body state = .ok (.cont next) → invariant next)
    (decreases : ∀ state next,
      body state = .ok (.cont next) → measure next < measure state) :
    ∀ fuel state, invariant state → measure state < fuel →
      Terminates (VcTermSort.runLoopFuel fuel body state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state stateInvariant bounded
      omega
  | succ fuel inductionHypothesis =>
      intro state stateInvariant bounded
      have currentTerminates := bodyTerminates state stateInvariant
      cases observed : body state with
      | div => simp [Terminates, observed] at currentTerminates
      | fail error => simp [VcTermSort.runLoopFuel, Terminates, observed]
      | ok flow =>
          cases flow with
          | done output =>
              simp [VcTermSort.runLoopFuel, Terminates, observed]
          | cont next =>
              simp [VcTermSort.runLoopFuel, observed]
              apply inductionHypothesis next
              · exact preserves state next stateInvariant observed
              · have smaller := decreases state next observed
                omega

theorem slice_iterator_next_some_member {T : Type}
    (iter next : core.slice.iter.Iter T) (value : T)
    (observed : core.slice.iter.IteratorSliceIter.next iter =
      .ok (some value, next)) :
    value ∈ iter.slice.val ∧ next.slice = iter.slice := by
  unfold core.slice.iter.IteratorSliceIter.next at observed
  split at observed
  · simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at observed
    obtain ⟨valueEq, nextEq⟩ := observed
    subst value
    subst next
    constructor
    · exact List.getElem_mem ..
    · rfl
  · simp at observed

theorem slice_iterator_next_terminates {T : Type}
    (iter : core.slice.iter.Iter T) :
    Terminates (core.slice.iter.IteratorSliceIter.next iter) := by
  by_cases within : iter.i < iter.slice.len
  · obtain ⟨value, next, observed, _, _⟩ :=
      slice_iterator_next_within_refines iter within
    rw [observed]
    simp [Terminates]
  · rw [slice_iterator_next_exhausted_refines iter within]
    simp [Terminates]

theorem sort_bool_accumulator_body_terminates
    (predicate : VcTermSort.Sort → Result Bool)
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (predicate child)) :
    Terminates (do
      let (maybeElement, next) ← core.slice.iter.IteratorSliceIter.next iter
      match maybeElement with
      | none => ok (done result)
      | some element =>
          if result then
            let nextResult ← predicate element
            ok (cont (next, nextResult))
          else ok (cont (next, false))) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail error => simp [Terminates, observed]
  | ok pair =>
      obtain ⟨maybeElement, next⟩ := pair
      cases maybeElement with
      | none => simp [Terminates, observed]
      | some element =>
          cases result with
          | false => simp [Terminates, observed]
          | true =>
              have member := (slice_iterator_next_some_member
                iter next element observed).1
              have recursiveTerminates := childrenTerminate element member
              cases predicateObserved : predicate element with
              | div => simp [Terminates, predicateObserved] at recursiveTerminates
              | fail error => simp [Terminates, observed, predicateObserved]
              | ok nextResult => simp [Terminates, observed, predicateObserved]

theorem sort_bool_accumulator_body_preserves_slice
    (predicate : VcTermSort.Sort → Result Bool)
    (iter next : core.slice.iter.Iter VcTermSort.Sort)
    (result nextResult : Bool)
    (continued : (do
      let (maybeElement, advanced) ← core.slice.iter.IteratorSliceIter.next iter
      match maybeElement with
      | none => ok (done result)
      | some element =>
          if result then
            let result1 ← predicate element
            ok (cont (advanced, result1))
          else ok (cont (advanced, false))) = .ok (cont (next, nextResult))) :
    next.slice = iter.slice := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error => simp [observed] at continued
  | div => simp [observed] at continued
  | ok pair =>
      obtain ⟨maybeElement, advanced⟩ := pair
      cases maybeElement with
      | none => simp [observed] at continued
      | some element =>
          have advancedSlice := (slice_iterator_next_some_member
            iter advanced element observed).2
          have advancedEq : advanced = next := by
            cases result with
            | false => simp [observed] at continued; exact continued.1
            | true =>
                simp [observed] at continued
                simp only [Bind.bind, Std.bind] at continued
                all_goals repeat' split at continued
                all_goals
                  have mapped := congrArg continuationIterator continued
                  simp [continuationIterator] at mapped <;> assumption
          subst next
          exact advancedSlice

theorem sort_bool_accumulator_body_decreases_generic
    (predicate : VcTermSort.Sort → Result Bool)
    (iter next : core.slice.iter.Iter VcTermSort.Sort)
    (result nextResult : Bool)
    (continued : (do
      let (maybeElement, advanced) ← core.slice.iter.IteratorSliceIter.next iter
      match maybeElement with
      | none => ok (done result)
      | some element =>
          if result then
            let result1 ← predicate element
            ok (cont (advanced, result1))
          else ok (cont (advanced, false))) = ok (cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error => simp [observed] at continued
  | div => simp [observed] at continued
  | ok pair =>
      obtain ⟨maybeElement, advanced⟩ := pair
      cases maybeElement with
      | none => simp [observed] at continued
      | some element =>
          have advancedEq : advanced = next := by
            cases result with
            | false => simp [observed] at continued; exact continued.1
            | true =>
                simp [observed] at continued
                simp only [Bind.bind, Std.bind] at continued
                all_goals repeat' split at continued
                all_goals
                  have mapped := congrArg continuationIterator continued
                  simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced element observed

theorem sort_bool_accumulator_loop_terminates
    (predicate : VcTermSort.Sort → Result Bool)
    (body : core.slice.iter.Iter VcTermSort.Sort → Bool →
      Result (ControlFlow (core.slice.iter.Iter VcTermSort.Sort × Bool) Bool))
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool)
    (bodyTerminates : ∀ state : core.slice.iter.Iter VcTermSort.Sort × Bool,
      (∀ child, child ∈ state.1.slice.val → Terminates (predicate child)) →
      Terminates (body state.1 state.2))
    (bodyPreserves : ∀ state next :
      core.slice.iter.Iter VcTermSort.Sort × Bool,
      body state.1 state.2 = .ok (.cont next) →
      next.1.slice = state.1.slice)
    (bodyDecreases : ∀ state next :
      core.slice.iter.Iter VcTermSort.Sort × Bool,
      body state.1 state.2 = .ok (.cont next) →
      sliceIteratorRemaining next.1 < sliceIteratorRemaining state.1)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (predicate child)) :
    Terminates (VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
      (fun state => body state.1 state.2) (iter, result)) := by
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter VcTermSort.Sort × Bool =>
      body state.1 state.2)
    (fun state => ∀ child, child ∈ state.1.slice.val →
      Terminates (predicate child))
    (fun state => sliceIteratorRemaining state.1)
  · intro state invariant
    exact bodyTerminates state invariant
  · intro state next invariant continued child member
    apply invariant child
    have slicesEqual := bodyPreserves state next continued
    simpa [slicesEqual] using member
  · intro state next continued
    exact bodyDecreases state next continued
  · exact childrenTerminate
  · simp [sliceIteratorRemaining]

theorem all_list_element_sorts_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.is_list_element_sort child)) :
    Terminates (VcTermSort.all_list_element_sorts_loop iter result) := by
  unfold VcTermSort.all_list_element_sorts_loop
  exact sort_bool_accumulator_loop_terminates
    VcTermSort.is_list_element_sort
    VcTermSort.all_list_element_sorts_loop.body iter result
    (by
      intro state invariant
      rw [VcTermSort.all_list_element_sorts_loop.body.eq_def]
      exact sort_bool_accumulator_body_terminates
        VcTermSort.is_list_element_sort state.1 state.2 invariant)
    (by
      intro state next continued
      rw [VcTermSort.all_list_element_sorts_loop.body.eq_def] at continued
      exact sort_bool_accumulator_body_preserves_slice
        VcTermSort.is_list_element_sort state.1 next.1 state.2 next.2 continued)
    (by
      intro state next continued
      exact all_list_element_sorts_body_decreases
        state.1 next.1 state.2 next.2 continued)
    childrenTerminate

theorem all_list_element_sorts_terminates
    (elements : Slice VcTermSort.Sort)
    (childrenTerminate : ∀ child, child ∈ elements.val →
      Terminates (VcTermSort.is_list_element_sort child)) :
    Terminates (VcTermSort.all_list_element_sorts elements) := by
  rw [VcTermSort.all_list_element_sorts.eq_def]
  change Terminates
    (VcTermSort.all_list_element_sorts_loop ⟨elements, 0⟩ true)
  exact all_list_element_sorts_loop_terminates
    ⟨elements, 0⟩ true childrenTerminate

theorem all_finite_dict_key_sorts_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.is_finite_dict_key_sort child)) :
    Terminates (VcTermSort.all_finite_dict_key_sorts_loop iter result) := by
  unfold VcTermSort.all_finite_dict_key_sorts_loop
  exact sort_bool_accumulator_loop_terminates
    VcTermSort.is_finite_dict_key_sort
    VcTermSort.all_finite_dict_key_sorts_loop.body iter result
    (by
      intro state invariant
      rw [VcTermSort.all_finite_dict_key_sorts_loop.body.eq_def]
      exact sort_bool_accumulator_body_terminates
        VcTermSort.is_finite_dict_key_sort state.1 state.2 invariant)
    (by
      intro state next continued
      rw [VcTermSort.all_finite_dict_key_sorts_loop.body.eq_def] at continued
      exact sort_bool_accumulator_body_preserves_slice
        VcTermSort.is_finite_dict_key_sort state.1 next.1 state.2 next.2 continued)
    (by
      intro state next continued
      exact all_finite_dict_key_sorts_body_decreases
        state.1 next.1 state.2 next.2 continued)
    childrenTerminate

theorem all_finite_dict_key_sorts_terminates
    (elements : Slice VcTermSort.Sort)
    (childrenTerminate : ∀ child, child ∈ elements.val →
      Terminates (VcTermSort.is_finite_dict_key_sort child)) :
    Terminates (VcTermSort.all_finite_dict_key_sorts elements) := by
  rw [VcTermSort.all_finite_dict_key_sorts.eq_def]
  change Terminates
    (VcTermSort.all_finite_dict_key_sorts_loop ⟨elements, 0⟩ true)
  exact all_finite_dict_key_sorts_loop_terminates
    ⟨elements, 0⟩ true childrenTerminate

theorem all_finite_dict_value_sorts_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.is_finite_dict_value_sort child)) :
    Terminates (VcTermSort.all_finite_dict_value_sorts_loop iter result) := by
  unfold VcTermSort.all_finite_dict_value_sorts_loop
  exact sort_bool_accumulator_loop_terminates
    VcTermSort.is_finite_dict_value_sort
    VcTermSort.all_finite_dict_value_sorts_loop.body iter result
    (by
      intro state invariant
      rw [VcTermSort.all_finite_dict_value_sorts_loop.body.eq_def]
      exact sort_bool_accumulator_body_terminates
        VcTermSort.is_finite_dict_value_sort state.1 state.2 invariant)
    (by
      intro state next continued
      rw [VcTermSort.all_finite_dict_value_sorts_loop.body.eq_def] at continued
      exact sort_bool_accumulator_body_preserves_slice
        VcTermSort.is_finite_dict_value_sort state.1 next.1 state.2 next.2 continued)
    (by
      intro state next continued
      exact all_finite_dict_value_sorts_body_decreases
        state.1 next.1 state.2 next.2 continued)
    childrenTerminate

theorem all_finite_dict_value_sorts_terminates
    (elements : Slice VcTermSort.Sort)
    (childrenTerminate : ∀ child, child ∈ elements.val →
      Terminates (VcTermSort.is_finite_dict_value_sort child)) :
    Terminates (VcTermSort.all_finite_dict_value_sorts elements) := by
  rw [VcTermSort.all_finite_dict_value_sorts.eq_def]
  change Terminates
    (VcTermSort.all_finite_dict_value_sorts_loop ⟨elements, 0⟩ true)
  exact all_finite_dict_value_sorts_loop_terminates
    ⟨elements, 0⟩ true childrenTerminate

def SortPredicatesTerminate (sort : VcTermSort.Sort) : Prop :=
  Terminates (VcTermSort.is_list_element_sort sort) ∧
  Terminates (VcTermSort.is_finite_dict_key_sort sort) ∧
  Terminates (VcTermSort.is_finite_dict_value_sort sort) ∧
  Terminates (VcTermSort.is_variadic_tuple_element_sort sort)

theorem sort_predicates_terminate (sort : VcTermSort.Sort) :
    SortPredicatesTerminate sort := by
  refine VcTermSort.Sort.rec
    (motive_1 := SortPredicatesTerminate)
    (motive_2 := fun elements =>
      ∀ child, child ∈ elements → SortPredicatesTerminate child)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sort
  · constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      simp [Terminates]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        simp [Terminates]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp [Terminates]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp [Terminates]
  · constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      simp [Terminates]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        simp [Terminates]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp [Terminates]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp [Terminates]
  · constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      simp [Terminates]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        simp [Terminates]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp [Terminates]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp [Terminates]
  · constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      simp [Terminates]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        simp [Terminates]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp [Terminates]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp [Terminates]
  · constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      simp [Terminates]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        simp [Terminates]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp [Terminates]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp [Terminates]
  · constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      simp [Terminates]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        simp [Terminates]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp [Terminates]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp [Terminates]
  · constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      simp [Terminates]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        simp [Terminates]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp [Terminates]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp [Terminates]
  · constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      simp [Terminates]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        simp [Terminates]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp [Terminates]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp [Terminates]
  · constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      simp [Terminates]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        simp [Terminates]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp [Terminates]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp [Terminates]
  · intro elements childrenTerminate
    unfold VcTermSort.ModelVec at *
    have listTerminates := all_list_element_sorts_terminates
      (VcTermSort.ModelVec.deref elements) (by
        intro child member
        exact (childrenTerminate child (List.mem_of_mem_take member)).1)
    have keyTerminates := all_finite_dict_key_sorts_terminates
      (VcTermSort.ModelVec.deref elements) (by
        intro child member
        exact (childrenTerminate child (List.mem_of_mem_take member)).2.1)
    have valueTerminates := all_finite_dict_value_sorts_terminates
      (VcTermSort.ModelVec.deref elements) (by
        intro child member
        exact (childrenTerminate child (List.mem_of_mem_take member)).2.2.1)
    constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      cases observed : VcTermSort.all_list_element_sorts
          (VcTermSort.ModelVec.deref elements) with
      | div => simp [Terminates, observed] at listTerminates
      | fail error => simp [Terminates, observed]
      | ok value => cases value <;> simp [Terminates, observed]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        cases observed : VcTermSort.all_finite_dict_key_sorts
            (VcTermSort.ModelVec.deref elements) with
        | div => simp [Terminates, observed] at keyTerminates
        | fail error => simp [Terminates, observed]
        | ok value => cases value <;> simp [Terminates, observed]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          cases observed : VcTermSort.all_finite_dict_value_sorts
              (VcTermSort.ModelVec.deref elements) with
          | div => simp [Terminates, observed] at valueTerminates
          | fail error => simp [Terminates, observed]
          | ok value => cases value <;> simp [Terminates, observed]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          have tupleListTerminates :
              Terminates (VcTermSort.is_list_element_sort (.Tuple elements)) := by
            rw [VcTermSort.is_list_element_sort.eq_def]
            cases observed : VcTermSort.all_list_element_sorts
                (VcTermSort.ModelVec.deref elements) with
            | div => simp [Terminates, observed] at listTerminates
            | fail error => simp [Terminates, observed]
            | ok value => cases value <;> simp [Terminates, observed]
          cases observed : VcTermSort.is_list_element_sort (.Tuple elements) with
          | div => simp [Terminates, observed] at tupleListTerminates
          | fail error => simp [Terminates, observed]
          | ok value => cases value <;> simp [Terminates, observed]
  · intro element childTerminates
    have listTerminates :
        Terminates (VcTermSort.is_list_element_sort (.VariadicTuple element)) := by
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases observed : VcTermSort.is_list_element_sort element with
      | div => exact (childTerminates.1 observed).elim
      | fail error => simp [Terminates, observed]
      | ok value => cases value <;> simp [Terminates, observed]
    have keyTerminates :
        Terminates (VcTermSort.is_finite_dict_key_sort (.VariadicTuple element)) := by
      rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      cases observed : VcTermSort.is_finite_dict_key_sort element with
      | div => exact (childTerminates.2.1 observed).elim
      | fail error => simp [Terminates, observed]
      | ok value => cases value <;> simp [Terminates, observed]
    have valueTerminates :
        Terminates (VcTermSort.is_finite_dict_value_sort (.VariadicTuple element)) := by
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases observed : VcTermSort.is_finite_dict_value_sort element with
      | div => exact (childTerminates.2.2.1 observed).elim
      | fail error => simp [Terminates, observed]
      | ok value => cases value <;> simp [Terminates, observed]
    refine ⟨listTerminates, keyTerminates, valueTerminates, ?_⟩
    rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
    cases listObserved : VcTermSort.is_list_element_sort
        (.VariadicTuple element) with
    | div => simp [Terminates, listObserved] at listTerminates
    | fail error => simp [Terminates, listObserved]
    | ok listAccepted =>
        cases listAccepted with
        | true => simp [Terminates, listObserved]
        | false =>
            cases recursiveObserved :
                VcTermSort.is_variadic_tuple_element_sort element with
            | div => exact (childTerminates.2.2.2 recursiveObserved).elim
            | fail error => simp [Terminates, listObserved, recursiveObserved]
            | ok accepted => cases accepted <;>
                simp [Terminates, listObserved, recursiveObserved]
  · intro element childTerminates
    have listTerminates :
        Terminates (VcTermSort.is_list_element_sort (.List element)) := by
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases observed : VcTermSort.is_list_element_sort element with
      | div => exact (childTerminates.1 observed).elim
      | fail error => simp [Terminates, observed]
      | ok value => cases value <;> simp [Terminates, observed]
    have valueTerminates :
        Terminates (VcTermSort.is_finite_dict_value_sort (.List element)) := by
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases observed : VcTermSort.is_finite_dict_value_sort element with
      | div => exact (childTerminates.2.2.1 observed).elim
      | fail error => simp [Terminates, observed]
      | ok value => cases value <;> simp [Terminates, observed]
    refine ⟨listTerminates, ?_, valueTerminates, ?_⟩
    · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      simp [Terminates]
    · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
      cases observed : VcTermSort.is_list_element_sort (.List element) with
      | div => exact (listTerminates observed).elim
      | fail error => simp [Terminates, observed]
      | ok value => cases value <;> simp [Terminates, observed]
  · intro element childTerminates
    have listTerminates :
        Terminates (VcTermSort.is_list_element_sort (.Set element)) := by
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases observed : VcTermSort.is_finite_dict_key_sort element with
      | div => exact (childTerminates.2.1 observed).elim
      | fail error => simp [Terminates, observed]
      | ok value => cases value <;> simp [Terminates, observed]
    have valueTerminates :
        Terminates (VcTermSort.is_finite_dict_value_sort (.Set element)) := by
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases observed : VcTermSort.is_finite_dict_key_sort element with
      | div => exact (childTerminates.2.1 observed).elim
      | fail error => simp [Terminates, observed]
      | ok value => cases value <;> simp [Terminates, observed]
    refine ⟨listTerminates, ?_, valueTerminates, ?_⟩
    · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      simp [Terminates]
    · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
      cases observed : VcTermSort.is_list_element_sort (.Set element) with
      | div => exact (listTerminates observed).elim
      | fail error => simp [Terminates, observed]
      | ok value => cases value <;> simp [Terminates, observed]
  · intro key value keyTerminates valueTerminates
    have listTerminates :
        Terminates (VcTermSort.is_list_element_sort (.Dict key value)) := by
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases keyObserved : VcTermSort.is_finite_dict_key_sort key with
      | div => exact (keyTerminates.2.1 keyObserved).elim
      | fail error => simp [Terminates, keyObserved]
      | ok keyAccepted =>
          cases keyAccepted with
          | false => simp [Terminates, keyObserved]
          | true =>
              cases valueObserved : VcTermSort.is_list_element_sort value with
              | div => exact (valueTerminates.1 valueObserved).elim
              | fail error => simp [Terminates, keyObserved, valueObserved]
              | ok valueAccepted => cases valueAccepted <;>
                  simp [Terminates, keyObserved, valueObserved]
    have dictValueTerminates :
        Terminates (VcTermSort.is_finite_dict_value_sort (.Dict key value)) := by
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases keyObserved : VcTermSort.is_finite_dict_key_sort key with
      | div => exact (keyTerminates.2.1 keyObserved).elim
      | fail error => simp [Terminates, keyObserved]
      | ok keyAccepted =>
          cases keyAccepted with
          | false => simp [Terminates, keyObserved]
          | true =>
              cases valueObserved :
                  VcTermSort.is_finite_dict_value_sort value with
              | div => exact (valueTerminates.2.2.1 valueObserved).elim
              | fail error => simp [Terminates, keyObserved, valueObserved]
              | ok valueAccepted => cases valueAccepted <;>
                  simp [Terminates, keyObserved, valueObserved]
    refine ⟨listTerminates, ?_, dictValueTerminates, ?_⟩
    · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      simp [Terminates]
    · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
      cases observed : VcTermSort.is_list_element_sort (.Dict key value) with
      | div => exact (listTerminates observed).elim
      | fail error => simp [Terminates, observed]
      | ok accepted => cases accepted <;> simp [Terminates, observed]
  · intro key value keyTerminates valueTerminates
    have listTerminates :
        Terminates (VcTermSort.is_list_element_sort (.FiniteDict key value)) := by
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases keyObserved : VcTermSort.is_finite_dict_key_sort key with
      | div => exact (keyTerminates.2.1 keyObserved).elim
      | fail error => simp [Terminates, keyObserved]
      | ok keyAccepted =>
          cases keyAccepted with
          | false => simp [Terminates, keyObserved]
          | true =>
              cases valueObserved : VcTermSort.is_list_element_sort value with
              | div => exact (valueTerminates.1 valueObserved).elim
              | fail error => simp [Terminates, keyObserved, valueObserved]
              | ok valueAccepted => cases valueAccepted <;>
                  simp [Terminates, keyObserved, valueObserved]
    have dictValueTerminates :
        Terminates (VcTermSort.is_finite_dict_value_sort
          (.FiniteDict key value)) := by
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases keyObserved : VcTermSort.is_finite_dict_key_sort key with
      | div => exact (keyTerminates.2.1 keyObserved).elim
      | fail error => simp [Terminates, keyObserved]
      | ok keyAccepted =>
          cases keyAccepted with
          | false => simp [Terminates, keyObserved]
          | true =>
              cases valueObserved :
                  VcTermSort.is_finite_dict_value_sort value with
              | div => exact (valueTerminates.2.2.1 valueObserved).elim
              | fail error => simp [Terminates, keyObserved, valueObserved]
              | ok valueAccepted => cases valueAccepted <;>
                  simp [Terminates, keyObserved, valueObserved]
    refine ⟨listTerminates, ?_, dictValueTerminates, ?_⟩
    · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      simp [Terminates]
    · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
      cases observed :
          VcTermSort.is_list_element_sort (.FiniteDict key value) with
      | div => exact (listTerminates observed).elim
      | fail error => simp [Terminates, observed]
      | ok accepted => cases accepted <;> simp [Terminates, observed]
  · intro key keyTerminates
    constructor
    · rw [VcTermSort.is_list_element_sort.eq_def]
      simp [Terminates]
    · constructor
      · rw [VcTermSort.is_finite_dict_key_sort.eq_def]
        simp [Terminates]
      · constructor
        · rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp [Terminates]
        · rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp [Terminates]
  · intro child member
    simp at member
  · intro head tail headTerminates tailTerminates child member
    simp at member
    rcases member with rfl | member
    · exact headTerminates
    · exact tailTerminates child member

theorem is_list_element_sort_terminates (sort : VcTermSort.Sort) :
    Terminates (VcTermSort.is_list_element_sort sort) :=
  (sort_predicates_terminate sort).1

theorem is_finite_dict_key_sort_terminates (sort : VcTermSort.Sort) :
    Terminates (VcTermSort.is_finite_dict_key_sort sort) :=
  (sort_predicates_terminate sort).2.1

theorem is_finite_dict_value_sort_terminates (sort : VcTermSort.Sort) :
    Terminates (VcTermSort.is_finite_dict_value_sort sort) :=
  (sort_predicates_terminate sort).2.2.1

theorem is_variadic_tuple_element_sort_terminates (sort : VcTermSort.Sort) :
    Terminates (VcTermSort.is_variadic_tuple_element_sort sort) :=
  (sort_predicates_terminate sort).2.2.2

theorem require_all_sorts_body_terminates
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates
      (VcTermSort.require_all_sorts_loop.body expected context iter result) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail error =>
      simp [Terminates, VcTermSort.require_all_sorts_loop.body, observed]
  | ok pair =>
      obtain ⟨maybeValue, next⟩ := pair
      cases maybeValue with
      | none =>
          simp [Terminates, VcTermSort.require_all_sorts_loop.body, observed]
      | some value =>
          have member := (slice_iterator_next_some_member
            iter next value observed).1
          cases result with
          | Err current =>
              simp [Terminates, VcTermSort.require_all_sorts_loop.body,
                observed, core.result.Result.is_ok]
          | Ok checkedUnit =>
              have requiredTerminates :=
                require_sort_terminates_of_term_sort_terminates
                  value expected context (childrenTerminate value member)
              rw [VcTermSort.require_all_sorts_loop.body]
              rw [observed]
              change Terminates (do
                let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone expected
                let checked ← VcTermSort.require_sort value cloned context
                ok (ControlFlow.cont (next, checked)))
              rw [sort_clone_exact]
              cases requiredObserved :
                  VcTermSort.require_sort value expected context with
              | div =>
                  simp [Terminates, requiredObserved] at requiredTerminates
              | fail error => simp [Terminates, requiredObserved]
              | ok checked => simp [Terminates, requiredObserved]

theorem require_all_sorts_body_preserves_slice
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.require_all_sorts_loop.body expected context iter result =
      .ok (.cont (next, nextResult))) :
    next.slice = iter.slice := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.require_all_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.require_all_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeValue, advanced⟩ := pair
      cases maybeValue with
      | none =>
          simp [VcTermSort.require_all_sorts_loop.body, observed] at continued
      | some value =>
          have advancedSlice := (slice_iterator_next_some_member
            iter advanced value observed).2
          have advancedEq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSort.require_all_sorts_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSort.require_all_sorts_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSort.require_all_sorts_loop.body, observed,
                      isOkObserved] at continued
                    simp_all
                | true =>
                    simp [VcTermSort.require_all_sorts_loop.body, observed,
                      isOkObserved] at continued
                    exact two_bind_cont_iterator_first
                      (VcTermSort.Sort.Insts.CoreCloneClone.clone expected)
                      (fun cloned => VcTermSort.require_sort value cloned context)
                      advanced next nextResult continued
          subst next
          exact advancedSlice

theorem require_all_sorts_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates
      (VcTermSort.require_all_sorts_loop iter expected context result) := by
  unfold VcTermSort.require_all_sorts_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter VcTermSort.Term ×
        core.result.Result Unit VcTermSort.SortError =>
      VcTermSort.require_all_sorts_loop.body expected context state.1 state.2)
    (fun state => ∀ child, child ∈ state.1.slice.val →
      Terminates (VcTermSort.Term.sort_typed child))
    (fun state => sliceIteratorRemaining state.1)
  · intro state stateInvariant
    exact require_all_sorts_body_terminates expected context
      state.1 state.2 stateInvariant
  · intro state next stateInvariant continued child member
    apply stateInvariant child
    have slicesEqual := require_all_sorts_body_preserves_slice
      expected context state.1 next.1 state.2 next.2 continued
    simpa [slicesEqual] using member
  · intro state next continued
    exact require_all_sorts_body_decreases expected context
      state.1 next.1 state.2 next.2 continued
  · exact childrenTerminate
  · simp [sliceIteratorRemaining]

theorem require_all_sorts_terminates
    (values : Slice VcTermSort.Term)
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (childrenTerminate : ∀ child, child ∈ values.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.require_all_sorts values expected context) := by
  rw [VcTermSort.require_all_sorts.eq_def]
  change Terminates (VcTermSort.require_all_sorts_loop
    ⟨values, 0⟩ expected context (core.result.Result.Ok ()))
  exact require_all_sorts_loop_terminates
    ⟨values, 0⟩ expected context (core.result.Result.Ok ())
    childrenTerminate

theorem require_variadic_tuple_element_sorts_body_terminates
    (expected : VcTermSort.Sort)
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.require_variadic_tuple_element_sorts_loop.body
      expected iter result) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail error =>
      simp [Terminates,
        VcTermSort.require_variadic_tuple_element_sorts_loop.body, observed]
  | ok pair =>
      obtain ⟨maybeValue, next⟩ := pair
      cases maybeValue with
      | none =>
          simp [Terminates,
            VcTermSort.require_variadic_tuple_element_sorts_loop.body, observed]
      | some value =>
          have member := (slice_iterator_next_some_member
            iter next value observed).1
          cases result with
          | Err current =>
              simp [Terminates,
                VcTermSort.require_variadic_tuple_element_sorts_loop.body,
                observed, core.result.Result.is_ok]
          | Ok checkedUnit =>
              rw [VcTermSort.require_variadic_tuple_element_sorts_loop.body]
              rw [observed]
              change Terminates (do
                let r ← VcTermSort.Term.sort_typed value
                match r with
                | core.result.Result.Ok actual =>
                    let equal ←
                      VcTermSort.Sort.Insts.CoreCmpPartialEqSort.eq
                        actual expected
                    if equal then
                      ok (ControlFlow.cont (next, core.result.Result.Ok ()))
                    else
                      let cloned ←
                        VcTermSort.Sort.Insts.CoreCloneClone.clone expected
                      ok (ControlFlow.cont (next, core.result.Result.Err
                        (VcTermSort.SortError.VariadicTupleElementSortMismatch
                          cloned actual)))
                | core.result.Result.Err error =>
                    ok (ControlFlow.cont (next, core.result.Result.Err error)))
              have valueTerminates := childrenTerminate value member
              cases valueObserved : VcTermSort.Term.sort_typed value with
              | div => simp [Terminates, valueObserved] at valueTerminates
              | fail error =>
                  simp [Terminates,
                    VcTermSort.require_variadic_tuple_element_sorts_loop.body,
                    observed, core.result.Result.is_ok, valueObserved]
              | ok checked =>
                  cases checked with
                  | Err error =>
                      simp [Terminates,
                        VcTermSort.require_variadic_tuple_element_sorts_loop.body,
                        observed, core.result.Result.is_ok, valueObserved]
                  | Ok actual =>
                      simp only [bind_tc_ok]
                      exact result_bind_terminates
                        (VcTermSort.Sort.Insts.CoreCmpPartialEqSort.eq
                          actual expected)
                        (fun equal =>
                          if equal then
                            ok (ControlFlow.cont
                              (next, core.result.Result.Ok ()))
                          else do
                            let cloned ←
                              VcTermSort.Sort.Insts.CoreCloneClone.clone expected
                            ok (ControlFlow.cont
                              (next, core.result.Result.Err
                                (VcTermSort.SortError.VariadicTupleElementSortMismatch
                                  cloned actual))))
                        (sort_partial_eq_terminates actual expected)
                        (by
                          intro equal
                          cases equal with
                          | true => simp [Terminates]
                          | false =>
                              simp only [Bool.false_eq, ↓reduceIte]
                              exact result_bind_terminates
                                (VcTermSort.Sort.Insts.CoreCloneClone.clone
                                  expected)
                                (fun cloned => ok (ControlFlow.cont
                                  (next, core.result.Result.Err
                                    (VcTermSort.SortError.VariadicTupleElementSortMismatch
                                      cloned actual))))
                                (sort_clone_terminates expected)
                                (by intro cloned; simp [Terminates]))

theorem require_variadic_tuple_element_sorts_body_preserves_slice
    (expected : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.require_variadic_tuple_element_sorts_loop.body
      expected iter result = .ok (.cont (next, nextResult))) :
    next.slice = iter.slice := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body,
        observed] at continued
  | div =>
      simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body,
        observed] at continued
  | ok pair =>
      obtain ⟨maybeValue, advanced⟩ := pair
      cases maybeValue with
      | none =>
          simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body,
            observed] at continued
      | some value =>
          have advancedSlice := (slice_iterator_next_some_member
            iter advanced value observed).2
          have advancedEq : advanced = next := by
            simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body,
              observed] at continued
            simp only [Bind.bind, Std.bind] at continued
            all_goals repeat' split at continued
            all_goals
              have mapped := congrArg continuationIterator continued
              simp [continuationIterator] at mapped <;> assumption
          subst next
          exact advancedSlice

theorem require_variadic_tuple_element_sorts_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (expected : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.require_variadic_tuple_element_sorts_loop
      iter expected result) := by
  unfold VcTermSort.require_variadic_tuple_element_sorts_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter VcTermSort.Term ×
        core.result.Result Unit VcTermSort.SortError =>
      VcTermSort.require_variadic_tuple_element_sorts_loop.body
        expected state.1 state.2)
    (fun state => ∀ child, child ∈ state.1.slice.val →
      Terminates (VcTermSort.Term.sort_typed child))
    (fun state => sliceIteratorRemaining state.1)
  · intro state invariant
    exact require_variadic_tuple_element_sorts_body_terminates
      expected state.1 state.2 invariant
  · intro state next invariant continued child member
    apply invariant child
    have slicesEqual := require_variadic_tuple_element_sorts_body_preserves_slice
      expected state.1 next.1 state.2 next.2 continued
    simpa [slicesEqual] using member
  · intro state next continued
    exact require_variadic_tuple_element_sorts_body_decreases expected
      state.1 next.1 state.2 next.2 continued
  · exact childrenTerminate
  · simp [sliceIteratorRemaining]

theorem require_variadic_tuple_element_sorts_terminates
    (values : Slice VcTermSort.Term) (expected : VcTermSort.Sort)
    (childrenTerminate : ∀ child, child ∈ values.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.require_variadic_tuple_element_sorts
      values expected) := by
  rw [VcTermSort.require_variadic_tuple_element_sorts.eq_def]
  change Terminates (VcTermSort.require_variadic_tuple_element_sorts_loop
    ⟨values, 0⟩ expected (core.result.Result.Ok ()))
  exact require_variadic_tuple_element_sorts_loop_terminates
    ⟨values, 0⟩ expected (core.result.Result.Ok ()) childrenTerminate

theorem model_vec_deref_children_terminate_of_smaller
    (values : VcTermSort.ModelVec VcTermSort.Term)
    (parent : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child parent →
        Terminates (VcTermSort.Term.sort_typed child))
    (childrenSmaller : ∀ child,
      child ∈ (show List VcTermSort.Term from values) →
        TermStrictlySmaller child parent) :
    ∀ child, child ∈ (VcTermSort.ModelVec.deref values).val →
      Terminates (VcTermSort.Term.sort_typed child) := by
  intro child member
  apply smallerTerminates child
  apply childrenSmaller child
  change child ∈ List.take Usize.max
    (show List VcTermSort.Term from values) at member
  exact List.mem_of_mem_take member

theorem model_vec_push_terminates {T : Type}
    (values : VcTermSort.ModelVec T) (value : T)
    (bounded : ModelVecBounded values) :
    Terminates (VcTermSort.ModelVec.push values value) := by
  unfold ModelVecBounded at bounded
  rcases Nat.lt_or_eq_of_le bounded with below | full
  · rw [VcTermSort.ModelVec.push_exact values value below]
    simp [Terminates]
  · rw [VcTermSort.ModelVec.push_at_capacity_fails values value full]
    simp [Terminates]

theorem model_vec_push_ok_bounded {T : Type}
    (values updated : VcTermSort.ModelVec T) (value : T)
    (bounded : ModelVecBounded values)
    (observed : VcTermSort.ModelVec.push values value = .ok updated) :
    ModelVecBounded updated := by
  unfold ModelVecBounded at bounded ⊢
  rcases Nat.lt_or_eq_of_le bounded with below | full
  · rw [VcTermSort.ModelVec.push_exact values value below] at observed
    simp only [Result.ok.injEq] at observed
    subst updated
    simp
    omega
  · rw [VcTermSort.ModelVec.push_at_capacity_fails values value full] at observed
    simp at observed

theorem collect_sorts_body_terminates
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (sorts : VcTermSort.ModelVec VcTermSort.Sort)
    (error : Option VcTermSort.SortError)
    (sortsBounded : ModelVecBounded sorts)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.collect_sorts_loop.body iter sorts error) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail iteratorError =>
      simp [Terminates, VcTermSort.collect_sorts_loop.body, observed]
  | ok pair =>
      obtain ⟨maybeValue, next⟩ := pair
      cases maybeValue with
      | none =>
          simp [Terminates, VcTermSort.collect_sorts_loop.body, observed]
      | some value =>
          have member := (slice_iterator_next_some_member
            iter next value observed).1
          cases error with
          | some current =>
              simp [Terminates, VcTermSort.collect_sorts_loop.body, observed]
          | none =>
              have sortTerminates := childrenTerminate value member
              cases sortObserved : VcTermSort.Term.sort_typed value with
              | div => simp [Terminates, sortObserved] at sortTerminates
              | fail sortError =>
                  simp [Terminates, VcTermSort.collect_sorts_loop.body,
                    observed, sortObserved]
              | ok checked =>
                  cases checked with
                  | Err current =>
                      simp [Terminates, VcTermSort.collect_sorts_loop.body,
                        observed, sortObserved]
                  | Ok sort =>
                      have pushTerminates := model_vec_push_terminates
                        sorts sort sortsBounded
                      cases pushObserved : VcTermSort.ModelVec.push sorts sort with
                      | div => simp [Terminates, pushObserved] at pushTerminates
                      | fail pushError =>
                          simp [Terminates, VcTermSort.collect_sorts_loop.body,
                            observed, sortObserved, pushObserved]
                      | ok updated =>
                          simp [Terminates, VcTermSort.collect_sorts_loop.body,
                            observed, sortObserved, pushObserved]

theorem collect_sorts_body_preserves_slice
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (sorts nextSorts : VcTermSort.ModelVec VcTermSort.Sort)
    (error nextError : Option VcTermSort.SortError)
    (continued : VcTermSort.collect_sorts_loop.body iter sorts error =
      .ok (.cont (next, nextSorts, nextError))) :
    next.slice = iter.slice := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSort.collect_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.collect_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeValue, advanced⟩ := pair
      cases maybeValue with
      | none =>
          simp [VcTermSort.collect_sorts_loop.body, observed] at continued
      | some value =>
          have advancedSlice := (slice_iterator_next_some_member
            iter advanced value observed).2
          have advancedEq : advanced = next := by
            cases error with
            | some current =>
                simp [VcTermSort.collect_sorts_loop.body, observed] at continued
                exact continued.1
            | none =>
                cases sortObserved : VcTermSort.Term.sort_typed value with
                | fail sortError =>
                    simp [VcTermSort.collect_sorts_loop.body, observed,
                      sortObserved] at continued
                | div =>
                    simp [VcTermSort.collect_sorts_loop.body, observed,
                      sortObserved] at continued
                | ok checked =>
                    cases checked with
                    | Err current =>
                        simp [VcTermSort.collect_sorts_loop.body, observed,
                          sortObserved] at continued
                        exact continued.1
                    | Ok sort =>
                        simp [VcTermSort.collect_sorts_loop.body, observed,
                          sortObserved] at continued
                        exact one_bind_cont_iterator_first
                          (VcTermSort.ModelVec.push sorts sort)
                          (fun updated => (updated, none))
                          advanced next (nextSorts, nextError) continued
          subst next
          exact advancedSlice

theorem collect_sorts_body_preserves_bounded
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (sorts nextSorts : VcTermSort.ModelVec VcTermSort.Sort)
    (error nextError : Option VcTermSort.SortError)
    (sortsBounded : ModelVecBounded sorts)
    (continued : VcTermSort.collect_sorts_loop.body iter sorts error =
      .ok (.cont (next, nextSorts, nextError))) :
    ModelVecBounded nextSorts := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSort.collect_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.collect_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeValue, advanced⟩ := pair
      cases maybeValue with
      | none =>
          simp [VcTermSort.collect_sorts_loop.body, observed] at continued
      | some value =>
          cases error with
          | some current =>
              simp [VcTermSort.collect_sorts_loop.body, observed] at continued
              simpa [continued.2.1] using sortsBounded
          | none =>
              cases sortObserved : VcTermSort.Term.sort_typed value with
              | fail sortError =>
                  simp [VcTermSort.collect_sorts_loop.body, observed,
                    sortObserved] at continued
              | div =>
                  simp [VcTermSort.collect_sorts_loop.body, observed,
                    sortObserved] at continued
              | ok checked =>
                  cases checked with
                  | Err current =>
                      simp [VcTermSort.collect_sorts_loop.body, observed,
                        sortObserved] at continued
                      simpa [continued.2.1] using sortsBounded
                  | Ok sort =>
                      cases pushObserved : VcTermSort.ModelVec.push sorts sort with
                      | div =>
                          simp [VcTermSort.collect_sorts_loop.body, observed,
                            sortObserved, pushObserved] at continued
                      | fail pushError =>
                          simp [VcTermSort.collect_sorts_loop.body, observed,
                            sortObserved, pushObserved] at continued
                      | ok updated =>
                          simp [VcTermSort.collect_sorts_loop.body, observed,
                            sortObserved, pushObserved] at continued
                          rw [← continued.2.1]
                          exact model_vec_push_ok_bounded
                            sorts updated sort sortsBounded pushObserved

theorem collect_sorts_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (sorts : VcTermSort.ModelVec VcTermSort.Sort)
    (error : Option VcTermSort.SortError)
    (sortsBounded : ModelVecBounded sorts)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.collect_sorts_loop iter sorts error) := by
  unfold VcTermSort.collect_sorts_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter VcTermSort.Term ×
        VcTermSort.ModelVec VcTermSort.Sort × Option VcTermSort.SortError =>
      VcTermSort.collect_sorts_loop.body state.1 state.2.1 state.2.2)
    (fun state =>
      (∀ child, child ∈ state.1.slice.val →
        Terminates (VcTermSort.Term.sort_typed child)) ∧
      ModelVecBounded state.2.1)
    (fun state => sliceIteratorRemaining state.1)
  · intro state stateInvariant
    exact collect_sorts_body_terminates state.1 state.2.1 state.2.2
      stateInvariant.2 stateInvariant.1
  · intro state next stateInvariant continued
    constructor
    · intro child member
      apply stateInvariant.1 child
      have slicesEqual := collect_sorts_body_preserves_slice
        state.1 next.1 state.2.1 next.2.1 state.2.2 next.2.2 continued
      simpa [slicesEqual] using member
    · exact collect_sorts_body_preserves_bounded
        state.1 next.1 state.2.1 next.2.1 state.2.2 next.2.2
        stateInvariant.2 continued
  · intro state next continued
    exact collect_sorts_body_decreases state.1 next.1 state.2.1 next.2.1
      state.2.2 next.2.2 continued
  · exact ⟨childrenTerminate, sortsBounded⟩
  · simp [sliceIteratorRemaining]

theorem collect_sorts_terminates
    (values : Slice VcTermSort.Term)
    (childrenTerminate : ∀ child, child ∈ values.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.collect_sorts values) := by
  rw [VcTermSort.collect_sorts.eq_def]
  change Terminates (do
    let output ← VcTermSort.collect_sorts_loop
      ⟨values, 0⟩ (VcTermSort.ModelVec.with_capacity VcTermSort.Sort
        (Slice.len values)) none
    match output.2 with
    | none => ok (core.result.Result.Ok output.1)
    | some error => ok (core.result.Result.Err error))
  have loopTerminates := collect_sorts_loop_terminates
    ⟨values, 0⟩
    (VcTermSort.ModelVec.with_capacity VcTermSort.Sort
      (Slice.len values)) none
    (model_vec_with_capacity_bounded (Slice.len values)) childrenTerminate
  cases observed : VcTermSort.collect_sorts_loop
      ⟨values, 0⟩
      (VcTermSort.ModelVec.with_capacity VcTermSort.Sort
        (Slice.len values)) none with
  | div => simp [Terminates, observed] at loopTerminates
  | fail loopError => simp [Terminates, observed]
  | ok output =>
      obtain ⟨sorts, error⟩ := output
      cases error <;> simp [Terminates, observed]

theorem list_anyM_pure_terminates {T : Type}
    (predicate : T → Bool) (values : List T) :
    Terminates (List.anyM (fun value => ok (predicate value)) values) := by
  induction values with
  | nil => simp [Terminates, List.anyM]
  | cons head tail inductionHypothesis =>
      simp only [List.anyM]
      cases predicate head
      · exact inductionHypothesis
      · simp [Terminates]

theorem validate_int_enum_descriptor_body_terminates
    (iter : core.slice.iter.Iter (String × Std.I64))
    (names : alloc.collections.btree.set.BTreeSet String Global)
    (values : alloc.collections.btree.set.BTreeSet Std.I64 Global)
    (valid : Bool) :
    Terminates
      (VcTermSort.validate_int_enum_descriptor_loop.body
        iter names values valid) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail iteratorError =>
      simp [Terminates,
        VcTermSort.validate_int_enum_descriptor_loop.body, observed]
  | ok pair =>
      obtain ⟨maybeEntry, next⟩ := pair
      cases maybeEntry with
      | none =>
          simp [Terminates,
            VcTermSort.validate_int_enum_descriptor_loop.body, observed]
      | some entry =>
          obtain ⟨memberName, value⟩ := entry
          cases valid with
          | false =>
              simp [Terminates,
                VcTermSort.validate_int_enum_descriptor_loop.body, observed]
          | true =>
              by_cases empty : memberName = ""
              · simp [Terminates,
                  VcTermSort.validate_int_enum_descriptor_loop.body, observed,
                  alloc.string.String.is_empty, empty]
              · have namesInsertTerminates : Terminates
                    (alloc.collections.btree.set.BTreeSet.insert
                      core.core.clone.CloneGlobal
                      alloc.string.String.Insts.CoreCmpOrd names memberName) := by
                  have anyTerminates : Terminates
                      (List.anyM
                        (fun existing =>
                          alloc.string.String.Insts.CoreCmpPartialEqString.eq
                            existing memberName) names) := by
                    simpa [alloc.string.String.Insts.CoreCmpPartialEqString.eq]
                      using list_anyM_pure_terminates
                        (fun existing => existing == memberName) names
                  cases anyObserved : List.anyM
                      (fun existing =>
                        alloc.string.String.Insts.CoreCmpPartialEqString.eq
                          existing memberName) names with
                  | div => simp [Terminates, anyObserved] at anyTerminates
                  | fail anyError =>
                      simp [Terminates,
                        alloc.collections.btree.set.BTreeSet.insert,
                        anyObserved]
                  | ok present =>
                      simp [Terminates,
                        alloc.collections.btree.set.BTreeSet.insert,
                        anyObserved]
                cases namesObserved :
                    alloc.collections.btree.set.BTreeSet.insert
                      core.core.clone.CloneGlobal
                      alloc.string.String.Insts.CoreCmpOrd names memberName with
                | div => simp [Terminates, namesObserved] at namesInsertTerminates
                | fail insertError =>
                    simp [Terminates,
                      VcTermSort.validate_int_enum_descriptor_loop.body,
                      observed, alloc.string.String.is_empty, empty,
                      alloc.string.String.Insts.CoreCloneClone.clone,
                      namesObserved]
                | ok namesResult =>
                    obtain ⟨nameFresh, updatedNames⟩ := namesResult
                    cases nameFresh with
                    | false =>
                        simp [Terminates,
                          VcTermSort.validate_int_enum_descriptor_loop.body,
                          observed, alloc.string.String.is_empty, empty,
                          alloc.string.String.Insts.CoreCloneClone.clone,
                          namesObserved]
                    | true =>
                        have valuesInsertTerminates : Terminates
                            (alloc.collections.btree.set.BTreeSet.insert
                              core.core.clone.CloneGlobal core.cmp.OrdI64
                              values value) := by
                          have anyTerminates : Terminates
                              (List.anyM
                                (fun existing => ok (decide (existing = value)))
                                values) := by
                            exact list_anyM_pure_terminates
                              (fun existing => decide (existing = value)) values
                          cases anyObserved : List.anyM
                              (fun existing => ok (decide (existing = value)))
                              values with
                          | div =>
                              simp [Terminates, anyObserved] at anyTerminates
                          | fail anyError =>
                              simp [Terminates,
                                alloc.collections.btree.set.BTreeSet.insert,
                                anyObserved]
                          | ok present =>
                              simp [Terminates,
                                alloc.collections.btree.set.BTreeSet.insert,
                                anyObserved]
                        cases valuesObserved :
                            alloc.collections.btree.set.BTreeSet.insert
                              core.core.clone.CloneGlobal core.cmp.OrdI64
                              values value with
                        | div =>
                            simp [Terminates, valuesObserved] at valuesInsertTerminates
                        | fail insertError =>
                            simp [Terminates,
                              VcTermSort.validate_int_enum_descriptor_loop.body,
                              observed, alloc.string.String.is_empty, empty,
                              alloc.string.String.Insts.CoreCloneClone.clone,
                              namesObserved, valuesObserved]
                        | ok valuesResult =>
                            obtain ⟨valueFresh, updatedValues⟩ := valuesResult
                            simp [Terminates,
                              VcTermSort.validate_int_enum_descriptor_loop.body,
                              observed, alloc.string.String.is_empty, empty,
                              alloc.string.String.Insts.CoreCloneClone.clone,
                              namesObserved, valuesObserved]

theorem validate_int_enum_descriptor_loop_terminates
    (iter : core.slice.iter.Iter (String × Std.I64))
    (names : alloc.collections.btree.set.BTreeSet String Global)
    (values : alloc.collections.btree.set.BTreeSet Std.I64 Global)
    (valid : Bool) :
    Terminates
      (VcTermSort.validate_int_enum_descriptor_loop iter names values valid) := by
  unfold VcTermSort.validate_int_enum_descriptor_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter (String × Std.I64) ×
        alloc.collections.btree.set.BTreeSet String Global ×
        alloc.collections.btree.set.BTreeSet Std.I64 Global × Bool =>
      VcTermSort.validate_int_enum_descriptor_loop.body
        state.1 state.2.1 state.2.2.1 state.2.2.2)
    (fun _ => True)
    (fun state => sliceIteratorRemaining state.1)
  · intro state _
    exact validate_int_enum_descriptor_body_terminates
      state.1 state.2.1 state.2.2.1 state.2.2.2
  · intro _ _ _ _
    trivial
  · intro state next continued
    exact validate_int_enum_descriptor_body_decreases
      state.1 next.1 state.2.1 next.2.1 state.2.2.1 next.2.2.1
      state.2.2.2 next.2.2.2 continued
  · trivial
  · simp [sliceIteratorRemaining]

theorem validate_int_enum_descriptor_terminates
    (descriptor : VcTermSort.IntEnumDescriptor) :
    Terminates (VcTermSort.validate_int_enum_descriptor descriptor) := by
  unfold VcTermSort.validate_int_enum_descriptor
  simp only [alloc.string.String.is_empty]
  cases descriptor.class.isEmpty
  · simp only [VcTermSort.ModelVec.is_empty]
    cases descriptor.members.isEmpty
    · have loopTerminates := validate_int_enum_descriptor_loop_terminates
          ⟨VcTermSort.ModelVec.deref descriptor.members, 0⟩ [] [] true
      simp only [
        alloc.collections.btree.set.BTreeSetTGlobal.new,
        SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter]
      cases observed : VcTermSort.validate_int_enum_descriptor_loop
          ⟨VcTermSort.ModelVec.deref descriptor.members, 0⟩ [] [] true with
      | div => simp [Terminates, observed] at loopTerminates
      | fail loopError => simp [Terminates, observed]
      | ok valid =>
          cases valid <;>
            simp [Terminates, observed,
              alloc.collections.btree.set.BTreeSetTGlobal.new,
              SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter,
              Str.Insts.AllocBorrowToOwnedString.to_owned]
    · simp [Terminates,
        Str.Insts.AllocBorrowToOwnedString.to_owned]
  · simp [Terminates,
      Str.Insts.AllocBorrowToOwnedString.to_owned]

theorem require_predicate_argument_sorts_body_terminates
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates
      (VcTermSort.require_predicate_argument_sorts_loop.body iter result) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail iteratorError =>
      simp [Terminates,
        VcTermSort.require_predicate_argument_sorts_loop.body, observed]
  | ok pair =>
      obtain ⟨maybeArgument, next⟩ := pair
      cases maybeArgument with
      | none =>
          simp [Terminates,
            VcTermSort.require_predicate_argument_sorts_loop.body, observed]
      | some argument =>
          have member := (slice_iterator_next_some_member
            iter next argument observed).1
          cases result with
          | Err current =>
              simp [Terminates,
                VcTermSort.require_predicate_argument_sorts_loop.body,
                observed, core.result.Result.is_ok]
          | Ok checkedUnit =>
              have sortTerminates := childrenTerminate argument member
              cases sortObserved : VcTermSort.Term.sort_typed argument with
              | div => simp [Terminates, sortObserved] at sortTerminates
              | fail sortError =>
                  simp [Terminates,
                    VcTermSort.require_predicate_argument_sorts_loop.body,
                    observed, core.result.Result.is_ok, sortObserved]
              | ok checked =>
                  cases checked with
                  | Err current =>
                      simp [Terminates,
                        VcTermSort.require_predicate_argument_sorts_loop.body,
                        observed, core.result.Result.is_ok, sortObserved]
                  | Ok sort =>
                      cases sort <;>
                        simp [Terminates,
                          VcTermSort.require_predicate_argument_sorts_loop.body,
                          observed, core.result.Result.is_ok, sortObserved,
                          Str.Insts.AllocBorrowToOwnedString.to_owned]

theorem require_predicate_argument_sorts_body_preserves_slice
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued :
      VcTermSort.require_predicate_argument_sorts_loop.body iter result =
        .ok (.cont (next, nextResult))) :
    next.slice = iter.slice := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSort.require_predicate_argument_sorts_loop.body,
        observed] at continued
  | div =>
      simp [VcTermSort.require_predicate_argument_sorts_loop.body,
        observed] at continued
  | ok pair =>
      obtain ⟨maybeArgument, advanced⟩ := pair
      cases maybeArgument with
      | none =>
          simp [VcTermSort.require_predicate_argument_sorts_loop.body,
            observed] at continued
      | some argument =>
          have advancedSlice := (slice_iterator_next_some_member
            iter advanced argument observed).2
          have advancedEq : advanced = next := by
            cases result with
            | Err current =>
                simp [VcTermSort.require_predicate_argument_sorts_loop.body,
                  observed, core.result.Result.is_ok] at continued
                exact continued.1
            | Ok checkedUnit =>
                cases sortObserved : VcTermSort.Term.sort_typed argument with
                | fail sortError =>
                    simp [VcTermSort.require_predicate_argument_sorts_loop.body,
                      observed, core.result.Result.is_ok, sortObserved] at continued
                | div =>
                    simp [VcTermSort.require_predicate_argument_sorts_loop.body,
                      observed, core.result.Result.is_ok, sortObserved] at continued
                | ok checked =>
                    cases checked with
                    | Err current =>
                        simp [VcTermSort.require_predicate_argument_sorts_loop.body,
                          observed, core.result.Result.is_ok,
                          sortObserved] at continued
                        exact continued.1
                    | Ok sort =>
                        cases sort <;>
                          simp [VcTermSort.require_predicate_argument_sorts_loop.body,
                            observed, core.result.Result.is_ok, sortObserved,
                            Str.Insts.AllocBorrowToOwnedString.to_owned] at continued <;>
                          exact continued.1
          subst next
          exact advancedSlice

theorem require_predicate_argument_sorts_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenTerminate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates
      (VcTermSort.require_predicate_argument_sorts_loop iter result) := by
  unfold VcTermSort.require_predicate_argument_sorts_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter VcTermSort.Term ×
        core.result.Result Unit VcTermSort.SortError =>
      VcTermSort.require_predicate_argument_sorts_loop.body state.1 state.2)
    (fun state => ∀ child, child ∈ state.1.slice.val →
      Terminates (VcTermSort.Term.sort_typed child))
    (fun state => sliceIteratorRemaining state.1)
  · intro state stateInvariant
    exact require_predicate_argument_sorts_body_terminates
      state.1 state.2 stateInvariant
  · intro state next stateInvariant continued child member
    apply stateInvariant child
    have slicesEqual := require_predicate_argument_sorts_body_preserves_slice
      state.1 next.1 state.2 next.2 continued
    simpa [slicesEqual] using member
  · intro state next continued
    exact require_predicate_argument_sorts_body_decreases
      state.1 next.1 state.2 next.2 continued
  · exact childrenTerminate
  · simp [sliceIteratorRemaining]

theorem require_predicate_argument_sorts_terminates
    (arguments : Slice VcTermSort.Term)
    (childrenTerminate : ∀ child, child ∈ arguments.val →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.require_predicate_argument_sorts arguments) := by
  rw [VcTermSort.require_predicate_argument_sorts.eq_def]
  change Terminates
    (VcTermSort.require_predicate_argument_sorts_loop
      ⟨arguments, 0⟩ (core.result.Result.Ok ()))
  exact require_predicate_argument_sorts_loop_terminates
    ⟨arguments, 0⟩ (core.result.Result.Ok ()) childrenTerminate

theorem require_permission_transfer_amounts_body_terminates
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result : core.result.Result Unit VcTermSort.SortError)
    (receiversTerminate : ∀ amount, amount ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed amount.receiver)) :
    Terminates
      (VcTermSort.require_permission_transfer_amounts_loop.body iter result) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail iteratorError =>
      simp [Terminates,
        VcTermSort.require_permission_transfer_amounts_loop.body, observed]
  | ok pair =>
      obtain ⟨maybeAmount, next⟩ := pair
      cases maybeAmount with
      | none =>
          simp [Terminates,
            VcTermSort.require_permission_transfer_amounts_loop.body, observed]
      | some amount =>
          have member := (slice_iterator_next_some_member
            iter next amount observed).1
          cases result with
          | Err current =>
              simp [Terminates,
                VcTermSort.require_permission_transfer_amounts_loop.body,
                observed, core.result.Result.is_ok]
          | Ok checkedUnit =>
              have requiredTerminates :=
                require_sort_terminates_of_term_sort_terminates
                  amount.receiver .Reference
                  VcTermSort.SortContext.PermissionTransferReceiver
                  (receiversTerminate amount member)
              cases requiredObserved : VcTermSort.require_sort
                  amount.receiver .Reference
                  VcTermSort.SortContext.PermissionTransferReceiver with
              | div => simp [Terminates, requiredObserved] at requiredTerminates
              | fail requiredError =>
                  simp [Terminates,
                    VcTermSort.require_permission_transfer_amounts_loop.body,
                    observed, core.result.Result.is_ok, requiredObserved]
              | ok checked =>
                  cases checked with
                  | Err current =>
                      simp [Terminates,
                        VcTermSort.require_permission_transfer_amounts_loop.body,
                        observed, core.result.Result.is_ok, requiredObserved]
                  | Ok value =>
                      simp [Terminates,
                        VcTermSort.require_permission_transfer_amounts_loop.body,
                        observed, core.result.Result.is_ok, requiredObserved,
                        core.fmt.rt.Argument.new_display,
                        core.fmt.Arguments.new, alloc.fmt.format,
                        core.hint.must_use]
                      by_cases zero : amount.denominator = 0#u32
                      · simp [zero, Terminates]
                      · by_cases comparison :
                            amount.denominator.val < amount.numerator.val <;>
                          simp [zero, comparison, Terminates]

theorem require_permission_transfer_amounts_body_preserves_slice
    (iter next : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued :
      VcTermSort.require_permission_transfer_amounts_loop.body iter result =
        .ok (.cont (next, nextResult))) :
    next.slice = iter.slice := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSort.require_permission_transfer_amounts_loop.body,
        observed] at continued
  | div =>
      simp [VcTermSort.require_permission_transfer_amounts_loop.body,
        observed] at continued
  | ok pair =>
      obtain ⟨maybeAmount, advanced⟩ := pair
      cases maybeAmount with
      | none =>
          simp [VcTermSort.require_permission_transfer_amounts_loop.body,
            observed] at continued
      | some amount =>
          have advancedSlice := (slice_iterator_next_some_member
            iter advanced amount observed).2
          have advancedEq : advanced = next := by
            cases result with
            | Err current =>
                simp [VcTermSort.require_permission_transfer_amounts_loop.body,
                  observed, core.result.Result.is_ok] at continued
                exact continued.1
            | Ok checkedUnit =>
                cases requiredObserved : VcTermSort.require_sort
                    amount.receiver .Reference
                    VcTermSort.SortContext.PermissionTransferReceiver with
                | fail requiredError =>
                    simp [VcTermSort.require_permission_transfer_amounts_loop.body,
                      observed, core.result.Result.is_ok,
                      requiredObserved] at continued
                | div =>
                    simp [VcTermSort.require_permission_transfer_amounts_loop.body,
                      observed, core.result.Result.is_ok,
                      requiredObserved] at continued
                | ok checked =>
                    cases checked with
                    | Err current =>
                        simp [VcTermSort.require_permission_transfer_amounts_loop.body,
                          observed, core.result.Result.is_ok,
                          requiredObserved] at continued
                        exact continued.1
                    | Ok value =>
                        simp [VcTermSort.require_permission_transfer_amounts_loop.body,
                          observed, core.result.Result.is_ok, requiredObserved,
                          core.fmt.rt.Argument.new_display,
                          core.fmt.Arguments.new, alloc.fmt.format,
                          core.hint.must_use] at continued
                        by_cases zero : amount.denominator = 0#u32
                        · simp [zero] at continued
                          exact continued.1
                        · by_cases comparison :
                              amount.denominator.val < amount.numerator.val
                          · simp [zero, comparison] at continued
                            exact continued.1
                          · simp [zero, comparison] at continued
                            exact continued.1
          subst next
          exact advancedSlice

theorem require_permission_transfer_amounts_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result : core.result.Result Unit VcTermSort.SortError)
    (receiversTerminate : ∀ amount, amount ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed amount.receiver)) :
    Terminates
      (VcTermSort.require_permission_transfer_amounts_loop iter result) := by
  unfold VcTermSort.require_permission_transfer_amounts_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter VcTermSort.PermissionTransferAmount ×
        core.result.Result Unit VcTermSort.SortError =>
      VcTermSort.require_permission_transfer_amounts_loop.body state.1 state.2)
    (fun state => ∀ amount, amount ∈ state.1.slice.val →
      Terminates (VcTermSort.Term.sort_typed amount.receiver))
    (fun state => sliceIteratorRemaining state.1)
  · intro state stateInvariant
    exact require_permission_transfer_amounts_body_terminates
      state.1 state.2 stateInvariant
  · intro state next stateInvariant continued amount member
    apply stateInvariant amount
    have slicesEqual := require_permission_transfer_amounts_body_preserves_slice
      state.1 next.1 state.2 next.2 continued
    simpa [slicesEqual] using member
  · intro state next continued
    exact require_permission_transfer_amounts_body_decreases
      state.1 next.1 state.2 next.2 continued
  · exact receiversTerminate
  · simp [sliceIteratorRemaining]

theorem require_permission_transfer_amounts_terminates
    (amounts : Slice VcTermSort.PermissionTransferAmount)
    (receiversTerminate : ∀ amount, amount ∈ amounts.val →
      Terminates (VcTermSort.Term.sort_typed amount.receiver)) :
    Terminates (VcTermSort.require_permission_transfer_amounts amounts) := by
  rw [VcTermSort.require_permission_transfer_amounts.eq_def]
  change Terminates
    (VcTermSort.require_permission_transfer_amounts_loop
      ⟨amounts, 0⟩ (core.result.Result.Ok ()))
  exact require_permission_transfer_amounts_loop_terminates
    ⟨amounts, 0⟩ (core.result.Result.Ok ()) receiversTerminate

set_option maxHeartbeats 500000 in
theorem all_nominal_reference_keys_body_terminates
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result : Bool) :
    Terminates (VcTermSort.all_nominal_reference_keys_loop.body iter result) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail error =>
      simp [Terminates,
        VcTermSort.all_nominal_reference_keys_loop.body, observed]
  | ok pair =>
      obtain ⟨maybeEntry, next⟩ := pair
      cases maybeEntry with
      | none =>
          simp [Terminates,
            VcTermSort.all_nominal_reference_keys_loop.body, observed]
      | some entry =>
          obtain ⟨key, value⟩ := entry
          cases result <;> cases key <;>
            simp [Terminates,
              VcTermSort.all_nominal_reference_keys_loop.body, observed]

theorem all_nominal_reference_keys_loop_terminates
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result : Bool) :
    Terminates (VcTermSort.all_nominal_reference_keys_loop iter result) := by
  unfold VcTermSort.all_nominal_reference_keys_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter
        (VcTermSort.Term × VcTermSort.Term) × Bool =>
      VcTermSort.all_nominal_reference_keys_loop.body state.1 state.2)
    (fun _ => True)
    (fun state => sliceIteratorRemaining state.1)
  · intro state _
    exact all_nominal_reference_keys_body_terminates state.1 state.2
  · intro _ _ _ _
    trivial
  · intro state next continued
    exact all_nominal_reference_keys_body_decreases
      state.1 next.1 state.2 next.2 continued
  · trivial
  · simp [sliceIteratorRemaining]

theorem all_nominal_reference_keys_terminates
    (entries : Slice (VcTermSort.Term × VcTermSort.Term)) :
    Terminates (VcTermSort.all_nominal_reference_keys entries) := by
  unfold VcTermSort.all_nominal_reference_keys
  change Terminates
    (VcTermSort.all_nominal_reference_keys_loop ⟨entries, 0⟩ true)
  exact all_nominal_reference_keys_loop_terminates ⟨entries, 0⟩ true

theorem require_finite_dict_entry_sorts_body_terminates
    (keySort valueSort : VcTermSort.Sort)
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenTerminate : ∀ entry, entry ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed entry.1) ∧
      Terminates (VcTermSort.Term.sort_typed entry.2)) :
    Terminates (VcTermSort.require_finite_dict_entry_sorts_loop.body
      keySort valueSort iter result) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail error =>
      simp [Terminates,
        VcTermSort.require_finite_dict_entry_sorts_loop.body, observed]
  | ok pair =>
      obtain ⟨maybeEntry, next⟩ := pair
      cases maybeEntry with
      | none =>
          simp [Terminates,
            VcTermSort.require_finite_dict_entry_sorts_loop.body, observed]
      | some entry =>
          obtain ⟨key, value⟩ := entry
          have member := (slice_iterator_next_some_member
            iter next (key, value) observed).1
          have keyRequired := require_sort_terminates_of_term_sort_terminates
            key keySort VcTermSort.SortContext.FiniteDictionaryKey
            (childrenTerminate (key, value) member).1
          have valueRequired := require_sort_terminates_of_term_sort_terminates
            value valueSort VcTermSort.SortContext.FiniteDictionaryValue
            (childrenTerminate (key, value) member).2
          cases result with
          | Err current =>
              simp [Terminates,
                VcTermSort.require_finite_dict_entry_sorts_loop.body,
                observed, core.result.Result.is_ok]
          | Ok checkedUnit =>
              rw [VcTermSort.require_finite_dict_entry_sorts_loop.body]
              rw [observed]
              change Terminates (do
                let keyClone ←
                  VcTermSort.Sort.Insts.CoreCloneClone.clone keySort
                let keyChecked ← VcTermSort.require_sort key keyClone
                  VcTermSort.SortContext.FiniteDictionaryKey
                match keyChecked with
                | core.result.Result.Ok _ => do
                    let valueClone ←
                      VcTermSort.Sort.Insts.CoreCloneClone.clone valueSort
                    let valueChecked ← VcTermSort.require_sort value valueClone
                      VcTermSort.SortContext.FiniteDictionaryValue
                    ok (ControlFlow.cont (next, valueChecked))
                | core.result.Result.Err _ =>
                    ok (ControlFlow.cont (next, keyChecked)))
              rw [sort_clone_exact]
              cases keyObserved : VcTermSort.require_sort key keySort
                  VcTermSort.SortContext.FiniteDictionaryKey with
              | div => simp [Terminates, keyObserved] at keyRequired
              | fail error => simp [Terminates, keyObserved]
              | ok keyChecked =>
                  cases keyChecked with
                  | Err current => simp [Terminates, keyObserved]
                  | Ok keyUnit =>
                      rw [sort_clone_exact]
                      cases valueObserved : VcTermSort.require_sort value valueSort
                          VcTermSort.SortContext.FiniteDictionaryValue with
                      | div =>
                          simp [Terminates, valueObserved] at valueRequired
                      | fail error =>
                          simp [Terminates, keyObserved, valueObserved]
                      | ok valueChecked =>
                          simp [Terminates, keyObserved, valueObserved]

theorem require_finite_dict_entry_sorts_body_preserves_slice
    (keySort valueSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.require_finite_dict_entry_sorts_loop.body
      keySort valueSort iter result = .ok (.cont (next, nextResult))) :
    next.slice = iter.slice := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.require_finite_dict_entry_sorts_loop.body,
        observed] at continued
  | div =>
      simp [VcTermSort.require_finite_dict_entry_sorts_loop.body,
        observed] at continued
  | ok pair =>
      obtain ⟨maybeEntry, advanced⟩ := pair
      cases maybeEntry with
      | none =>
          simp [VcTermSort.require_finite_dict_entry_sorts_loop.body,
            observed] at continued
      | some entry =>
          obtain ⟨key, value⟩ := entry
          have advancedSlice := (slice_iterator_next_some_member
            iter advanced (key, value) observed).2
          have advancedEq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSort.require_finite_dict_entry_sorts_loop.body,
                  observed, isOkObserved] at continued
            | div =>
                simp [VcTermSort.require_finite_dict_entry_sorts_loop.body,
                  observed, isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSort.require_finite_dict_entry_sorts_loop.body,
                      observed, isOkObserved] at continued
                    exact continued.1
                | true =>
                    simp [VcTermSort.require_finite_dict_entry_sorts_loop.body,
                      observed, isOkObserved] at continued
                    simp only [Bind.bind, Std.bind] at continued
                    all_goals repeat' split at continued
                    all_goals
                      have mapped := congrArg continuationIterator continued
                      simp [continuationIterator] at mapped <;> assumption
          subst next
          exact advancedSlice

theorem require_finite_dict_entry_sorts_loop_terminates
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (keySort valueSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenTerminate : ∀ entry, entry ∈ iter.slice.val →
      Terminates (VcTermSort.Term.sort_typed entry.1) ∧
      Terminates (VcTermSort.Term.sort_typed entry.2)) :
    Terminates (VcTermSort.require_finite_dict_entry_sorts_loop
      iter keySort valueSort result) := by
  unfold VcTermSort.require_finite_dict_entry_sorts_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter
        (VcTermSort.Term × VcTermSort.Term) ×
        core.result.Result Unit VcTermSort.SortError =>
      VcTermSort.require_finite_dict_entry_sorts_loop.body
        keySort valueSort state.1 state.2)
    (fun state => ∀ entry, entry ∈ state.1.slice.val →
      Terminates (VcTermSort.Term.sort_typed entry.1) ∧
      Terminates (VcTermSort.Term.sort_typed entry.2))
    (fun state => sliceIteratorRemaining state.1)
  · intro state stateInvariant
    exact require_finite_dict_entry_sorts_body_terminates
      keySort valueSort state.1 state.2 stateInvariant
  · intro state next stateInvariant continued entry member
    apply stateInvariant entry
    have slicesEqual := require_finite_dict_entry_sorts_body_preserves_slice
      keySort valueSort state.1 next.1 state.2 next.2 continued
    simpa [slicesEqual] using member
  · intro state next continued
    exact require_finite_dict_entry_sorts_body_decreases keySort valueSort
      state.1 next.1 state.2 next.2 continued
  · exact childrenTerminate
  · simp [sliceIteratorRemaining]

theorem require_finite_dict_entry_sorts_terminates
    (entries : Slice (VcTermSort.Term × VcTermSort.Term))
    (keySort valueSort : VcTermSort.Sort)
    (childrenTerminate : ∀ entry, entry ∈ entries.val →
      Terminates (VcTermSort.Term.sort_typed entry.1) ∧
      Terminates (VcTermSort.Term.sort_typed entry.2)) :
    Terminates (VcTermSort.require_finite_dict_entry_sorts
      entries keySort valueSort) := by
  rw [VcTermSort.require_finite_dict_entry_sorts.eq_def]
  change Terminates (VcTermSort.require_finite_dict_entry_sorts_loop
    ⟨entries, 0⟩ keySort valueSort (core.result.Result.Ok ()))
  exact require_finite_dict_entry_sorts_loop_terminates
    ⟨entries, 0⟩ keySort valueSort (core.result.Result.Ok ())
    childrenTerminate

/-- First recursive constructor connected to the structural induction
    boundary: its only recursive call is on its immediate child. -/
theorem term_sort_runtime_class_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.RuntimeClass value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.RuntimeClass value)) := by
  have childSmaller : TermStrictlySmaller value (.RuntimeClass value) := by
    simp [TermStrictlySmaller]
  have childTerminates := smallerTerminates value childSmaller
  have requiredTerminates :=
    require_sort_terminates_of_term_sort_terminates value .Reference
      VcTermSort.SortContext.RuntimeClassOperand childTerminates
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_sort_then_ok_terminates _ requiredTerminates .Class

/-- Boolean negation has the same single-child induction shape. -/
theorem term_sort_not_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Not value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Not value)) := by
  have childSmaller : TermStrictlySmaller value (.Not value) := by
    simp [TermStrictlySmaller]
  have childTerminates := smallerTerminates value childSmaller
  have requiredTerminates :=
    require_sort_terminates_of_term_sort_terminates value .Bool
      VcTermSort.SortContext.NotOperand childTerminates
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_sort_then_ok_terminates _ requiredTerminates .Bool

/-- Arithmetic negation has the same single-child induction shape. -/
theorem term_sort_negate_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Negate value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Negate value)) := by
  have childSmaller : TermStrictlySmaller value (.Negate value) := by
    simp [TermStrictlySmaller]
  have childTerminates := smallerTerminates value childSmaller
  have requiredTerminates :=
    require_sort_terminates_of_term_sort_terminates value .Int
      VcTermSort.SortContext.NegationOperand childTerminates
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_sort_then_ok_terminates _ requiredTerminates .Int

/-- String length connects another generated unary branch to the same
    well-founded child relation. -/
theorem term_sort_string_length_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.StringLength value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.StringLength value)) := by
  have childSmaller : TermStrictlySmaller value (.StringLength value) := by
    simp [TermStrictlySmaller]
  have childTerminates := smallerTerminates value childSmaller
  have requiredTerminates :=
    require_sort_terminates_of_term_sort_terminates value .String
      VcTermSort.SortContext.StringLengthOperand childTerminates
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_sort_then_ok_terminates _ requiredTerminates .Int

/-- Bytes length connects another generated unary branch to the same
    well-founded child relation. -/
theorem term_sort_bytes_length_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.BytesLength value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.BytesLength value)) := by
  have childSmaller : TermStrictlySmaller value (.BytesLength value) := by
    simp [TermStrictlySmaller]
  have childTerminates := smallerTerminates value childSmaller
  have requiredTerminates :=
    require_sort_terminates_of_term_sort_terminates value .Bytes
      VcTermSort.SortContext.BytesLengthOperand childTerminates
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_sort_then_ok_terminates _ requiredTerminates .Int

/-- Class-subtype checking is the first two-child branch: both recursive calls
    are connected to the structural relation, while the generated `?` order is
    retained by `require_two_sorts_then_ok_terminates`. -/
theorem term_sort_class_subtype_terminates_of_smaller
    (actual expected : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.ClassSubtype actual expected) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.ClassSubtype actual expected)) := by
  have actualSmaller : TermStrictlySmaller actual (.ClassSubtype actual expected) := by
    simp [TermStrictlySmaller]
    omega
  have expectedSmaller : TermStrictlySmaller expected (.ClassSubtype actual expected) := by
    simp [TermStrictlySmaller]
  have actualRequired := require_sort_terminates_of_term_sort_terminates
    actual .Class VcTermSort.SortContext.SubclassActualOperand
    (smallerTerminates actual actualSmaller)
  have expectedRequired := require_sort_terminates_of_term_sort_terminates
    expected .Class VcTermSort.SortContext.SubclassExpectedOperand
    (smallerTerminates expected expectedSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_two_sorts_then_ok_terminates _ _ actualRequired expectedRequired .Bool

/-- Boolean implication has the same exact ordered two-child shape. -/
theorem term_sort_implies_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Implies left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Implies left right)) := by
  have leftSmaller : TermStrictlySmaller left (.Implies left right) := by
    simp [TermStrictlySmaller]
    omega
  have rightSmaller : TermStrictlySmaller right (.Implies left right) := by
    simp [TermStrictlySmaller]
  have leftRequired := require_sort_terminates_of_term_sort_terminates
    left .Bool VcTermSort.SortContext.ImplicationLeftOperand
    (smallerTerminates left leftSmaller)
  have rightRequired := require_sort_terminates_of_term_sort_terminates
    right .Bool VcTermSort.SortContext.ImplicationRightOperand
    (smallerTerminates right rightSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_two_sorts_then_ok_terminates _ _ leftRequired rightRequired .Bool

theorem term_sort_less_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Less left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Less left right)) := by
  have leftSmaller : TermStrictlySmaller left (.Less left right) := by
    simp [TermStrictlySmaller]
    omega
  have rightSmaller : TermStrictlySmaller right (.Less left right) := by
    simp [TermStrictlySmaller]
  have leftRequired := require_sort_terminates_of_term_sort_terminates
    left .Int VcTermSort.SortContext.IntegerLeftOperand (smallerTerminates left leftSmaller)
  have rightRequired := require_sort_terminates_of_term_sort_terminates
    right .Int VcTermSort.SortContext.IntegerRightOperand (smallerTerminates right rightSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_two_sorts_then_ok_terminates _ _ leftRequired rightRequired .Bool

theorem term_sort_less_equal_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.LessEqual left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.LessEqual left right)) := by
  have leftSmaller : TermStrictlySmaller left (.LessEqual left right) := by
    simp [TermStrictlySmaller]
    omega
  have rightSmaller : TermStrictlySmaller right (.LessEqual left right) := by
    simp [TermStrictlySmaller]
  have leftRequired := require_sort_terminates_of_term_sort_terminates
    left .Int VcTermSort.SortContext.IntegerLeftOperand (smallerTerminates left leftSmaller)
  have rightRequired := require_sort_terminates_of_term_sort_terminates
    right .Int VcTermSort.SortContext.IntegerRightOperand (smallerTerminates right rightSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_two_sorts_then_ok_terminates _ _ leftRequired rightRequired .Bool

theorem term_sort_greater_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Greater left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Greater left right)) := by
  have leftSmaller : TermStrictlySmaller left (.Greater left right) := by
    simp [TermStrictlySmaller]
    omega
  have rightSmaller : TermStrictlySmaller right (.Greater left right) := by
    simp [TermStrictlySmaller]
  have leftRequired := require_sort_terminates_of_term_sort_terminates
    left .Int VcTermSort.SortContext.IntegerLeftOperand (smallerTerminates left leftSmaller)
  have rightRequired := require_sort_terminates_of_term_sort_terminates
    right .Int VcTermSort.SortContext.IntegerRightOperand (smallerTerminates right rightSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_two_sorts_then_ok_terminates _ _ leftRequired rightRequired .Bool

theorem term_sort_greater_equal_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.GreaterEqual left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.GreaterEqual left right)) := by
  have leftSmaller : TermStrictlySmaller left (.GreaterEqual left right) := by
    simp [TermStrictlySmaller]
    omega
  have rightSmaller : TermStrictlySmaller right (.GreaterEqual left right) := by
    simp [TermStrictlySmaller]
  have leftRequired := require_sort_terminates_of_term_sort_terminates
    left .Int VcTermSort.SortContext.IntegerLeftOperand (smallerTerminates left leftSmaller)
  have rightRequired := require_sort_terminates_of_term_sort_terminates
    right .Int VcTermSort.SortContext.IntegerRightOperand (smallerTerminates right rightSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_two_sorts_then_ok_terminates _ _ leftRequired rightRequired .Bool

theorem term_sort_add_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Add left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Add left right)) := by
  have leftSmaller : TermStrictlySmaller left (.Add left right) := by
    simp [TermStrictlySmaller]
    omega
  have rightSmaller : TermStrictlySmaller right (.Add left right) := by
    simp [TermStrictlySmaller]
  have leftRequired := require_sort_terminates_of_term_sort_terminates
    left .Int VcTermSort.SortContext.IntegerLeftOperand (smallerTerminates left leftSmaller)
  have rightRequired := require_sort_terminates_of_term_sort_terminates
    right .Int VcTermSort.SortContext.IntegerRightOperand (smallerTerminates right rightSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_two_sorts_then_ok_terminates _ _ leftRequired rightRequired .Int

theorem term_sort_subtract_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Subtract left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Subtract left right)) := by
  have leftSmaller : TermStrictlySmaller left (.Subtract left right) := by
    simp [TermStrictlySmaller]
    omega
  have rightSmaller : TermStrictlySmaller right (.Subtract left right) := by
    simp [TermStrictlySmaller]
  have leftRequired := require_sort_terminates_of_term_sort_terminates
    left .Int VcTermSort.SortContext.IntegerLeftOperand (smallerTerminates left leftSmaller)
  have rightRequired := require_sort_terminates_of_term_sort_terminates
    right .Int VcTermSort.SortContext.IntegerRightOperand (smallerTerminates right rightSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_two_sorts_then_ok_terminates _ _ leftRequired rightRequired .Int

theorem term_sort_multiply_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Multiply left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Multiply left right)) := by
  have leftSmaller : TermStrictlySmaller left (.Multiply left right) := by
    simp [TermStrictlySmaller]
    omega
  have rightSmaller : TermStrictlySmaller right (.Multiply left right) := by
    simp [TermStrictlySmaller]
  have leftRequired := require_sort_terminates_of_term_sort_terminates
    left .Int VcTermSort.SortContext.IntegerLeftOperand (smallerTerminates left leftSmaller)
  have rightRequired := require_sort_terminates_of_term_sort_terminates
    right .Int VcTermSort.SortContext.IntegerRightOperand (smallerTerminates right rightSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_two_sorts_then_ok_terminates _ _ leftRequired rightRequired .Int

theorem term_sort_bytes_get_terminates_of_smaller
    (bytes index : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.BytesGet bytes index) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.BytesGet bytes index)) := by
  have bytesSmaller : TermStrictlySmaller bytes (.BytesGet bytes index) := by
    simp [TermStrictlySmaller]
    omega
  have indexSmaller : TermStrictlySmaller index (.BytesGet bytes index) := by
    simp [TermStrictlySmaller]
  have bytesRequired := require_sort_terminates_of_term_sort_terminates
    bytes .Bytes VcTermSort.SortContext.BytesIndexReceiver (smallerTerminates bytes bytesSmaller)
  have indexRequired := require_sort_terminates_of_term_sort_terminates
    index .Int VcTermSort.SortContext.BytesIndex (smallerTerminates index indexSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_two_sorts_then_ok_terminates _ _ bytesRequired indexRequired .Int

/-- A positive-permission predicate performs one recursive receiver check and
    then returns its Boolean sort. -/
theorem term_sort_permission_positive_terminates_of_smaller
    (mask : Std.U32) (receiver : VcTermSort.Term) (field : String)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.PermissionPositive mask receiver field) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.PermissionPositive mask receiver field)) := by
  have receiverSmaller :
      TermStrictlySmaller receiver (.PermissionPositive mask receiver field) := by
    simp [TermStrictlySmaller]
    omega
  have receiverRequired := require_sort_terminates_of_term_sort_terminates
    receiver .Reference VcTermSort.SortContext.PermissionReceiver
    (smallerTerminates receiver receiverSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  exact require_sort_then_ok_terminates _ receiverRequired .Bool

/-- Positive floor division retains the source divisor check after its single
    recursive operand check. Both divisor outcomes are concrete. -/
theorem term_sort_floor_divide_terminates_of_smaller
    (value : VcTermSort.Term) (divisor : Std.U64)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.FloorDivideByPositive value divisor) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.FloorDivideByPositive value divisor)) := by
  have valueSmaller :
      TermStrictlySmaller value (.FloorDivideByPositive value divisor) := by
    simp [TermStrictlySmaller]
    omega
  have valueRequired := require_sort_terminates_of_term_sort_terminates
    value .Int VcTermSort.SortContext.FloorDivisionOperand
    (smallerTerminates value valueSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases valueObserved :
      VcTermSort.require_sort value .Int VcTermSort.SortContext.FloorDivisionOperand with
  | div => simp [Terminates, valueObserved] at valueRequired
  | fail error => simp [Terminates, valueObserved]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, valueObserved, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          simp [Terminates, valueObserved, core.result.Result.Insts.CoreOpsTry.branch,
            Str.Insts.AllocBorrowToOwnedString.to_owned]
          split <;> simp

/-- List length inspects the exact recursive child sort and has a total
    diagnostic continuation for every one of the fourteen sort variants. -/
theorem term_sort_list_length_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.ListLength value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.ListLength value)) := by
  have valueSmaller : TermStrictlySmaller value (.ListLength value) := by
    simp [TermStrictlySmaller]
  have valueTerminates := smallerTerminates value valueSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases valueObserved : VcTermSort.Term.sort_typed value with
  | div => simp [Terminates, valueObserved] at valueTerminates
  | fail error => simp [Terminates, valueObserved]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, valueObserved, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok actual =>
          cases actual <;>
            simp [Terminates, valueObserved, core.result.Result.Insts.CoreOpsTry.branch,
              core.fmt.rt.Argument.new_debug, core.fmt.Arguments.new,
              alloc.fmt.format, core.hint.must_use]

/-- Static list slicing inspects only the recursive source sort. The literal
    bounds and nonzero step are stored data and do not introduce a call. -/
theorem term_sort_list_slice_terminates_of_smaller
    (source : VcTermSort.Term) (lower upper : Option Std.I128)
    (step : core.num.nonzero.NonZero Std.I128
      core.num.niche_types.NonZeroI128Inner)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.ListSlice source lower upper step) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates
      (VcTermSort.Term.sort_typed (.ListSlice source lower upper step)) := by
  have sourceSmaller :
      TermStrictlySmaller source (.ListSlice source lower upper step) := by
    simp [TermStrictlySmaller] <;> omega
  have sourceTerminates := smallerTerminates source sourceSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases sourceObserved : VcTermSort.Term.sort_typed source with
  | div => simp [Terminates, sourceObserved] at sourceTerminates
  | fail error => simp [Terminates, sourceObserved]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, sourceObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok actual =>
          cases actual <;>
            simp [Terminates, sourceObserved,
              core.result.Result.Insts.CoreOpsTry.branch]

theorem term_sort_list_concat_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.ListConcat left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.ListConcat left right)) := by
  have leftSmaller : TermStrictlySmaller left (.ListConcat left right) := by
    simp [TermStrictlySmaller] <;> omega
  have rightSmaller : TermStrictlySmaller right (.ListConcat left right) := by
    simp [TermStrictlySmaller] <;> omega
  have leftTerminates := smallerTerminates left leftSmaller
  have rightTerminates := smallerTerminates right rightSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases leftObserved : VcTermSort.Term.sort_typed left with
  | div => simp [Terminates, leftObserved] at leftTerminates
  | fail error => simp [Terminates, leftObserved]
  | ok leftChecked =>
      cases leftChecked with
      | Err error =>
          simp [Terminates, leftObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok leftSort =>
          cases leftSort <;>
            simp_all [Terminates, leftObserved,
              core.result.Result.Insts.CoreOpsTry.branch, box_ne_refines,
              core.cmp.PartialEq.ne.trait_default,
              core.cmp.PartialEq.ne.default, VcTermSort.sortPartialEqModel]
          case List leftElement =>
            have rightTerminates := smallerTerminates right rightSmaller
            cases rightObserved : VcTermSort.Term.sort_typed right with
            | div => simp [Terminates, rightObserved] at rightTerminates
            | fail error => simp [Terminates, rightObserved]
            | ok rightChecked =>
                cases rightChecked with
                | Err error =>
                    simp [Terminates, rightObserved,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                | Ok rightSort =>
                    cases rightSort <;>
                      simp_all [Terminates, rightObserved,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        box_ne_refines, core.cmp.PartialEq.ne.trait_default,
                        core.cmp.PartialEq.ne.default,
                        VcTermSort.sortPartialEqModel]
                    case List rightElement => split <;> simp [Terminates]

theorem term_sort_list_sum_terminates_of_smaller
    (source : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.ListSum source) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.ListSum source)) := by
  have sourceSmaller : TermStrictlySmaller source (.ListSum source) := by
    simp [TermStrictlySmaller] <;> omega
  have sourceTerminates := smallerTerminates source sourceSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases sourceObserved : VcTermSort.Term.sort_typed source with
  | div => simp [Terminates, sourceObserved] at sourceTerminates
  | fail error => simp [Terminates, sourceObserved]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, sourceObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok actual =>
          simp only [sourceObserved, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry.branch]
          rw [VcTermSort.sortPartialEqModel]
          simp [Terminates]
          split <;> simp

theorem term_sort_list_sorted_terminates_of_smaller
    (source : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.ListSorted source) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.ListSorted source)) := by
  have sourceSmaller : TermStrictlySmaller source (.ListSorted source) := by
    simp [TermStrictlySmaller] <;> omega
  have sourceTerminates := smallerTerminates source sourceSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases sourceObserved : VcTermSort.Term.sort_typed source with
  | div => simp [Terminates, sourceObserved] at sourceTerminates
  | fail error => simp [Terminates, sourceObserved]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, sourceObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok actual =>
          simp only [sourceObserved, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry.branch]
          rw [VcTermSort.sortPartialEqModel]
          simp [Terminates]
          split <;> simp

/-- Set length has the same exact child-sort/total-diagnostic shape. -/
theorem term_sort_set_length_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.SetLength value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.SetLength value)) := by
  have valueSmaller : TermStrictlySmaller value (.SetLength value) := by
    simp [TermStrictlySmaller]
  have valueTerminates := smallerTerminates value valueSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases valueObserved : VcTermSort.Term.sort_typed value with
  | div => simp [Terminates, valueObserved] at valueTerminates
  | fail error => simp [Terminates, valueObserved]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, valueObserved, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok actual =>
          cases actual <;>
            simp [Terminates, valueObserved, core.result.Result.Insts.CoreOpsTry.branch,
              core.fmt.rt.Argument.new_debug, core.fmt.Arguments.new,
              alloc.fmt.format, core.hint.must_use]

/-- Dictionary length has the same exact child-sort/total-diagnostic shape. -/
theorem term_sort_dict_length_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.DictLength value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.DictLength value)) := by
  have valueSmaller : TermStrictlySmaller value (.DictLength value) := by
    simp [TermStrictlySmaller]
  have valueTerminates := smallerTerminates value valueSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases valueObserved : VcTermSort.Term.sort_typed value with
  | div => simp [Terminates, valueObserved] at valueTerminates
  | fail error => simp [Terminates, valueObserved]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, valueObserved, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok actual =>
          cases actual <;>
            simp [Terminates, valueObserved, core.result.Result.Insts.CoreOpsTry.branch,
              core.fmt.rt.Argument.new_debug, core.fmt.Arguments.new,
              alloc.fmt.format, core.hint.must_use]

/-- A field read checks its recursive receiver and then executes the exact
    source-owned admissibility/clone continuation for its declared field sort. -/
theorem term_sort_field_read_terminates_of_smaller
    (mask : Std.U32) (receiver : VcTermSort.Term) (field : String)
    (sort : VcTermSort.Sort)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.FieldRead mask receiver field sort) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.FieldRead mask receiver field sort)) := by
  have receiverSmaller :
      TermStrictlySmaller receiver (.FieldRead mask receiver field sort) := by
    simp [TermStrictlySmaller]
    omega
  have receiverRequired := require_sort_terminates_of_term_sort_terminates
    receiver .Reference VcTermSort.SortContext.FieldReceiver
    (smallerTerminates receiver receiverSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases receiverObserved :
      VcTermSort.require_sort receiver .Reference VcTermSort.SortContext.FieldReceiver with
  | div => simp [Terminates, receiverObserved] at receiverRequired
  | fail error => simp [Terminates, receiverObserved]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, receiverObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          cases sort <;>
            simp [Terminates, receiverObserved,
              core.result.Result.Insts.CoreOpsTry.branch,
              VcTermSort.is_list_element_sort]
          all_goals try exact sort_clone_then_result_ok_terminates _
          case List element =>
            have predicateTerminates := is_list_element_sort_terminates element
            cases predicateObserved : VcTermSort.is_list_element_sort element with
            | div => simp [Terminates, predicateObserved] at predicateTerminates
            | fail error => simp [Terminates, predicateObserved]
            | ok accepted =>
                cases accepted <;> simp [Terminates, predicateObserved]
                · exact sort_clone_then_result_error_terminates _ _
                · exact sort_clone_then_result_ok_terminates _

/-- Permission-fraction validation is total after its recursive receiver
    check; both the zero-denominator and scalar-comparison diagnostics are
    retained from the generated source semantics. -/
theorem term_sort_permission_at_least_terminates_of_smaller
    (mask : Std.U32) (receiver : VcTermSort.Term) (field : String)
    (numerator denominator : Std.U32)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child
          (.PermissionAtLeast mask receiver field numerator denominator) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed
      (.PermissionAtLeast mask receiver field numerator denominator)) := by
  have receiverSmaller : TermStrictlySmaller receiver
      (.PermissionAtLeast mask receiver field numerator denominator) := by
    simp [TermStrictlySmaller]
    omega
  have receiverRequired := require_sort_terminates_of_term_sort_terminates
    receiver .Reference VcTermSort.SortContext.PermissionReceiver
    (smallerTerminates receiver receiverSmaller)
  have fractionCompared := u32_shared_gt_terminates numerator denominator
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases receiverObserved :
      VcTermSort.require_sort receiver .Reference VcTermSort.SortContext.PermissionReceiver with
  | div => simp [Terminates, receiverObserved] at receiverRequired
  | fail error => simp [Terminates, receiverObserved]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, receiverObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          by_cases denominatorZero : denominator = 0#u32
          · simp [Terminates, receiverObserved, denominatorZero,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.fmt.rt.Argument.new_display, core.fmt.Arguments.new,
              alloc.fmt.format, core.hint.must_use]
          · cases comparisonObserved :
                Shared1A.Insts.CoreCmpPartialOrdShared0B.gt
                  core.cmp.PartialOrdU32 numerator denominator with
            | div => simp [Terminates, comparisonObserved] at fractionCompared
            | fail error =>
                simp [Terminates, receiverObserved, denominatorZero,
                  comparisonObserved,
                  core.result.Result.Insts.CoreOpsTry.branch]
            | ok greater =>
                cases greater <;>
                  simp [Terminates, receiverObserved, denominatorZero,
                    comparisonObserved,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.fmt.rt.Argument.new_display, core.fmt.Arguments.new,
                    alloc.fmt.format, core.hint.must_use]

theorem term_sort_permission_at_most_terminates_of_smaller
    (mask : Std.U32) (receiver : VcTermSort.Term) (field : String)
    (numerator denominator : Std.U32)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child
          (.PermissionAtMost mask receiver field numerator denominator) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed
      (.PermissionAtMost mask receiver field numerator denominator)) := by
  have receiverSmaller : TermStrictlySmaller receiver
      (.PermissionAtMost mask receiver field numerator denominator) := by
    simp [TermStrictlySmaller]
    omega
  have receiverRequired := require_sort_terminates_of_term_sort_terminates
    receiver .Reference VcTermSort.SortContext.PermissionReceiver
    (smallerTerminates receiver receiverSmaller)
  have fractionCompared := u32_shared_gt_terminates numerator denominator
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases receiverObserved :
      VcTermSort.require_sort receiver .Reference VcTermSort.SortContext.PermissionReceiver with
  | div => simp [Terminates, receiverObserved] at receiverRequired
  | fail error => simp [Terminates, receiverObserved]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, receiverObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          by_cases denominatorZero : denominator = 0#u32
          · simp [Terminates, receiverObserved, denominatorZero,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.fmt.rt.Argument.new_display, core.fmt.Arguments.new,
              alloc.fmt.format, core.hint.must_use]
          · cases comparisonObserved :
                Shared1A.Insts.CoreCmpPartialOrdShared0B.gt
                  core.cmp.PartialOrdU32 numerator denominator with
            | div => simp [Terminates, comparisonObserved] at fractionCompared
            | fail error =>
                simp [Terminates, receiverObserved, denominatorZero,
                  comparisonObserved,
                  core.result.Result.Insts.CoreOpsTry.branch]
            | ok greater =>
                cases greater <;>
                  simp [Terminates, receiverObserved, denominatorZero,
                    comparisonObserved,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.fmt.rt.Argument.new_display, core.fmt.Arguments.new,
                    alloc.fmt.format, core.hint.must_use]

/-- Equality retains both recursive child sorts and the exact structural-sort
    inequality check before producing its Boolean result. -/
theorem term_sort_equal_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Equal left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Equal left right)) := by
  have leftSmaller : TermStrictlySmaller left (.Equal left right) := by
    simp [TermStrictlySmaller]
    omega
  have rightSmaller : TermStrictlySmaller right (.Equal left right) := by
    simp [TermStrictlySmaller]
  have leftTerminates := smallerTerminates left leftSmaller
  have rightTerminates := smallerTerminates right rightSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases leftObserved : VcTermSort.Term.sort_typed left with
  | div => simp [Terminates, leftObserved] at leftTerminates
  | fail error => simp [Terminates, leftObserved]
  | ok leftChecked =>
      cases leftChecked with
      | Err error =>
          simp [Terminates, leftObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok leftSort =>
          cases rightObserved : VcTermSort.Term.sort_typed right with
          | div => simp [Terminates, rightObserved] at rightTerminates
          | fail error => simp [Terminates, leftObserved, rightObserved,
              core.result.Result.Insts.CoreOpsTry.branch]
          | ok rightChecked =>
              cases rightChecked with
              | Err error =>
                  simp [Terminates, leftObserved, rightObserved,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
              | Ok rightSort =>
                  have compared := sort_ne_terminates leftSort rightSort
                  cases comparisonObserved :
                      core.cmp.PartialEq.ne.trait_default
                        VcTermSort.Sort.Insts.CoreCmpPartialEqSort
                        leftSort rightSort with
                  | div => simp [Terminates, comparisonObserved] at compared
                  | fail error =>
                      simp [Terminates, leftObserved, rightObserved,
                        comparisonObserved,
                        core.result.Result.Insts.CoreOpsTry.branch]
                  | ok different =>
                      cases different <;>
                        simp [Terminates, leftObserved, rightObserved,
                          comparisonObserved,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.fmt.rt.Argument.new_debug,
                          core.fmt.Arguments.new, alloc.fmt.format,
                          core.hint.must_use]

/-- Conditional synthesis checks its Boolean guard, evaluates both recursive
    branch sorts, and retains the exact structural-sort mismatch diagnostic. -/
theorem term_sort_if_then_else_terminates_of_smaller
    (condition thenValue elseValue : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.IfThenElse condition thenValue elseValue) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed
      (.IfThenElse condition thenValue elseValue)) := by
  have conditionSmaller : TermStrictlySmaller condition
      (.IfThenElse condition thenValue elseValue) := by
    simp [TermStrictlySmaller]
    omega
  have thenSmaller : TermStrictlySmaller thenValue
      (.IfThenElse condition thenValue elseValue) := by
    simp [TermStrictlySmaller]
    omega
  have elseSmaller : TermStrictlySmaller elseValue
      (.IfThenElse condition thenValue elseValue) := by
    simp [TermStrictlySmaller]
  have conditionRequired := require_sort_terminates_of_term_sort_terminates
    condition .Bool VcTermSort.SortContext.ConditionalGuard
    (smallerTerminates condition conditionSmaller)
  have thenTerminates := smallerTerminates thenValue thenSmaller
  have elseTerminates := smallerTerminates elseValue elseSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases conditionObserved :
      VcTermSort.require_sort condition .Bool VcTermSort.SortContext.ConditionalGuard with
  | div => simp [Terminates, conditionObserved] at conditionRequired
  | fail error => simp [Terminates, conditionObserved]
  | ok conditionChecked =>
      cases conditionChecked with
      | Err error =>
          simp [Terminates, conditionObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          cases thenObserved : VcTermSort.Term.sort_typed thenValue with
          | div => simp [Terminates, thenObserved] at thenTerminates
          | fail error => simp [Terminates, conditionObserved, thenObserved,
              core.result.Result.Insts.CoreOpsTry.branch]
          | ok thenChecked =>
              cases thenChecked with
              | Err error =>
                  simp [Terminates, conditionObserved, thenObserved,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
              | Ok thenSort =>
                  cases elseObserved : VcTermSort.Term.sort_typed elseValue with
                  | div => simp [Terminates, elseObserved] at elseTerminates
                  | fail error =>
                      simp [Terminates, conditionObserved, thenObserved,
                        elseObserved,
                        core.result.Result.Insts.CoreOpsTry.branch]
                  | ok elseChecked =>
                      cases elseChecked with
                      | Err error =>
                          simp [Terminates, conditionObserved, thenObserved,
                            elseObserved,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                      | Ok elseSort =>
                          have compared := sort_ne_terminates thenSort elseSort
                          cases comparisonObserved :
                              core.cmp.PartialEq.ne.trait_default
                                VcTermSort.Sort.Insts.CoreCmpPartialEqSort
                                thenSort elseSort with
                          | div =>
                              simp [Terminates, comparisonObserved] at compared
                          | fail error =>
                              simp [Terminates, conditionObserved, thenObserved,
                                elseObserved, comparisonObserved,
                                core.result.Result.Insts.CoreOpsTry.branch]
                          | ok different =>
                              cases different <;>
                                simp [Terminates, conditionObserved,
                                  thenObserved, elseObserved,
                                  comparisonObserved,
                                  core.result.Result.Insts.CoreOpsTry.branch,
                                  core.fmt.rt.Argument.new_debug,
                                  core.fmt.Arguments.new, alloc.fmt.format,
                                  core.hint.must_use]

theorem term_sort_list_get_terminates_of_smaller
    (list index : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.ListGet list index) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.ListGet list index)) := by
  have listSmaller : TermStrictlySmaller list (.ListGet list index) := by
    simp [TermStrictlySmaller]
    omega
  have indexSmaller : TermStrictlySmaller index (.ListGet list index) := by
    simp [TermStrictlySmaller]
  have listTerminates := smallerTerminates list listSmaller
  have indexRequired := require_sort_terminates_of_term_sort_terminates
    index .Int VcTermSort.SortContext.ListIndex
    (smallerTerminates index indexSmaller)
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases indexObserved :
      VcTermSort.require_sort index .Int VcTermSort.SortContext.ListIndex with
  | div => simp [Terminates, indexObserved] at indexRequired
  | fail error => simp [Terminates, indexObserved]
  | ok indexChecked =>
      cases indexChecked with
      | Err error =>
          simp [Terminates, indexObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          cases listObserved : VcTermSort.Term.sort_typed list with
          | div => simp [Terminates, listObserved] at listTerminates
          | fail error => simp [Terminates, indexObserved, listObserved,
              core.result.Result.Insts.CoreOpsTry.branch]
          | ok listChecked =>
              cases listChecked with
              | Err error =>
                  simp [Terminates, indexObserved, listObserved,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
              | Ok listSort =>
                  cases listSort <;>
                    simp [Terminates, indexObserved, listObserved,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      Str.Insts.AllocBorrowToOwnedString.to_owned]

theorem term_sort_list_contains_terminates_of_smaller
    (list value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.ListContains list value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.ListContains list value)) := by
  have listSmaller : TermStrictlySmaller list (.ListContains list value) := by
    simp [TermStrictlySmaller]
    omega
  have valueSmaller : TermStrictlySmaller value (.ListContains list value) := by
    simp [TermStrictlySmaller]
  have listTerminates := smallerTerminates list listSmaller
  have valueTerminates := smallerTerminates value valueSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases listObserved : VcTermSort.Term.sort_typed list with
  | div => simp [Terminates, listObserved] at listTerminates
  | fail error => simp [Terminates, listObserved]
  | ok listChecked =>
      cases listChecked with
      | Err error =>
          simp [Terminates, listObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok listSort =>
          cases listSort <;>
            simp [Terminates, listObserved,
              core.result.Result.Insts.CoreOpsTry.branch,
              Str.Insts.AllocBorrowToOwnedString.to_owned]
          case List element =>
            have valueRequired := require_sort_terminates_of_term_sort_terminates
              value element VcTermSort.SortContext.ListMembershipValue valueTerminates
            cases valueObserved :
                VcTermSort.require_sort value element
                  VcTermSort.SortContext.ListMembershipValue with
            | div => simp [Terminates, valueObserved] at valueRequired
            | fail error => simp
            | ok valueChecked =>
                cases valueChecked with
                | Err error =>
                    simp [
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                | Ok checkedUnit => simp

theorem term_sort_set_contains_terminates_of_smaller
    (set value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.SetContains set value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.SetContains set value)) := by
  have setSmaller : TermStrictlySmaller set (.SetContains set value) := by
    simp [TermStrictlySmaller]
    omega
  have valueSmaller : TermStrictlySmaller value (.SetContains set value) := by
    simp [TermStrictlySmaller]
  have setTerminates := smallerTerminates set setSmaller
  have valueTerminates := smallerTerminates value valueSmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases setObserved : VcTermSort.Term.sort_typed set with
  | div => simp [Terminates, setObserved] at setTerminates
  | fail error => simp [Terminates, setObserved]
  | ok setChecked =>
      cases setChecked with
      | Err error =>
          simp [Terminates, setObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok setSort =>
          cases setSort <;>
            simp [Terminates, setObserved,
              core.result.Result.Insts.CoreOpsTry.branch,
              Str.Insts.AllocBorrowToOwnedString.to_owned]
          case Set element =>
            have valueRequired := require_sort_terminates_of_term_sort_terminates
              value element VcTermSort.SortContext.SetMembershipValue valueTerminates
            cases valueObserved :
                VcTermSort.require_sort value element
                  VcTermSort.SortContext.SetMembershipValue with
            | div => simp [Terminates, valueObserved] at valueRequired
            | fail error => simp
            | ok valueChecked =>
                cases valueChecked with
                | Err error =>
                    simp [
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                | Ok checkedUnit => simp

theorem term_sort_dict_contains_terminates_of_smaller
    (dict key : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.DictContains dict key) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.DictContains dict key)) := by
  have dictSmaller : TermStrictlySmaller dict (.DictContains dict key) := by
    simp [TermStrictlySmaller]
    omega
  have keySmaller : TermStrictlySmaller key (.DictContains dict key) := by
    simp [TermStrictlySmaller]
  have dictTerminates := smallerTerminates dict dictSmaller
  have keyTerminates := smallerTerminates key keySmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases dictObserved : VcTermSort.Term.sort_typed dict with
  | div => simp [Terminates, dictObserved] at dictTerminates
  | fail error => simp [Terminates, dictObserved]
  | ok dictChecked =>
      cases dictChecked with
      | Err error =>
          simp [Terminates, dictObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok dictSort =>
          cases dictSort <;>
            simp [Terminates, dictObserved,
              core.result.Result.Insts.CoreOpsTry.branch,
              Str.Insts.AllocBorrowToOwnedString.to_owned]
          case Dict expected valueSort =>
            have keyRequired := require_sort_terminates_of_term_sort_terminates
              key expected VcTermSort.SortContext.DictionaryMembershipKey keyTerminates
            cases keyObserved :
                VcTermSort.require_sort key expected
                  VcTermSort.SortContext.DictionaryMembershipKey with
            | div => simp [Terminates, keyObserved] at keyRequired
            | fail error => simp
            | ok keyChecked =>
                cases keyChecked with
                | Err error =>
                    simp [
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                | Ok checkedUnit => simp

theorem term_sort_dict_get_terminates_of_smaller
    (dict key : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.DictGet dict key) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.DictGet dict key)) := by
  have dictSmaller : TermStrictlySmaller dict (.DictGet dict key) := by
    simp [TermStrictlySmaller]
    omega
  have keySmaller : TermStrictlySmaller key (.DictGet dict key) := by
    simp [TermStrictlySmaller]
  have dictTerminates := smallerTerminates dict dictSmaller
  have keyTerminates := smallerTerminates key keySmaller
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases dictObserved : VcTermSort.Term.sort_typed dict with
  | div => simp [Terminates, dictObserved] at dictTerminates
  | fail error => simp [Terminates, dictObserved]
  | ok dictChecked =>
      cases dictChecked with
      | Err error =>
          simp [Terminates, dictObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok dictSort =>
          cases dictSort <;>
            simp [Terminates, dictObserved,
              core.result.Result.Insts.CoreOpsTry.branch,
              Str.Insts.AllocBorrowToOwnedString.to_owned]
          case Dict expected valueSort =>
            have keyRequired := require_sort_terminates_of_term_sort_terminates
              key expected VcTermSort.SortContext.DictionaryLookupKey keyTerminates
            cases keyObserved :
                VcTermSort.require_sort key expected
                  VcTermSort.SortContext.DictionaryLookupKey with
            | div => simp [Terminates, keyObserved] at keyRequired
            | fail error => simp
            | ok keyChecked =>
                cases keyChecked with
                | Err error =>
                    simp [
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                | Ok checkedUnit => simp

/-- IntEnum projection first checks the exact source constructor and only
    recurses for a descriptor-carrying value. The extracted box borrow is
    identity, so every rejected shape is an immediate concrete diagnostic. -/
theorem term_sort_int_enum_projection_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.IntEnumProjection value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.IntEnumProjection value)) := by
  have valueSmaller : TermStrictlySmaller value (.IntEnumProjection value) := by
    simp [TermStrictlySmaller]
  have valueTerminates := smallerTerminates value valueSmaller
  rw [VcTermSort.Term.sort_typed.eq_def (.IntEnumProjection value)]
  simp only
  rw [box_as_ref_refines]
  cases value <;>
    simp [Terminates, Str.Insts.AllocBorrowToOwnedString.to_owned]
  case IntEnumValue descriptor payload =>
    cases observed :
        VcTermSort.Term.sort_typed (.IntEnumValue descriptor payload) with
    | div => simp [Terminates, observed] at valueTerminates
    | fail error => simp [Terminates, observed]
    | ok checked =>
        cases checked <;>
          simp [Terminates, observed,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- IntEnum domain has the same constructor-guarded recursive shape as
    projection and returns a Boolean sort on the accepted path. -/
theorem term_sort_int_enum_domain_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.IntEnumDomain value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.IntEnumDomain value)) := by
  have valueSmaller : TermStrictlySmaller value (.IntEnumDomain value) := by
    simp [TermStrictlySmaller]
  have valueTerminates := smallerTerminates value valueSmaller
  rw [VcTermSort.Term.sort_typed.eq_def (.IntEnumDomain value)]
  simp only
  rw [box_as_ref_refines]
  cases value <;>
    simp [Terminates, Str.Insts.AllocBorrowToOwnedString.to_owned]
  case IntEnumValue descriptor payload =>
    cases observed :
        VcTermSort.Term.sort_typed (.IntEnumValue descriptor payload) with
    | div => simp [Terminates, observed] at valueTerminates
    | fail error => simp [Terminates, observed]
    | ok checked =>
        cases checked <;>
          simp [Terminates, observed,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

set_option maxHeartbeats 800000

/-- IntEnum identity accepts only two descriptor-carrying values, then
    preserves the exact left-to-right recursive `?` order. -/
theorem term_sort_int_enum_identity_terminates_of_smaller
    (left right : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.IntEnumIdentity left right) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.IntEnumIdentity left right)) := by
  have leftSmaller :
      TermStrictlySmaller left (.IntEnumIdentity left right) := by
    simp [TermStrictlySmaller]
    omega
  have rightSmaller :
      TermStrictlySmaller right (.IntEnumIdentity left right) := by
    simp [TermStrictlySmaller]
  have leftTerminates := smallerTerminates left leftSmaller
  have rightTerminates := smallerTerminates right rightSmaller
  rw [VcTermSort.Term.sort_typed.eq_def (.IntEnumIdentity left right)]
  simp only
  rw [box_as_ref_refines]
  cases left
  case IntEnumValue leftDescriptor leftPayload =>
    rw [box_as_ref_refines]
    cases right
    case IntEnumValue rightDescriptor rightPayload =>
      cases leftObserved : VcTermSort.Term.sort_typed
          (.IntEnumValue leftDescriptor leftPayload) with
      | div => simp [Terminates, leftObserved] at leftTerminates
      | fail error => simp [Terminates, leftObserved]
      | ok leftChecked =>
          cases leftChecked with
          | Err error =>
              simp [Terminates, leftObserved,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          | Ok leftSort =>
              cases rightObserved : VcTermSort.Term.sort_typed
                  (.IntEnumValue rightDescriptor rightPayload) with
              | div => simp [Terminates, rightObserved] at rightTerminates
              | fail error =>
                  simp [Terminates, leftObserved, rightObserved,
                    core.result.Result.Insts.CoreOpsTry.branch]
              | ok rightChecked =>
                  cases rightChecked <;>
                    simp [Terminates, leftObserved, rightObserved,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
    all_goals simp [Terminates, Str.Insts.AllocBorrowToOwnedString.to_owned]
  all_goals simp [Terminates, Str.Insts.AllocBorrowToOwnedString.to_owned]

/-- IntEnum values first validate their finite descriptor and then sort their
    numeric payload, the constructor's sole strict structural child. -/
theorem term_sort_int_enum_value_terminates_of_smaller
    (descriptor : VcTermSort.IntEnumDescriptor)
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.IntEnumValue descriptor value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.IntEnumValue descriptor value)) := by
  have valueSmaller :
      TermStrictlySmaller value (.IntEnumValue descriptor value) := by
    simp [TermStrictlySmaller]
  have valueTerminates := smallerTerminates value valueSmaller
  have requiredTerminates :=
    require_sort_terminates_of_term_sort_terminates
      value .Int VcTermSort.SortContext.IntEnumNumericValue valueTerminates
  have descriptorTerminates :=
    validate_int_enum_descriptor_terminates descriptor
  rw [VcTermSort.Term.sort_typed.eq_def (.IntEnumValue descriptor value)]
  simp only
  cases descriptorObserved :
      VcTermSort.validate_int_enum_descriptor descriptor with
  | div => simp [Terminates, descriptorObserved] at descriptorTerminates
  | fail descriptorError => simp [Terminates, descriptorObserved]
  | ok descriptorChecked =>
      cases descriptorChecked with
      | Err error =>
          simp [Terminates, descriptorObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          cases requiredObserved : VcTermSort.require_sort
              value .Int VcTermSort.SortContext.IntEnumNumericValue with
          | div => simp [Terminates, requiredObserved] at requiredTerminates
          | fail requiredError =>
              simp [Terminates, descriptorObserved, requiredObserved,
                core.result.Result.Insts.CoreOpsTry.branch]
          | ok requiredChecked =>
              cases requiredChecked <;>
                simp [Terminates, descriptorObserved, requiredObserved,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

set_option maxHeartbeats 200000

/-- Variables do not recurse: their source-declared structural sort is
    validated for list-element admissibility where required and cloned
    exactly. -/
theorem term_sort_variable_terminates
    (variableName : String) (sort : VcTermSort.Sort) :
    Terminates (VcTermSort.Term.sort_typed (.Variable variableName sort)) := by
  rw [VcTermSort.Term.sort_typed.eq_def (.Variable variableName sort)]
  simp only
  cases sort
  case VariadicTuple element =>
    simp only
    have predicateTerminates :=
      is_variadic_tuple_element_sort_terminates element
    cases predicateObserved :
        VcTermSort.is_variadic_tuple_element_sort element with
    | div => simp [Terminates, predicateObserved] at predicateTerminates
    | fail error => simp [Terminates, predicateObserved]
    | ok accepted =>
        cases accepted with
        | true =>
            exact sort_clone_then_result_ok_terminates _
        | false =>
            rw [box_as_ref_refines]
            exact sort_clone_then_result_error_terminates _ _
  case List element =>
    simp only
    have predicateTerminates := is_list_element_sort_terminates element
    cases predicateObserved : VcTermSort.is_list_element_sort element with
    | div => simp [Terminates, predicateObserved] at predicateTerminates
    | fail error => simp [Terminates, predicateObserved]
    | ok accepted =>
        cases accepted <;> simp [Terminates, predicateObserved]
        · exact sort_clone_then_result_error_terminates _ _
        · exact sort_clone_then_result_ok_terminates _
  all_goals exact sort_clone_then_result_ok_terminates _

/-- Tuple indexing sorts its immediate child and then follows the exact
    generated slice lookup, structural clone, and lazy out-of-range diagnostic
    paths. Every continuation is concrete for either lookup outcome. -/
theorem term_sort_tuple_get_terminates_of_smaller
    (tuple : VcTermSort.Term) (index : Std.Usize)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.TupleGet tuple index) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.TupleGet tuple index)) := by
  have tupleSmaller : TermStrictlySmaller tuple (.TupleGet tuple index) := by
    simp [TermStrictlySmaller]
    omega
  have tupleTerminates := smallerTerminates tuple tupleSmaller
  rw [VcTermSort.Term.sort_typed.eq_def (.TupleGet tuple index)]
  simp only
  cases observed : VcTermSort.Term.sort_typed tuple with
  | div => simp [Terminates, observed] at tupleTerminates
  | fail error => simp [Terminates, observed]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, observed,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok tupleSort =>
          cases tupleSort <;>
            simp [Terminates, observed,
              core.result.Result.Insts.CoreOpsTry.branch,
              Str.Insts.AllocBorrowToOwnedString.to_owned]
          case Tuple elements =>
            cases lookupObserved : (VcTermSort.ModelVec.deref elements)[index]? with
            | none =>
                simp [Terminates, observed,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.slice.Slice.get,
                  core.slice.index.SliceIndexUsizeSlice,
                  lookupObserved, core.option.OptionShared0T.cloned,
                  core.option.Option.ok_or]
            | some element =>
                simp [Terminates, observed,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.slice.Slice.get,
                  core.slice.index.SliceIndexUsizeSlice,
                  lookupObserved, core.option.OptionShared0T.cloned,
                  core.option.Option.ok_or]
                exact sort_clone_then_result_ok_terminates element

/-- Boolean conjunction traverses the exact extracted operand vector; every
    loop continuation sorts a strict structural child. -/
theorem term_sort_and_terminates_of_smaller
    (values : VcTermSort.ModelVec VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.And values) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.And values)) := by
  have childrenSmaller : ∀ child,
      child ∈ (show List VcTermSort.Term from values) →
        TermStrictlySmaller child (.And values) := by
    intro child member
    unfold TermStrictlySmaller
    have childBelow := List.sizeOf_lt_of_mem member
    simp at childBelow ⊢
    omega
  have childrenTerminate := model_vec_deref_children_terminate_of_smaller
    values (.And values) smallerTerminates childrenSmaller
  have requiredTerminates := require_all_sorts_terminates
    (VcTermSort.ModelVec.deref values) .Bool VcTermSort.SortContext.BooleanOperand
    childrenTerminate
  rw [VcTermSort.Term.sort_typed.eq_def (.And values)]
  simp only
  exact require_sort_then_ok_terminates _ requiredTerminates .Bool

theorem term_sort_or_terminates_of_smaller
    (values : VcTermSort.ModelVec VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Or values) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Or values)) := by
  have childrenSmaller : ∀ child,
      child ∈ (show List VcTermSort.Term from values) →
        TermStrictlySmaller child (.Or values) := by
    intro child member
    unfold TermStrictlySmaller
    have childBelow := List.sizeOf_lt_of_mem member
    simp at childBelow ⊢
    omega
  have childrenTerminate := model_vec_deref_children_terminate_of_smaller
    values (.Or values) smallerTerminates childrenSmaller
  have requiredTerminates := require_all_sorts_terminates
    (VcTermSort.ModelVec.deref values) .Bool VcTermSort.SortContext.BooleanOperand
    childrenTerminate
  rw [VcTermSort.Term.sort_typed.eq_def (.Or values)]
  simp only
  exact require_sort_then_ok_terminates _ requiredTerminates .Bool

theorem term_sort_string_concat_terminates_of_smaller
    (values : VcTermSort.ModelVec VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.StringConcat values) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.StringConcat values)) := by
  have childrenSmaller : ∀ child,
      child ∈ (show List VcTermSort.Term from values) →
        TermStrictlySmaller child (.StringConcat values) := by
    intro child member
    unfold TermStrictlySmaller
    have childBelow := List.sizeOf_lt_of_mem member
    simp at childBelow ⊢
    omega
  have childrenTerminate := model_vec_deref_children_terminate_of_smaller
    values (.StringConcat values) smallerTerminates childrenSmaller
  have requiredTerminates := require_all_sorts_terminates
    (VcTermSort.ModelVec.deref values) .String
    VcTermSort.SortContext.StringConcatenationOperand childrenTerminate
  rw [VcTermSort.Term.sort_typed.eq_def (.StringConcat values)]
  simp only
  exact require_sort_then_ok_terminates _ requiredTerminates .String

theorem term_sort_bytes_concat_terminates_of_smaller
    (values : VcTermSort.ModelVec VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.BytesConcat values) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.BytesConcat values)) := by
  have childrenSmaller : ∀ child,
      child ∈ (show List VcTermSort.Term from values) →
        TermStrictlySmaller child (.BytesConcat values) := by
    intro child member
    unfold TermStrictlySmaller
    have childBelow := List.sizeOf_lt_of_mem member
    simp at childBelow ⊢
    omega
  have childrenTerminate := model_vec_deref_children_terminate_of_smaller
    values (.BytesConcat values) smallerTerminates childrenSmaller
  have requiredTerminates := require_all_sorts_terminates
    (VcTermSort.ModelVec.deref values) .Bytes
    VcTermSort.SortContext.BytesConcatenationOperand childrenTerminate
  rw [VcTermSort.Term.sort_typed.eq_def (.BytesConcat values)]
  simp only
  exact require_sort_then_ok_terminates _ requiredTerminates .Bytes

/-- Cloning a validated element sort preserves the exact sort consumed by the
    generated list traversal and returned by the list constructor. -/
theorem sort_clone_require_all_then_list_ok_terminates
    (values : Slice VcTermSort.Term) (elementSort : VcTermSort.Sort)
    (context : VcTermSort.SortContext)
    (requiredTerminates : Terminates
      (VcTermSort.require_all_sorts values elementSort context)) :
    Terminates (do
      let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone elementSort
      let r ← VcTermSort.require_all_sorts values cloned context
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (core.result.Result.Ok (VcTermSort.Sort.List cloned))
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual) := by
  rw [sort_clone_exact]
  exact require_sort_then_ok_terminates _ requiredTerminates (.List elementSort)

theorem sort_clone_require_all_then_dict_keys_ok_terminates
    (values : Slice VcTermSort.Term) (keySort : VcTermSort.Sort)
    (context : VcTermSort.SortContext)
    (requiredTerminates : Terminates
      (VcTermSort.require_all_sorts values keySort context)) :
    Terminates (do
      let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone keySort
      let r ← VcTermSort.require_all_sorts values cloned context
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (core.result.Result.Ok (VcTermSort.Sort.DictKeys cloned))
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual) := by
  rw [sort_clone_exact]
  exact require_sort_then_ok_terminates _ requiredTerminates
    (.DictKeys keySort)

/-- List construction validates the declared element sort, clones it exactly,
    and traverses every extracted element in source order. Every recursive sort
    call is therefore on a strict structural child of the list term. -/
theorem term_sort_list_terminates_of_smaller
    (elementSort : VcTermSort.Sort)
    (values : VcTermSort.ModelVec VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.List elementSort values) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.List elementSort values)) := by
  have childrenSmaller : ∀ child,
      child ∈ (show List VcTermSort.Term from values) →
        TermStrictlySmaller child (.List elementSort values) := by
    intro child member
    unfold TermStrictlySmaller
    have childBelow := List.sizeOf_lt_of_mem member
    simp at childBelow ⊢
    omega
  have childrenTerminate := model_vec_deref_children_terminate_of_smaller
    values (.List elementSort values) smallerTerminates childrenSmaller
  have requiredTerminates := require_all_sorts_terminates
    (VcTermSort.ModelVec.deref values) elementSort VcTermSort.SortContext.ListElement
    childrenTerminate
  rw [VcTermSort.Term.sort_typed.eq_def (.List elementSort values)]
  simp only
  have predicateTerminates := is_list_element_sort_terminates elementSort
  cases predicateObserved : VcTermSort.is_list_element_sort elementSort with
  | div => simp [Terminates, predicateObserved] at predicateTerminates
  | fail error => simp [Terminates, predicateObserved]
  | ok accepted =>
      cases accepted with
      | true =>
          apply sort_clone_require_all_then_list_ok_terminates
          exact requiredTerminates
      | false =>
          exact sort_clone_then_result_error_terminates _ _

theorem term_sort_variadic_tuple_terminates_of_smaller
    (elementSort : VcTermSort.Sort)
    (values : VcTermSort.ModelVec VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.VariadicTuple elementSort values) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed
      (.VariadicTuple elementSort values)) := by
  have childrenSmaller : ∀ child,
      child ∈ (show List VcTermSort.Term from values) →
        TermStrictlySmaller child (.VariadicTuple elementSort values) := by
    intro child member
    unfold TermStrictlySmaller
    have childBelow := List.sizeOf_lt_of_mem member
    simp at childBelow ⊢
    omega
  have childrenTerminate := model_vec_deref_children_terminate_of_smaller
    values (.VariadicTuple elementSort values)
    smallerTerminates childrenSmaller
  have requiredTerminates := require_variadic_tuple_element_sorts_terminates
    (VcTermSort.ModelVec.deref values) elementSort childrenTerminate
  have predicateTerminates :=
    is_variadic_tuple_element_sort_terminates elementSort
  rw [VcTermSort.Term.sort_typed.eq_def
    (.VariadicTuple elementSort values)]
  simp only
  cases predicateObserved :
      VcTermSort.is_variadic_tuple_element_sort elementSort with
  | div => simp [Terminates, predicateObserved] at predicateTerminates
  | fail error => simp [Terminates, predicateObserved]
  | ok accepted =>
      cases accepted with
      | false =>
          exact sort_clone_then_result_error_terminates _ _
      | true =>
          cases requiredObserved :
              VcTermSort.require_variadic_tuple_element_sorts
                (VcTermSort.ModelVec.deref values) elementSort with
          | div => simp [Terminates, requiredObserved] at requiredTerminates
          | fail error => simp [Terminates, requiredObserved]
          | ok checked =>
              cases checked with
              | Err error =>
                  simp [Terminates, requiredObserved,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
              | Ok unit =>
                  simp only [bind_tc_ok, Bool.true_eq, ↓reduceIte,
                    core.result.Result.Insts.CoreOpsTry.branch]
                  exact result_bind_terminates
                    (VcTermSort.Sort.Insts.CoreCloneClone.clone elementSort)
                    (fun cloned => ok (core.result.Result.Ok
                      (VcTermSort.Sort.VariadicTuple cloned)))
                    (sort_clone_terminates elementSort)
                    (by intro cloned; simp [Terminates])

theorem term_sort_variadic_tuple_length_terminates_of_smaller
    (value : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.VariadicTupleLength value) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.VariadicTupleLength value)) := by
  have valueTerminates := smallerTerminates value (by
    simp [TermStrictlySmaller])
  rw [VcTermSort.Term.sort_typed.eq_def (.VariadicTupleLength value)]
  simp only
  cases observed : VcTermSort.Term.sort_typed value with
  | div => simp [Terminates, observed] at valueTerminates
  | fail error => simp [Terminates, observed]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, observed,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok actual =>
          cases actual <;>
            simp [Terminates, observed,
              core.result.Result.Insts.CoreOpsTry.branch]

theorem term_sort_variadic_tuple_get_terminates_of_smaller
    (tuple index : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.VariadicTupleGet tuple index) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.VariadicTupleGet tuple index)) := by
  have indexTerminates := smallerTerminates index (by
    simp [TermStrictlySmaller])
  have tupleTerminates := smallerTerminates tuple (by
    simp [TermStrictlySmaller]
    omega)
  have indexRequired := require_sort_terminates_of_term_sort_terminates
    index .Int VcTermSort.SortContext.VariadicTupleIndex indexTerminates
  rw [VcTermSort.Term.sort_typed.eq_def (.VariadicTupleGet tuple index)]
  simp only
  cases indexObserved : VcTermSort.require_sort index .Int
      VcTermSort.SortContext.VariadicTupleIndex with
  | div => simp [Terminates, indexObserved] at indexRequired
  | fail error => simp [Terminates, indexObserved]
  | ok indexChecked =>
      cases indexChecked with
      | Err error =>
          simp [Terminates, indexObserved,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok unit =>
          cases tupleObserved : VcTermSort.Term.sort_typed tuple with
          | div => simp [Terminates, tupleObserved] at tupleTerminates
          | fail error =>
              simp [Terminates, indexObserved, tupleObserved,
                core.result.Result.Insts.CoreOpsTry.branch]
          | ok tupleChecked =>
              cases tupleChecked with
              | Err error =>
                  simp [Terminates, indexObserved, tupleObserved,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
              | Ok actual =>
                  cases actual <;>
                    simp [Terminates, indexObserved, tupleObserved,
                      core.result.Result.Insts.CoreOpsTry.branch]

theorem term_sort_variadic_tuple_slice_terminates_of_smaller
    (source : VcTermSort.Term) (lower upper : Option Std.I128)
    (step : core.num.nonzero.NonZero Std.I128
      core.num.niche_types.NonZeroI128Inner)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.VariadicTupleSlice source lower upper step) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed
      (.VariadicTupleSlice source lower upper step)) := by
  have sourceTerminates := smallerTerminates source (by
    simp [TermStrictlySmaller]
    omega)
  rw [VcTermSort.Term.sort_typed.eq_def
    (.VariadicTupleSlice source lower upper step)]
  simp only
  cases observed : VcTermSort.Term.sort_typed source with
  | div => simp [Terminates, observed] at sourceTerminates
  | fail error => simp [Terminates, observed]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates, observed,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok actual =>
          cases actual <;>
            simp [Terminates, observed,
              core.result.Result.Insts.CoreOpsTry.branch]

/-- Tuple construction collects the exact structural sorts of every source
    element. Each loop call sorts only an immediate strict child. -/
theorem term_sort_tuple_terminates_of_smaller
    (values : VcTermSort.ModelVec VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.Tuple values) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.Tuple values)) := by
  have childrenSmaller : ∀ child,
      child ∈ (show List VcTermSort.Term from values) →
        TermStrictlySmaller child (.Tuple values) := by
    intro child member
    unfold TermStrictlySmaller
    have childBelow := List.sizeOf_lt_of_mem member
    simp at childBelow ⊢
    omega
  have childrenTerminate := model_vec_deref_children_terminate_of_smaller
    values (.Tuple values) smallerTerminates childrenSmaller
  have collectedTerminates := collect_sorts_terminates
    (VcTermSort.ModelVec.deref values) childrenTerminate
  rw [VcTermSort.Term.sort_typed.eq_def (.Tuple values)]
  simp only
  cases observed : VcTermSort.collect_sorts
      (VcTermSort.ModelVec.deref values) with
  | div => simp [Terminates, observed] at collectedTerminates
  | fail error => simp [Terminates, observed]
  | ok checked =>
      cases checked <;>
        simp [Terminates, observed,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Predicate instances traverse each source argument exactly once after the
    source-level name and nonempty-vector guards. Every recursive sort call is
    on an immediate strict child. -/
theorem term_sort_predicate_instance_terminates_of_smaller
    (predicate : String)
    (arguments : VcTermSort.ModelVec VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.PredicateInstance predicate arguments) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates
      (VcTermSort.Term.sort_typed (.PredicateInstance predicate arguments)) := by
  have childrenSmaller : ∀ child,
      child ∈ (show List VcTermSort.Term from arguments) →
        TermStrictlySmaller child (.PredicateInstance predicate arguments) := by
    intro child member
    unfold TermStrictlySmaller
    have childBelow := List.sizeOf_lt_of_mem member
    simp at childBelow ⊢
    omega
  have childrenTerminate := model_vec_deref_children_terminate_of_smaller
    arguments (.PredicateInstance predicate arguments)
    smallerTerminates childrenSmaller
  have requiredTerminates := require_predicate_argument_sorts_terminates
    (VcTermSort.ModelVec.deref arguments) childrenTerminate
  rw [VcTermSort.Term.sort_typed.eq_def (.PredicateInstance predicate arguments)]
  simp only
  by_cases predicateEmpty : predicate = ""
  · simp [Terminates, alloc.string.String.is_empty, predicateEmpty,
      Str.Insts.AllocBorrowToOwnedString.to_owned]
  · by_cases argumentsEmpty : arguments.isEmpty
    · simp [Terminates, alloc.string.String.is_empty, predicateEmpty,
        VcTermSort.ModelVec.is_empty, argumentsEmpty,
        Str.Insts.AllocBorrowToOwnedString.to_owned]
    · simp [alloc.string.String.is_empty, predicateEmpty,
        VcTermSort.ModelVec.is_empty, argumentsEmpty]
      cases observed : VcTermSort.require_predicate_argument_sorts
          (VcTermSort.ModelVec.deref arguments) with
      | div => simp [Terminates, observed] at requiredTerminates
      | fail error => simp [Terminates, observed]
      | ok checked =>
          cases checked <;>
            simp [Terminates, observed,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Dictionary-key collections accept exactly the source-declared key sorts
    and check every key in the exact extracted vector traversal. -/
theorem term_sort_dict_keys_terminates_of_smaller
    (keySort : VcTermSort.Sort)
    (values : VcTermSort.ModelVec VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.DictKeys keySort values) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed (.DictKeys keySort values)) := by
  have childrenSmaller : ∀ child,
      child ∈ (show List VcTermSort.Term from values) →
        TermStrictlySmaller child (.DictKeys keySort values) := by
    intro child member
    unfold TermStrictlySmaller
    have childBelow := List.sizeOf_lt_of_mem member
    simp at childBelow ⊢
    omega
  have childrenTerminate := model_vec_deref_children_terminate_of_smaller
    values (.DictKeys keySort values) smallerTerminates childrenSmaller
  have requiredTerminates := require_all_sorts_terminates
    (VcTermSort.ModelVec.deref values) keySort VcTermSort.SortContext.DictionaryKey
    childrenTerminate
  rw [VcTermSort.Term.sort_typed.eq_def (.DictKeys keySort values)]
  simp only
  have predicateTerminates := is_finite_dict_key_sort_terminates keySort
  cases predicateObserved : VcTermSort.is_finite_dict_key_sort keySort with
  | div => simp [Terminates, predicateObserved] at predicateTerminates
  | fail error => simp [Terminates, predicateObserved]
  | ok accepted =>
      cases accepted with
      | true =>
          apply sort_clone_require_all_then_dict_keys_ok_terminates
          exact requiredTerminates
      | false =>
          exact sort_clone_then_result_error_terminates _ _

theorem term_sort_finite_dict_terminates_of_smaller
    (keySort valueSort : VcTermSort.Sort)
    (entries : VcTermSort.ModelVec (VcTermSort.Term × VcTermSort.Term))
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.FiniteDict keySort valueSort entries) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed
      (.FiniteDict keySort valueSort entries)) := by
  have childrenTerminate : ∀ entry,
      entry ∈ (VcTermSort.ModelVec.deref entries).val →
      Terminates (VcTermSort.Term.sort_typed entry.1) ∧
      Terminates (VcTermSort.Term.sort_typed entry.2) := by
    intro entry member
    change entry ∈ List.take Usize.max
      (show List (VcTermSort.Term × VcTermSort.Term) from entries) at member
    have sourceMember := List.mem_of_mem_take member
    have entryBelow := List.sizeOf_lt_of_mem sourceMember
    obtain ⟨key, value⟩ := entry
    constructor
    · apply smallerTerminates key
      unfold TermStrictlySmaller
      simp at entryBelow ⊢
      omega
    · apply smallerTerminates value
      unfold TermStrictlySmaller
      simp at entryBelow ⊢
      omega
  have requiredTerminates := require_finite_dict_entry_sorts_terminates
    (VcTermSort.ModelVec.deref entries) keySort valueSort childrenTerminate
  have acceptedKeyTerminates : Terminates (do
      let valueValid ← VcTermSort.is_finite_dict_value_sort valueSort
      if valueValid
      then
        let checked ← VcTermSort.require_finite_dict_entry_sorts
          (VcTermSort.ModelVec.deref entries) keySort valueSort
        let flow ← core.result.Result.Insts.CoreOpsTry.branch checked
        match flow with
        | core.ops.control_flow.ControlFlow.Continue _ => do
            let clonedKey ←
              VcTermSort.Sort.Insts.CoreCloneClone.clone keySort
            let clonedValue ←
              VcTermSort.Sort.Insts.CoreCloneClone.clone valueSort
            ok (core.result.Result.Ok
              (VcTermSort.Sort.FiniteDict clonedKey clonedValue))
        | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual
      else
        let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone valueSort
        ok (core.result.Result.Err
          (VcTermSort.SortError.FiniteDictionaryValueSortUnsupported cloned))) := by
    have valuePredicateTerminates :=
      is_finite_dict_value_sort_terminates valueSort
    cases valueObserved : VcTermSort.is_finite_dict_value_sort valueSort with
    | div => simp [Terminates, valueObserved] at valuePredicateTerminates
    | fail valueError => simp [Terminates, valueObserved]
    | ok valueValid =>
        cases valueValid with
        | false =>
            simpa [valueObserved] using
              sort_clone_then_result_error_terminates valueSort
                VcTermSort.SortError.FiniteDictionaryValueSortUnsupported
        | true =>
            cases requiredObserved : VcTermSort.require_finite_dict_entry_sorts
                (VcTermSort.ModelVec.deref entries) keySort valueSort with
            | div => simp [Terminates, requiredObserved] at requiredTerminates
            | fail requiredError =>
                simp [Terminates, valueObserved, requiredObserved]
            | ok requiredChecked =>
                cases requiredChecked with
                | Err requiredError =>
                    simp [Terminates, valueObserved, requiredObserved,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                | Ok requiredUnit =>
                    rw [sort_clone_exact, sort_clone_exact]
                    simp [Terminates, valueObserved, requiredObserved,
                      core.result.Result.Insts.CoreOpsTry.branch]
  have tailTerminates (exactReferenceKeys : Bool) : Terminates (do
      let keyValid ← VcTermSort.is_finite_dict_key_sort keySort
      if keyValid
      then
        let valueValid ← VcTermSort.is_finite_dict_value_sort valueSort
        if valueValid
        then
          let checked ← VcTermSort.require_finite_dict_entry_sorts
            (VcTermSort.ModelVec.deref entries) keySort valueSort
          let flow ← core.result.Result.Insts.CoreOpsTry.branch checked
          match flow with
          | core.ops.control_flow.ControlFlow.Continue _ => do
              let clonedKey ←
                VcTermSort.Sort.Insts.CoreCloneClone.clone keySort
              let clonedValue ←
                VcTermSort.Sort.Insts.CoreCloneClone.clone valueSort
              ok (core.result.Result.Ok
                (VcTermSort.Sort.FiniteDict clonedKey clonedValue))
          | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual
        else
          let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone valueSort
          ok (core.result.Result.Err
            (VcTermSort.SortError.FiniteDictionaryValueSortUnsupported cloned))
      else if exactReferenceKeys
      then
        let valueValid ← VcTermSort.is_finite_dict_value_sort valueSort
        if valueValid
        then
          let checked ← VcTermSort.require_finite_dict_entry_sorts
            (VcTermSort.ModelVec.deref entries) keySort valueSort
          let flow ← core.result.Result.Insts.CoreOpsTry.branch checked
          match flow with
          | core.ops.control_flow.ControlFlow.Continue _ => do
              let clonedKey ←
                VcTermSort.Sort.Insts.CoreCloneClone.clone keySort
              let clonedValue ←
                VcTermSort.Sort.Insts.CoreCloneClone.clone valueSort
              ok (core.result.Result.Ok
                (VcTermSort.Sort.FiniteDict clonedKey clonedValue))
          | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual
        else
          let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone valueSort
          ok (core.result.Result.Err
            (VcTermSort.SortError.FiniteDictionaryValueSortUnsupported cloned))
      else
        let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone keySort
        ok (core.result.Result.Err
          (VcTermSort.SortError.FiniteDictionaryKeySortUnsupported cloned))) := by
    have keyPredicateTerminates := is_finite_dict_key_sort_terminates keySort
    cases keyObserved : VcTermSort.is_finite_dict_key_sort keySort with
    | div => simp [Terminates, keyObserved] at keyPredicateTerminates
    | fail keyError => simp [Terminates, keyObserved]
    | ok keyValid =>
        cases keyValid with
        | true => simpa [keyObserved] using acceptedKeyTerminates
        | false =>
            cases exactReferenceKeys with
            | true => simpa [keyObserved] using acceptedKeyTerminates
            | false =>
                simpa [keyObserved] using
                  sort_clone_then_result_error_terminates keySort
                    VcTermSort.SortError.FiniteDictionaryKeySortUnsupported
  rw [VcTermSort.Term.sort_typed.eq_def (.FiniteDict keySort valueSort entries)]
  simp only
  apply result_bind_terminates
  · exact sort_partial_eq_terminates keySort VcTermSort.Sort.Reference
  · intro isReference
    cases isReference with
    | false =>
        apply result_bind_terminates
        · simp [Terminates]
        · intro exactReferenceKeys
          apply result_bind_terminates
          · exact is_finite_dict_key_sort_terminates keySort
          · intro keyValid
            cases keyValid with
            | false =>
                cases exactReferenceKeys with
                | false =>
                    exact sort_clone_then_result_error_terminates keySort
                      VcTermSort.SortError.FiniteDictionaryKeySortUnsupported
                | true =>
                    apply result_bind_terminates
                    · exact is_finite_dict_value_sort_terminates valueSort
                    · intro valueValid
                      cases valueValid with
                      | false =>
                          exact sort_clone_then_result_error_terminates valueSort
                            VcTermSort.SortError.FiniteDictionaryValueSortUnsupported
                      | true =>
                          apply result_bind_terminates
                          · exact requiredTerminates
                          · intro checked
                            cases checked with
                            | Err error =>
                                simp [Terminates,
                                  core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                            | Ok checkedUnit =>
                                apply result_bind_terminates
                                · simp [Terminates,
                                    core.result.Result.Insts.CoreOpsTry.branch]
                                · intro flow
                                  cases flow with
                                  | Continue value =>
                                      apply result_bind_terminates
                                      · exact sort_clone_terminates keySort
                                      · intro clonedKey
                                        apply result_bind_terminates
                                        · exact sort_clone_terminates valueSort
                                        · intro clonedValue
                                          simp [Terminates]
                                  | Break residual =>
                                      cases residual with
                                      | Ok impossible => exact nomatch impossible
                                      | Err error =>
                                          simp [Terminates,
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            | true =>
                apply result_bind_terminates
                · exact is_finite_dict_value_sort_terminates valueSort
                · intro valueValid
                  cases valueValid with
                  | false =>
                      exact sort_clone_then_result_error_terminates valueSort
                        VcTermSort.SortError.FiniteDictionaryValueSortUnsupported
                  | true =>
                      apply result_bind_terminates
                      · exact requiredTerminates
                      · intro checked
                        cases checked with
                        | Err error =>
                            simp [Terminates,
                              core.result.Result.Insts.CoreOpsTry.branch,
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                        | Ok checkedUnit =>
                            apply result_bind_terminates
                            · simp [Terminates,
                                core.result.Result.Insts.CoreOpsTry.branch]
                            · intro flow
                              cases flow with
                              | Continue value =>
                                  apply result_bind_terminates
                                  · exact sort_clone_terminates keySort
                                  · intro clonedKey
                                    apply result_bind_terminates
                                    · exact sort_clone_terminates valueSort
                                    · intro clonedValue
                                      simp [Terminates]
                              | Break residual =>
                                  cases residual with
                                  | Ok impossible => exact nomatch impossible
                                  | Err error =>
                                      simp [Terminates,
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
    | true =>
        apply result_bind_terminates
        · exact all_nominal_reference_keys_terminates
            (VcTermSort.ModelVec.deref entries)
        · intro exactReferenceKeys
          apply result_bind_terminates
          · exact is_finite_dict_key_sort_terminates keySort
          · intro keyValid
            cases keyValid with
            | false =>
                cases exactReferenceKeys with
                | false =>
                    exact sort_clone_then_result_error_terminates keySort
                      VcTermSort.SortError.FiniteDictionaryKeySortUnsupported
                | true =>
                    apply result_bind_terminates
                    · exact is_finite_dict_value_sort_terminates valueSort
                    · intro valueValid
                      cases valueValid with
                      | false =>
                          exact sort_clone_then_result_error_terminates valueSort
                            VcTermSort.SortError.FiniteDictionaryValueSortUnsupported
                      | true =>
                          apply result_bind_terminates
                          · exact requiredTerminates
                          · intro checked
                            cases checked with
                            | Err error =>
                                simp [Terminates,
                                  core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                            | Ok checkedUnit =>
                                apply result_bind_terminates
                                · simp [Terminates,
                                    core.result.Result.Insts.CoreOpsTry.branch]
                                · intro flow
                                  cases flow with
                                  | Continue value =>
                                      apply result_bind_terminates
                                      · exact sort_clone_terminates keySort
                                      · intro clonedKey
                                        apply result_bind_terminates
                                        · exact sort_clone_terminates valueSort
                                        · intro clonedValue
                                          simp [Terminates]
                                  | Break residual =>
                                      cases residual with
                                      | Ok impossible => exact nomatch impossible
                                      | Err error =>
                                          simp [Terminates,
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            | true =>
                apply result_bind_terminates
                · exact is_finite_dict_value_sort_terminates valueSort
                · intro valueValid
                  cases valueValid with
                  | false =>
                      exact sort_clone_then_result_error_terminates valueSort
                        VcTermSort.SortError.FiniteDictionaryValueSortUnsupported
                  | true =>
                      apply result_bind_terminates
                      · exact requiredTerminates
                      · intro checked
                        cases checked with
                        | Err error =>
                            simp [Terminates,
                              core.result.Result.Insts.CoreOpsTry.branch,
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                        | Ok checkedUnit =>
                            apply result_bind_terminates
                            · simp [Terminates,
                                core.result.Result.Insts.CoreOpsTry.branch]
                            · intro flow
                              cases flow with
                              | Continue value =>
                                  apply result_bind_terminates
                                  · exact sort_clone_terminates keySort
                                  · intro clonedKey
                                    apply result_bind_terminates
                                    · exact sort_clone_terminates valueSort
                                    · intro clonedValue
                                      simp [Terminates]
                              | Break residual =>
                                  cases residual with
                                  | Ok impossible => exact nomatch impossible
                                  | Err error =>
                                      simp [Terminates,
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

theorem term_sort_permission_mask_transition_terminates_of_smaller
    (preMask postMask : Std.U32) (field : String)
    (consumed produced :
      VcTermSort.ModelVec VcTermSort.PermissionTransferAmount)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child
        (.PermissionMaskTransition preMask postMask field consumed produced) →
        Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed
      (.PermissionMaskTransition preMask postMask field consumed produced)) := by
  have consumedTerminate : ∀ amount,
      amount ∈ (VcTermSort.ModelVec.deref consumed).val →
        Terminates (VcTermSort.Term.sort_typed amount.receiver) := by
    intro amount member
    apply smallerTerminates amount.receiver
    change amount ∈ List.take Usize.max
      (show List VcTermSort.PermissionTransferAmount from consumed) at member
    have sourceMember := List.mem_of_mem_take member
    have amountBelow := List.sizeOf_lt_of_mem sourceMember
    cases amount
    unfold TermStrictlySmaller
    simp at amountBelow ⊢
    omega
  have producedTerminate : ∀ amount,
      amount ∈ (VcTermSort.ModelVec.deref produced).val →
        Terminates (VcTermSort.Term.sort_typed amount.receiver) := by
    intro amount member
    apply smallerTerminates amount.receiver
    change amount ∈ List.take Usize.max
      (show List VcTermSort.PermissionTransferAmount from produced) at member
    have sourceMember := List.mem_of_mem_take member
    have amountBelow := List.sizeOf_lt_of_mem sourceMember
    cases amount
    unfold TermStrictlySmaller
    simp at amountBelow ⊢
    omega
  have consumedRequired := require_permission_transfer_amounts_terminates
    (VcTermSort.ModelVec.deref consumed) consumedTerminate
  have producedRequired := require_permission_transfer_amounts_terminates
    (VcTermSort.ModelVec.deref produced) producedTerminate
  rw [VcTermSort.Term.sort_typed.eq_def
    (.PermissionMaskTransition preMask postMask field consumed produced)]
  simp [lift]
  split
  · simp [Terminates,
      Str.Insts.AllocBorrowToOwnedString.to_owned]
  · simp [alloc.string.String.is_empty]
    split
    · simp [Terminates, Str.Insts.AllocBorrowToOwnedString.to_owned]
    ·
      cases consumedObserved : VcTermSort.require_permission_transfer_amounts
          (VcTermSort.ModelVec.deref consumed) with
      | div => simp [Terminates, consumedObserved] at consumedRequired
      | fail error => simp [Terminates, consumedObserved]
      | ok consumedChecked =>
          cases consumedChecked with
          | Err error =>
              simp [Terminates, consumedObserved,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          | Ok checkedUnit =>
              cases producedObserved :
                  VcTermSort.require_permission_transfer_amounts
                    (VcTermSort.ModelVec.deref produced) with
              | div => simp [Terminates, producedObserved] at producedRequired
              | fail error =>
                  simp [Terminates, consumedObserved, producedObserved,
                    core.result.Result.Insts.CoreOpsTry.branch]
              | ok producedChecked =>
                  cases producedChecked <;>
                    simp [Terminates, consumedObserved, producedObserved,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-! ## Totality of bound-occurrence validation

The four remaining `Term.sort` branches share this generated structural
validator.  Its helpers and loops are mutually partial in the extraction, so
we first close each concrete helper under exact child-totality hypotheses and
then discharge those hypotheses by well-founded induction on the source
`Term` size below.
-/

theorem validate_bound_occurrences_one_terminates_of_validate
    (term : VcTermSort.Term) (binder : String) (binderSort : VcTermSort.Sort)
    (validated : Terminates
      (VcTermSort.validate_bound_occurrences term binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.one term binder binderSort) := by
  rw [VcTermSort.validate_bound_occurrences.one.eq_def]
  exact validated

theorem validate_bound_occurrences_two_terminates_of_validate
    (left right : VcTermSort.Term)
    (binder : String) (binderSort : VcTermSort.Sort)
    (leftValidated : Terminates
      (VcTermSort.validate_bound_occurrences left binder binderSort))
    (rightValidated : Terminates
      (VcTermSort.validate_bound_occurrences right binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.two
        left right binder binderSort) := by
  rw [VcTermSort.validate_bound_occurrences.two.eq_def]
  have leftOne := validate_bound_occurrences_one_terminates_of_validate
    left binder binderSort leftValidated
  have rightOne := validate_bound_occurrences_one_terminates_of_validate
    right binder binderSort rightValidated
  cases leftObserved : VcTermSort.validate_bound_occurrences.one
      left binder binderSort with
  | div => simp [Terminates, leftObserved] at leftOne
  | fail error => simp [Terminates]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          simpa [core.result.Result.Insts.CoreOpsTry.branch] using rightOne

theorem validate_bound_occurrences_all_body_terminates
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenValidate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.validate_bound_occurrences child binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.all_loop.body
        binder binderSort iter result) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail error =>
      simp [Terminates,
        VcTermSort.validate_bound_occurrences.all_loop.body, observed]
  | ok pair =>
      obtain ⟨maybeTerm, next⟩ := pair
      cases maybeTerm with
      | none =>
          simp [Terminates,
            VcTermSort.validate_bound_occurrences.all_loop.body, observed]
      | some term =>
          have member := (slice_iterator_next_some_member
            iter next term observed).1
          cases result with
          | Err current =>
              simp [Terminates,
                VcTermSort.validate_bound_occurrences.all_loop.body,
                observed, core.result.Result.is_ok]
          | Ok checkedUnit =>
              have termValidated :=
                validate_bound_occurrences_one_terminates_of_validate
                  term binder binderSort (childrenValidate term member)
              rw [VcTermSort.validate_bound_occurrences.all_loop.body]
              rw [observed]
              cases validatedObserved :
                  VcTermSort.validate_bound_occurrences.one
                    term binder binderSort with
              | div => simp [Terminates, validatedObserved] at termValidated
              | fail error =>
                  simp [Terminates, validatedObserved,
                    core.result.Result.is_ok]
              | ok checked =>
                  simp [Terminates, validatedObserved,
                    core.result.Result.is_ok]

theorem validate_bound_occurrences_all_body_preserves_slice
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.validate_bound_occurrences.all_loop.body
      binder binderSort iter result = .ok (.cont (next, nextResult))) :
    next.slice = iter.slice := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.validate_bound_occurrences.all_loop.body,
        observed] at continued
  | div =>
      simp [VcTermSort.validate_bound_occurrences.all_loop.body,
        observed] at continued
  | ok pair =>
      obtain ⟨maybeTerm, advanced⟩ := pair
      cases maybeTerm with
      | none =>
          simp [VcTermSort.validate_bound_occurrences.all_loop.body,
            observed] at continued
      | some term =>
          have advancedSlice := (slice_iterator_next_some_member
            iter advanced term observed).2
          have advancedEq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSort.validate_bound_occurrences.all_loop.body,
                  observed, isOkObserved] at continued
            | div =>
                simp [VcTermSort.validate_bound_occurrences.all_loop.body,
                  observed, isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSort.validate_bound_occurrences.all_loop.body,
                      observed, isOkObserved] at continued
                    exact continued.1
                | true =>
                    simp [VcTermSort.validate_bound_occurrences.all_loop.body,
                      observed, isOkObserved] at continued
                    exact one_bind_cont_iterator_first
                      (VcTermSort.validate_bound_occurrences.one
                        term binder binderSort)
                      (fun checked => checked) advanced next nextResult continued
          subst next
          exact advancedSlice

theorem validate_bound_occurrences_all_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenValidate : ∀ child, child ∈ iter.slice.val →
      Terminates (VcTermSort.validate_bound_occurrences child binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.all_loop
        iter binder binderSort result) := by
  unfold VcTermSort.validate_bound_occurrences.all_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter VcTermSort.Term ×
        core.result.Result Unit VcTermSort.SortError =>
      VcTermSort.validate_bound_occurrences.all_loop.body
        binder binderSort state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    apply validate_bound_occurrences_all_body_terminates
    intro child member
    apply childrenValidate child
    simpa [sliceEq] using member
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        validate_bound_occurrences_all_body_preserves_slice
          binder binderSort state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact validate_bound_occurrences_all_body_decreases
      binder binderSort state.1 next.1 state.2 next.2 continued
  · rfl
  · simp [sliceIteratorRemaining]

theorem validate_bound_occurrences_all_terminates
    (terms : Slice VcTermSort.Term)
    (binder : String) (binderSort : VcTermSort.Sort)
    (childrenValidate : ∀ child, child ∈ terms.val →
      Terminates (VcTermSort.validate_bound_occurrences child binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.all terms binder binderSort) := by
  rw [VcTermSort.validate_bound_occurrences.all.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply validate_bound_occurrences_all_loop_terminates
  simpa using childrenValidate

theorem validate_bound_occurrences_all_transfers_body_terminates
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result : core.result.Result Unit VcTermSort.SortError)
    (receiversValidate : ∀ amount, amount ∈ iter.slice.val →
      Terminates (VcTermSort.validate_bound_occurrences
        amount.receiver binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.all_transfers_loop.body
        binder binderSort iter result) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail error =>
      simp [Terminates,
        VcTermSort.validate_bound_occurrences.all_transfers_loop.body,
        observed]
  | ok pair =>
      obtain ⟨maybeAmount, next⟩ := pair
      cases maybeAmount with
      | none =>
          simp [Terminates,
            VcTermSort.validate_bound_occurrences.all_transfers_loop.body,
            observed]
      | some amount =>
          have member := (slice_iterator_next_some_member
            iter next amount observed).1
          cases result with
          | Err current =>
              simp [Terminates,
                VcTermSort.validate_bound_occurrences.all_transfers_loop.body,
                observed, core.result.Result.is_ok]
          | Ok checkedUnit =>
              have receiverValidated :=
                validate_bound_occurrences_one_terminates_of_validate
                  amount.receiver binder binderSort
                  (receiversValidate amount member)
              rw [VcTermSort.validate_bound_occurrences.all_transfers_loop.body]
              rw [observed]
              cases validatedObserved :
                  VcTermSort.validate_bound_occurrences.one
                    amount.receiver binder binderSort with
              | div =>
                  simp [Terminates, validatedObserved] at receiverValidated
              | fail error =>
                  simp [Terminates, validatedObserved,
                    core.result.Result.is_ok]
              | ok checked =>
                  simp [Terminates, validatedObserved,
                    core.result.Result.is_ok]

theorem validate_bound_occurrences_all_transfers_body_preserves_slice
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.validate_bound_occurrences.all_transfers_loop.body
      binder binderSort iter result = .ok (.cont (next, nextResult))) :
    next.slice = iter.slice := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.validate_bound_occurrences.all_transfers_loop.body,
        observed] at continued
  | div =>
      simp [VcTermSort.validate_bound_occurrences.all_transfers_loop.body,
        observed] at continued
  | ok pair =>
      obtain ⟨maybeAmount, advanced⟩ := pair
      cases maybeAmount with
      | none =>
          simp [VcTermSort.validate_bound_occurrences.all_transfers_loop.body,
            observed] at continued
      | some amount =>
          have advancedSlice := (slice_iterator_next_some_member
            iter advanced amount observed).2
          have advancedEq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSort.validate_bound_occurrences.all_transfers_loop.body,
                  observed, isOkObserved] at continued
            | div =>
                simp [VcTermSort.validate_bound_occurrences.all_transfers_loop.body,
                  observed, isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSort.validate_bound_occurrences.all_transfers_loop.body,
                      observed, isOkObserved] at continued
                    exact continued.1
                | true =>
                    simp [VcTermSort.validate_bound_occurrences.all_transfers_loop.body,
                      observed, isOkObserved] at continued
                    exact one_bind_cont_iterator_first
                      (VcTermSort.validate_bound_occurrences.one
                        amount.receiver binder binderSort)
                      (fun checked => checked) advanced next nextResult continued
          subst next
          exact advancedSlice

theorem validate_bound_occurrences_all_transfers_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (receiversValidate : ∀ amount, amount ∈ iter.slice.val →
      Terminates (VcTermSort.validate_bound_occurrences
        amount.receiver binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.all_transfers_loop
        iter binder binderSort result) := by
  unfold VcTermSort.validate_bound_occurrences.all_transfers_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter VcTermSort.PermissionTransferAmount ×
        core.result.Result Unit VcTermSort.SortError =>
      VcTermSort.validate_bound_occurrences.all_transfers_loop.body
        binder binderSort state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    apply validate_bound_occurrences_all_transfers_body_terminates
    intro amount member
    apply receiversValidate amount
    simpa [sliceEq] using member
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        validate_bound_occurrences_all_transfers_body_preserves_slice
          binder binderSort state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact validate_bound_occurrences_all_transfers_body_decreases
      binder binderSort state.1 next.1 state.2 next.2 continued
  · rfl
  · simp [sliceIteratorRemaining]

theorem validate_bound_occurrences_all_transfers_terminates
    (amounts : Slice VcTermSort.PermissionTransferAmount)
    (binder : String) (binderSort : VcTermSort.Sort)
    (receiversValidate : ∀ amount, amount ∈ amounts.val →
      Terminates (VcTermSort.validate_bound_occurrences
        amount.receiver binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.all_transfers
        amounts binder binderSort) := by
  rw [VcTermSort.validate_bound_occurrences.all_transfers.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply validate_bound_occurrences_all_transfers_loop_terminates
  simpa using receiversValidate

theorem validate_bound_occurrences_all_entries_body_terminates
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result : core.result.Result Unit VcTermSort.SortError)
    (entriesValidate : ∀ entry, entry ∈ iter.slice.val →
      Terminates (VcTermSort.validate_bound_occurrences
        entry.1 binder binderSort) ∧
      Terminates (VcTermSort.validate_bound_occurrences
        entry.2 binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.all_entries_loop.body
        binder binderSort iter result) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail error =>
      simp [Terminates,
        VcTermSort.validate_bound_occurrences.all_entries_loop.body,
        observed]
  | ok pair =>
      obtain ⟨maybeEntry, next⟩ := pair
      cases maybeEntry with
      | none =>
          simp [Terminates,
            VcTermSort.validate_bound_occurrences.all_entries_loop.body,
            observed]
      | some entry =>
          obtain ⟨key, value⟩ := entry
          have member := (slice_iterator_next_some_member
            iter next (key, value) observed).1
          cases result with
          | Err current =>
              simp [Terminates,
                VcTermSort.validate_bound_occurrences.all_entries_loop.body,
                observed, core.result.Result.is_ok]
          | Ok checkedUnit =>
              have pairValidated :=
                validate_bound_occurrences_two_terminates_of_validate
                  key value binder binderSort
                  (entriesValidate (key, value) member).1
                  (entriesValidate (key, value) member).2
              rw [VcTermSort.validate_bound_occurrences.all_entries_loop.body]
              rw [observed]
              cases validatedObserved :
                  VcTermSort.validate_bound_occurrences.two
                    key value binder binderSort with
              | div => simp [Terminates, validatedObserved] at pairValidated
              | fail error =>
                  simp [Terminates, validatedObserved,
                    core.result.Result.is_ok]
              | ok checked =>
                  simp [Terminates, validatedObserved,
                    core.result.Result.is_ok]

theorem validate_bound_occurrences_all_entries_body_preserves_slice
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.validate_bound_occurrences.all_entries_loop.body
      binder binderSort iter result = .ok (.cont (next, nextResult))) :
    next.slice = iter.slice := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.validate_bound_occurrences.all_entries_loop.body,
        observed] at continued
  | div =>
      simp [VcTermSort.validate_bound_occurrences.all_entries_loop.body,
        observed] at continued
  | ok pair =>
      obtain ⟨maybeEntry, advanced⟩ := pair
      cases maybeEntry with
      | none =>
          simp [VcTermSort.validate_bound_occurrences.all_entries_loop.body,
            observed] at continued
      | some entry =>
          obtain ⟨key, value⟩ := entry
          have advancedSlice := (slice_iterator_next_some_member
            iter advanced (key, value) observed).2
          have advancedEq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSort.validate_bound_occurrences.all_entries_loop.body,
                  observed, isOkObserved] at continued
            | div =>
                simp [VcTermSort.validate_bound_occurrences.all_entries_loop.body,
                  observed, isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSort.validate_bound_occurrences.all_entries_loop.body,
                      observed, isOkObserved] at continued
                    exact continued.1
                | true =>
                    simp [VcTermSort.validate_bound_occurrences.all_entries_loop.body,
                      observed, isOkObserved] at continued
                    exact one_bind_cont_iterator_first
                      (VcTermSort.validate_bound_occurrences.two
                        key value binder binderSort)
                      (fun checked => checked) advanced next nextResult continued
          subst next
          exact advancedSlice

theorem validate_bound_occurrences_all_entries_loop_terminates
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (entriesValidate : ∀ entry, entry ∈ iter.slice.val →
      Terminates (VcTermSort.validate_bound_occurrences
        entry.1 binder binderSort) ∧
      Terminates (VcTermSort.validate_bound_occurrences
        entry.2 binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.all_entries_loop
        iter binder binderSort result) := by
  unfold VcTermSort.validate_bound_occurrences.all_entries_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term) ×
        core.result.Result Unit VcTermSort.SortError =>
      VcTermSort.validate_bound_occurrences.all_entries_loop.body
        binder binderSort state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    apply validate_bound_occurrences_all_entries_body_terminates
    intro entry member
    apply entriesValidate entry
    simpa [sliceEq] using member
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        validate_bound_occurrences_all_entries_body_preserves_slice
          binder binderSort state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact validate_bound_occurrences_all_entries_body_decreases
      binder binderSort state.1 next.1 state.2 next.2 continued
  · rfl
  · simp [sliceIteratorRemaining]

theorem validate_bound_occurrences_all_entries_terminates
    (entries : Slice (VcTermSort.Term × VcTermSort.Term))
    (binder : String) (binderSort : VcTermSort.Sort)
    (entriesValidate : ∀ entry, entry ∈ entries.val →
      Terminates (VcTermSort.validate_bound_occurrences
        entry.1 binder binderSort) ∧
      Terminates (VcTermSort.validate_bound_occurrences
        entry.2 binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences.all_entries
        entries binder binderSort) := by
  rw [VcTermSort.validate_bound_occurrences.all_entries.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply validate_bound_occurrences_all_entries_loop_terminates
  simpa using entriesValidate

theorem validate_bound_occurrences_terminates_of_smaller
    (term : VcTermSort.Term) (binder : String) (binderSort : VcTermSort.Sort)
    (smallerValidate : ∀ child, TermStrictlySmaller child term →
      Terminates (VcTermSort.validate_bound_occurrences
        child binder binderSort)) :
    Terminates
      (VcTermSort.validate_bound_occurrences term binder binderSort) := by
  rw [VcTermSort.validate_bound_occurrences.eq_def term]
  cases term with
  | Bool value => simp [Terminates]
  | Int value => simp [Terminates]
  | String value => simp [Terminates]
  | Bytes value => simp [Terminates]
  | Range value => simp [Terminates]
  | Unit => simp [Terminates]
  | NullReference => simp [Terminates]
  | NominalReference className objectName => simp [Terminates]
  | ClassLiteral className => simp [Terminates]
  | PermissionMaskValid mask field => simp [Terminates]
  | Variable variableName sort =>
      simp only
      rw [string_eq_refines]
      simp only [bind_tc_ok]
      split
      · apply result_bind_terminates
        · exact sort_partial_eq_terminates sort binderSort
        · intro equal
          cases equal with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [string_clone_refines]
              simp only [bind_tc_ok]
              exact two_sort_clones_then_result_error_terminates sort binderSort
                (VcTermSort.SortError.BinderSortMismatch binder)
          | true => simp [Terminates]
      · simp [Terminates]
  | IntEnumValue descriptor value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | IntEnumProjection value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | IntEnumDomain value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | RuntimeClass value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | FieldRead mask value field sort =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller] <;> omega
  | PermissionAtLeast mask value field numerator denominator =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller] <;> omega
  | PermissionAtMost mask value field numerator denominator =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller] <;> omega
  | PermissionPositive mask value field =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller] <;> omega
  | Not value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | FloorDivideByPositive value divisor =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller] <;> omega
  | Negate value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | StringLength value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | BytesLength value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | TupleGet value index =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller] <;> omega
  | ListLength value | VariadicTupleLength value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | ListSlice value lower upper step =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller] <;> omega
  | VariadicTupleSlice value lower upper step =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller] <;> omega
  | ListSum value | ListSorted value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller] <;> omega
  | SetLength value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | DictLength value =>
      apply validate_bound_occurrences_one_terminates_of_validate
      apply smallerValidate value
      simp [TermStrictlySmaller]
  | IntEnumIdentity left right | ClassSubtype left right
  | Implies left right | Equal left right | Less left right
  | LessEqual left right | Greater left right | GreaterEqual left right
  | Add left right | Subtract left right | Multiply left right
  | BytesGet left right | ListGet left right | ListContains left right
  | VariadicTupleGet left right
  | ListConcat left right
  | SetContains left right | DictContains left right | DictGet left right =>
      apply validate_bound_occurrences_two_terminates_of_validate
      · apply smallerValidate left
        simp [TermStrictlySmaller] <;> omega
      · apply smallerValidate right
        simp [TermStrictlySmaller] <;> omega
  | PredicateInstance predicate values | And values | Or values
  | StringConcat values | BytesConcat values | Tuple values
  | DictKeys _ values =>
      apply validate_bound_occurrences_all_terminates
      intro child member
      apply smallerValidate child
      change child ∈ List.take Usize.max
        (show List VcTermSort.Term from values) at member
      have sourceMember := List.mem_of_mem_take member
      unfold TermStrictlySmaller
      have childBelow := List.sizeOf_lt_of_mem sourceMember
      simp at childBelow ⊢
      omega
  | List _ values | VariadicTuple _ values =>
      apply validate_bound_occurrences_all_terminates
      intro child member
      apply smallerValidate child
      change child ∈ List.take Usize.max
        (show List VcTermSort.Term from values) at member
      have sourceMember := List.mem_of_mem_take member
      unfold TermStrictlySmaller
      have childBelow := List.sizeOf_lt_of_mem sourceMember
      simp at childBelow ⊢
      omega
  | IfThenElse condition thenValue elseValue =>
      simp only
      have conditionValidated :=
        validate_bound_occurrences_one_terminates_of_validate
          condition binder binderSort (smallerValidate condition (by
            simp [TermStrictlySmaller] <;> omega))
      have thenValidated :=
        validate_bound_occurrences_one_terminates_of_validate
          thenValue binder binderSort (smallerValidate thenValue (by
            simp [TermStrictlySmaller] <;> omega))
      have elseValidated :=
        validate_bound_occurrences_one_terminates_of_validate
          elseValue binder binderSort (smallerValidate elseValue (by
            simp [TermStrictlySmaller] <;> omega))
      cases conditionObserved : VcTermSort.validate_bound_occurrences.one
          condition binder binderSort with
      | div => simp [Terminates, conditionObserved] at conditionValidated
      | fail error => simp [Terminates]
      | ok checked =>
          cases checked with
          | Err error =>
              simp [Terminates,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          | Ok checkedUnit =>
              cases thenObserved : VcTermSort.validate_bound_occurrences.one
                  thenValue binder binderSort with
              | div => simp [Terminates, thenObserved] at thenValidated
              | fail error =>
                  simp [Terminates,
                    core.result.Result.Insts.CoreOpsTry.branch]
              | ok checkedThen =>
                  cases checkedThen with
                  | Err error =>
                      simp [Terminates,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                  | Ok checkedUnit =>
                      simpa [core.result.Result.Insts.CoreOpsTry.branch] using
                        elseValidated
  | PermissionMaskTransition preMask postMask field consumed produced =>
      simp only
      have consumedValidated : Terminates
          (VcTermSort.validate_bound_occurrences.all_transfers
            (VcTermSort.ModelVec.deref consumed) binder binderSort) := by
        apply validate_bound_occurrences_all_transfers_terminates
        intro amount member
        apply smallerValidate amount.receiver
        change amount ∈ List.take Usize.max
          (show List VcTermSort.PermissionTransferAmount from consumed) at member
        have sourceMember := List.mem_of_mem_take member
        exact permission_receiver_strictly_smaller amount consumed
          (.PermissionMaskTransition preMask postMask field consumed produced)
          sourceMember (by simp <;> omega)
      have producedValidated : Terminates
          (VcTermSort.validate_bound_occurrences.all_transfers
            (VcTermSort.ModelVec.deref produced) binder binderSort) := by
        apply validate_bound_occurrences_all_transfers_terminates
        intro amount member
        apply smallerValidate amount.receiver
        change amount ∈ List.take Usize.max
          (show List VcTermSort.PermissionTransferAmount from produced) at member
        have sourceMember := List.mem_of_mem_take member
        exact permission_receiver_strictly_smaller amount produced
          (.PermissionMaskTransition preMask postMask field consumed produced)
          sourceMember (by simp <;> omega)
      cases consumedObserved : VcTermSort.validate_bound_occurrences.all_transfers
          (VcTermSort.ModelVec.deref consumed) binder binderSort with
      | div => simp [Terminates, consumedObserved] at consumedValidated
      | fail error => simp [Terminates]
      | ok checked =>
          cases checked with
          | Err error =>
              simp [Terminates,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          | Ok checkedUnit =>
              simpa [core.result.Result.Insts.CoreOpsTry.branch] using
                producedValidated
  | FiniteDict keySort valueSort entries =>
      apply validate_bound_occurrences_all_entries_terminates
      intro entry member
      change entry ∈ List.take Usize.max
        (show List (VcTermSort.Term × VcTermSort.Term) from entries) at member
      have sourceMember := List.mem_of_mem_take member
      constructor
      · apply smallerValidate entry.1
        exact finite_dict_key_strictly_smaller entry entries
          (.FiniteDict keySort valueSort entries) sourceMember (by simp)
      · apply smallerValidate entry.2
        exact finite_dict_value_strictly_smaller entry entries
          (.FiniteDict keySort valueSort entries) sourceMember (by simp)
  | ListComprehension resultName source nested nestedSort mapped filter
  | SetComprehension resultName source nested nestedSort mapped filter =>
      simp only
      rw [string_eq_refines]
      simp only [bind_tc_ok]
      split
      · simp [Terminates, string_clone_refines, core.fmt.rt.Argument.new_debug,
          core.fmt.Arguments.new, alloc.fmt.format, core.hint.must_use]
      ·
        have sourceValidated :=
          validate_bound_occurrences_one_terminates_of_validate
            source binder binderSort (smallerValidate source (by
              simp [TermStrictlySmaller] <;> omega))
        have mappedValidated :=
          validate_bound_occurrences_one_terminates_of_validate
            mapped binder binderSort (smallerValidate mapped (by
              simp [TermStrictlySmaller] <;> omega))
        have filterValidated : ∀ child, filter = some child →
            Terminates (VcTermSort.validate_bound_occurrences.one
              child binder binderSort) := by
          intro child present
          apply validate_bound_occurrences_one_terminates_of_validate
          apply smallerValidate child
          subst filter
          simp [TermStrictlySmaller] <;> omega
        cases sourceObserved : VcTermSort.validate_bound_occurrences.one
            source binder binderSort with
        | div => simp [Terminates, sourceObserved] at sourceValidated
        | fail error => simp [Terminates]
        | ok sourceChecked =>
            cases sourceChecked with
            | Err error =>
                simp [Terminates,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            | Ok checkedUnit =>
                cases mappedObserved : VcTermSort.validate_bound_occurrences.one
                    mapped binder binderSort with
                | div => simp [Terminates, mappedObserved] at mappedValidated
                | fail error =>
                    simp [Terminates, core.result.Result.Insts.CoreOpsTry.branch]
                | ok mappedChecked =>
                    cases mappedChecked with
                    | Err error =>
                        simp [Terminates,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                    | Ok checkedUnit =>
                        cases filter with
                        | none => simp [Terminates,
                            core.result.Result.Insts.CoreOpsTry.branch]
                        | some filterTerm =>
                            have currentFilter := filterValidated filterTerm rfl
                            exact result_try_then_ok_unit_terminates
                              (VcTermSort.validate_bound_occurrences.one
                                filterTerm binder binderSort) currentFilter
  | DictComprehension resultName source nested nestedSort keySort key value filter =>
      simp only
      rw [string_eq_refines]
      simp only [bind_tc_ok]
      split
      · simp [Terminates, string_clone_refines, core.fmt.rt.Argument.new_debug,
          core.fmt.Arguments.new, alloc.fmt.format, core.hint.must_use]
      ·
        have sourceValidated :=
          validate_bound_occurrences_one_terminates_of_validate
            source binder binderSort (smallerValidate source (by
              simp [TermStrictlySmaller] <;> omega))
        have pairValidated :=
          validate_bound_occurrences_two_terminates_of_validate
            key value binder binderSort
            (smallerValidate key (by simp [TermStrictlySmaller] <;> omega))
            (smallerValidate value (by simp [TermStrictlySmaller] <;> omega))
        have filterValidated : ∀ child, filter = some child →
            Terminates (VcTermSort.validate_bound_occurrences.one
              child binder binderSort) := by
          intro child present
          apply validate_bound_occurrences_one_terminates_of_validate
          apply smallerValidate child
          subst filter
          simp [TermStrictlySmaller] <;> omega
        cases sourceObserved : VcTermSort.validate_bound_occurrences.one
            source binder binderSort with
        | div => simp [Terminates, sourceObserved] at sourceValidated
        | fail error => simp [Terminates]
        | ok sourceChecked =>
            cases sourceChecked with
            | Err error =>
                simp [Terminates,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            | Ok checkedUnit =>
                cases pairObserved : VcTermSort.validate_bound_occurrences.two
                    key value binder binderSort with
                | div => simp [Terminates, pairObserved] at pairValidated
                | fail error =>
                    simp [Terminates, core.result.Result.Insts.CoreOpsTry.branch]
                | ok pairChecked =>
                    cases pairChecked with
                    | Err error =>
                        simp [Terminates,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                    | Ok checkedUnit =>
                        cases filter with
                        | none => simp [Terminates,
                            core.result.Result.Insts.CoreOpsTry.branch]
                        | some filterTerm =>
                            have currentFilter := filterValidated filterTerm rfl
                            exact result_try_then_ok_unit_terminates
                              (VcTermSort.validate_bound_occurrences.one
                                filterTerm binder binderSort) currentFilter
  | ForAll nested nestedSort body =>
      simp only
      rw [string_eq_refines]
      simp only [bind_tc_ok]
      split
      · simp [Terminates, string_clone_refines, core.fmt.rt.Argument.new_debug,
          core.fmt.Arguments.new, alloc.fmt.format, core.hint.must_use]
      · apply validate_bound_occurrences_one_terminates_of_validate
        apply smallerValidate body
        simp [TermStrictlySmaller]

theorem validate_bound_occurrences_terminates
    (term : VcTermSort.Term) (binder : String) (binderSort : VcTermSort.Sort) :
    Terminates
      (VcTermSort.validate_bound_occurrences term binder binderSort) := by
  apply term_strictly_smaller_well_founded.induction term
  intro current smallerValidate
  exact validate_bound_occurrences_terminates_of_smaller
    current binder binderSort smallerValidate

theorem require_bound_term_sort_terminates
    (binder : String) (binderSort : VcTermSort.Sort)
    (term : VcTermSort.Term) (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (termSortTerminates : Terminates (VcTermSort.Term.sort_typed term)) :
    Terminates
      (VcTermSort.require_bound_term_sort
        binder binderSort term expected context) := by
  rw [VcTermSort.require_bound_term_sort.eq_def]
  have validated := validate_bound_occurrences_terminates
    term binder binderSort
  cases validateObserved : VcTermSort.validate_bound_occurrences
      term binder binderSort with
  | div => simp [Terminates, validateObserved] at validated
  | fail error => simp [Terminates]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
          apply result_bind_terminates
          · exact sort_clone_terminates expected
          · intro cloned
            exact require_sort_terminates_of_term_sort_terminates
              term cloned context termSortTerminates

theorem require_comprehension_body_terminates
    (binder : String) (binderSort : VcTermSort.Sort)
    (mapped : VcTermSort.Term) (mappedSort : VcTermSort.Sort)
    (filter : Option VcTermSort.Term)
    (mappedSortTerminates : Terminates (VcTermSort.Term.sort_typed mapped))
    (filterSortTerminates : ∀ child, filter = some child →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates
      (VcTermSort.require_comprehension_body
        binder binderSort mapped mappedSort filter) := by
  rw [VcTermSort.require_comprehension_body.eq_def]
  simp [alloc.string.String.is_empty]
  split
  · simp [Terminates, Str.Insts.AllocBorrowToOwnedString.to_owned]
  ·
    have mappedRequired := require_bound_term_sort_terminates
      binder binderSort mapped mappedSort VcTermSort.SortContext.ComprehensionMapper
      mappedSortTerminates
    cases mappedObserved : VcTermSort.require_bound_term_sort
        binder binderSort mapped mappedSort VcTermSort.SortContext.ComprehensionMapper with
    | div => simp [Terminates, mappedObserved] at mappedRequired
    | fail error => simp [Terminates]
    | ok checked =>
        cases checked with
        | Err error =>
            simp [Terminates,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        | Ok checkedUnit =>
            cases filter with
            | none =>
                simp [Terminates, core.result.Result.Insts.CoreOpsTry.branch]
            | some filterTerm =>
                have filterRequired := require_bound_term_sort_terminates
                  binder binderSort filterTerm VcTermSort.Sort.Bool
                  VcTermSort.SortContext.ComprehensionFilter
                  (filterSortTerminates filterTerm rfl)
                simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
                exact result_try_then_ok_unit_terminates
                  (VcTermSort.require_bound_term_sort binder binderSort
                    filterTerm VcTermSort.Sort.Bool
                    VcTermSort.SortContext.ComprehensionFilter) filterRequired

theorem all_nominal_references_body_terminates
    (iter : core.slice.iter.Iter VcTermSort.Term) (result : Bool) :
    Terminates (VcTermSort.all_nominal_references_loop.body iter result) := by
  have nextTerminates := slice_iterator_next_terminates iter
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | div => simp [Terminates, observed] at nextTerminates
  | fail error =>
      simp [Terminates, VcTermSort.all_nominal_references_loop.body, observed]
  | ok pair =>
      obtain ⟨maybeTerm, next⟩ := pair
      cases maybeTerm with
      | none =>
          simp [Terminates, VcTermSort.all_nominal_references_loop.body,
            observed]
      | some term =>
          cases result with
          | false =>
              simp [Terminates, VcTermSort.all_nominal_references_loop.body,
                observed]
          | true =>
              cases term <;>
                simp [Terminates,
                  VcTermSort.all_nominal_references_loop.body, observed]

theorem all_nominal_references_loop_terminates
    (iter : core.slice.iter.Iter VcTermSort.Term) (result : Bool) :
    Terminates (VcTermSort.all_nominal_references_loop iter result) := by
  unfold VcTermSort.all_nominal_references_loop
  apply run_loop_fuel_terminates_of_invariant
    (fun state : core.slice.iter.Iter VcTermSort.Term × Bool =>
      VcTermSort.all_nominal_references_loop.body state.1 state.2)
    (fun _ => True) (fun state => sliceIteratorRemaining state.1)
  · intro state invariant
    exact all_nominal_references_body_terminates state.1 state.2
  · simp
  · intro state next continued
    exact all_nominal_references_body_decreases
      state.1 next.1 state.2 next.2 continued
  · trivial
  · simp [sliceIteratorRemaining]

theorem all_nominal_references_terminates
    (values : Slice VcTermSort.Term) :
    Terminates (VcTermSort.all_nominal_references values) := by
  unfold VcTermSort.all_nominal_references
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  exact all_nominal_references_loop_terminates _ true

theorem is_exact_nominal_reference_list_terminates
    (source : VcTermSort.Term) :
    Terminates (VcTermSort.is_exact_nominal_reference_list source) := by
  cases source <;> simp [VcTermSort.is_exact_nominal_reference_list, Terminates]
  case List elementSort values =>
    cases elementSort <;> simp [Terminates]
    exact all_nominal_references_terminates (VcTermSort.ModelVec.deref values)

theorem is_reference_binder_projection_terminates
    (mapped : VcTermSort.Term) (binder : String) :
    Terminates (VcTermSort.is_reference_binder_projection mapped binder) := by
  cases mapped <;>
    simp [VcTermSort.is_reference_binder_projection, Terminates,
      string_eq_refines]
  case Variable variableName sort =>
    cases sort <;> simp [Terminates, string_eq_refines]

theorem term_sort_for_all_terminates_of_smaller
    (binder : String) (binderSort : VcTermSort.Sort)
    (body : VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child (.ForAll binder binderSort body) →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates
      (VcTermSort.Term.sort_typed (.ForAll binder binderSort body)) := by
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp [alloc.string.String.is_empty]
  split
  · simp [Terminates, Str.Insts.AllocBorrowToOwnedString.to_owned]
  ·
    have bodyTerminates := smallerTerminates body (by
      simp [TermStrictlySmaller] <;> omega)
    have required := require_bound_term_sort_terminates
      binder binderSort body VcTermSort.Sort.Bool
      VcTermSort.SortContext.QuantifierBody bodyTerminates
    exact require_sort_then_ok_terminates
      (VcTermSort.require_bound_term_sort binder binderSort body
        VcTermSort.Sort.Bool VcTermSort.SortContext.QuantifierBody)
      required VcTermSort.Sort.Bool

theorem term_sort_list_comprehension_terminates_of_smaller
    (resultName : String) (source : VcTermSort.Term)
    (binder : String) (elementSort : VcTermSort.Sort)
    (mapped : VcTermSort.Term) (filter : Option VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child
        (.ListComprehension resultName source binder elementSort mapped filter) →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed
      (.ListComprehension resultName source binder elementSort mapped filter)) := by
  have sourceTerminates := smallerTerminates source (by
    simp [TermStrictlySmaller] <;> omega)
  have mappedTerminates := smallerTerminates mapped (by
    simp [TermStrictlySmaller] <;> omega)
  have filterTerminates : ∀ child, filter = some child →
      Terminates (VcTermSort.Term.sort_typed child) := by
    intro child present
    apply smallerTerminates child
    subst filter
    simp [TermStrictlySmaller] <;> omega
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp only
  cases sourceObserved : VcTermSort.Term.sort_typed source with
  | div => simp [Terminates, sourceObserved] at sourceTerminates
  | fail error => simp [Terminates]
  | ok result =>
      cases result with
      | Err error =>
          simp [Terminates,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok sourceSort =>
          cases sourceSort <;>
            simp [Terminates, core.result.Result.Insts.CoreOpsTry.branch,
              Str.Insts.AllocBorrowToOwnedString.to_owned]
          case List sourceElement =>
            have required := require_comprehension_body_terminates
              binder sourceElement mapped elementSort filter
              mappedTerminates filterTerminates
            cases requiredObserved : VcTermSort.require_comprehension_body
                binder sourceElement mapped elementSort filter with
            | div => simp [Terminates, requiredObserved] at required
            | fail error =>
                simp [Terminates,
                  core.result.Result.Insts.CoreOpsTry.branch]
            | ok checked =>
                cases checked with
                | Err error =>
                    simp [Terminates,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                | Ok checkedUnit =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,
                      bind_tc_ok]
                    exact result_bind_terminates
                      (VcTermSort.Sort.Insts.CoreCloneClone.clone elementSort)
                      (fun cloned => ok (core.result.Result.Ok
                        (VcTermSort.Sort.List cloned)))
                      (sort_clone_terminates elementSort)
                      (by intro cloned; simp [Terminates])

theorem require_comprehension_then_set_terminates
    (binder : String) (sourceElement : VcTermSort.Sort)
    (mapped : VcTermSort.Term) (elementSort : VcTermSort.Sort)
    (filter : Option VcTermSort.Term)
    (requiredTerminates : Terminates
      (VcTermSort.require_comprehension_body
        binder sourceElement mapped elementSort filter)) :
    Terminates (do
      let r ← VcTermSort.require_comprehension_body
        binder sourceElement mapped elementSort filter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
          let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone elementSort
          ok (core.result.Result.Ok (VcTermSort.Sort.Set cloned))
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual) := by
  cases observed : VcTermSort.require_comprehension_body
      binder sourceElement mapped elementSort filter with
  | div => simp [Terminates, observed] at requiredTerminates
  | fail error => simp [Terminates]
  | ok checked =>
      cases checked with
      | Err error =>
          simp [Terminates,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
          exact result_bind_terminates
            (VcTermSort.Sort.Insts.CoreCloneClone.clone elementSort)
            (fun cloned => ok (core.result.Result.Ok
              (VcTermSort.Sort.Set cloned)))
            (sort_clone_terminates elementSort)
            (by intro cloned; simp [Terminates])

theorem set_comprehension_finish_terminates
    (binder : String) (sourceElement : VcTermSort.Sort)
    (mapped : VcTermSort.Term) (elementSort : VcTermSort.Sort)
    (filter : Option VcTermSort.Term) (exactReferenceIdentity : Bool)
    (mappedSortTerminates : Terminates (VcTermSort.Term.sort_typed mapped))
    (filterSortTerminates : ∀ child, filter = some child →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (do
      let valid ← VcTermSort.is_finite_dict_key_sort elementSort
      if valid then
        let r ← VcTermSort.require_comprehension_body
          binder sourceElement mapped elementSort filter
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
            let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone elementSort
            ok (core.result.Result.Ok (VcTermSort.Sort.Set cloned))
        | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual
      else if exactReferenceIdentity then
        let r ← VcTermSort.require_comprehension_body
          binder sourceElement mapped elementSort filter
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
            let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone elementSort
            ok (core.result.Result.Ok (VcTermSort.Sort.Set cloned))
        | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual
      else
        let cloned ← VcTermSort.Sort.Insts.CoreCloneClone.clone elementSort
        ok (core.result.Result.Err
          (VcTermSort.SortError.SetComprehensionElementSortUnsupported cloned))) := by
  apply result_bind_terminates
  · exact is_finite_dict_key_sort_terminates elementSort
  · intro valid
    cases valid with
    | false =>
        cases exactReferenceIdentity with
        | false =>
            apply result_bind_terminates
            · exact sort_clone_terminates elementSort
            · intro cloned
              simp [Terminates]
        | true =>
            exact require_comprehension_then_set_terminates
              binder sourceElement mapped elementSort filter
              (require_comprehension_body_terminates
                binder sourceElement mapped elementSort filter
                mappedSortTerminates filterSortTerminates)
    | true =>
        exact require_comprehension_then_set_terminates
          binder sourceElement mapped elementSort filter
          (require_comprehension_body_terminates
            binder sourceElement mapped elementSort filter
            mappedSortTerminates filterSortTerminates)

theorem set_comprehension_reference_prelude_terminates
    (source mapped : VcTermSort.Term) (binder : String)
    (elementSort : VcTermSort.Sort) (filter : Option VcTermSort.Term) :
    Terminates (do
      let exactList ← VcTermSort.is_exact_nominal_reference_list source
      let exactProjection ←
        if exactList then
          VcTermSort.is_reference_binder_projection mapped binder
        else ok false
      ok (binder, elementSort, mapped, filter, exactProjection)) := by
  apply result_bind_terminates
    (input := VcTermSort.is_exact_nominal_reference_list source)
  · exact is_exact_nominal_reference_list_terminates source
  · intro exactList
    cases exactList with
    | false => simp [Terminates]
    | true =>
        apply result_bind_terminates
          (input := VcTermSort.is_reference_binder_projection mapped binder)
        · exact is_reference_binder_projection_terminates mapped binder
        · intro exactProjection
          simp [Terminates]

theorem set_comprehension_reference_prelude_ok_shape
    (source mapped : VcTermSort.Term) (binder : String)
    (elementSort : VcTermSort.Sort) (filter : Option VcTermSort.Term)
    (binder1 : String) (elementSort1 : VcTermSort.Sort)
    (mapped1 : VcTermSort.Term) (filter1 : Option VcTermSort.Term)
    (exactProjection : Bool)
    (observed : (do
      let exactList ← VcTermSort.is_exact_nominal_reference_list source
      let exactProjection ←
        if exactList then
          VcTermSort.is_reference_binder_projection mapped binder
        else ok false
      ok (binder, elementSort, mapped, filter, exactProjection)) =
      .ok (binder1, elementSort1, mapped1, filter1, exactProjection)) :
    binder1 = binder ∧ elementSort1 = elementSort ∧ mapped1 = mapped ∧
      filter1 = filter := by
  cases exactObserved : VcTermSort.is_exact_nominal_reference_list source with
  | div => simp [exactObserved] at observed
  | fail error => simp [exactObserved] at observed
  | ok exactList =>
      cases exactList with
      | false => simp [exactObserved] at observed; simp_all
      | true =>
          cases projectionObserved :
              VcTermSort.is_reference_binder_projection mapped binder with
          | div => simp [exactObserved, projectionObserved] at observed
          | fail error => simp [exactObserved, projectionObserved] at observed
          | ok projection =>
              simp [exactObserved, projectionObserved] at observed
              simp_all

theorem term_sort_set_comprehension_terminates_of_smaller
    (resultName : String) (source : VcTermSort.Term)
    (binder : String) (elementSort : VcTermSort.Sort)
    (mapped : VcTermSort.Term) (filter : Option VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child
        (.SetComprehension resultName source binder elementSort mapped filter) →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed
      (.SetComprehension resultName source binder elementSort mapped filter)) := by
  have sourceTerminates := smallerTerminates source (by
    simp [TermStrictlySmaller] <;> omega)
  have mappedTerminates := smallerTerminates mapped (by
    simp [TermStrictlySmaller] <;> omega)
  have filterTerminates : ∀ child, filter = some child →
      Terminates (VcTermSort.Term.sort_typed child) := by
    intro child present
    apply smallerTerminates child
    subst filter
    simp [TermStrictlySmaller] <;> omega
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp only
  cases sourceObserved : VcTermSort.Term.sort_typed source with
  | div => simp [Terminates, sourceObserved] at sourceTerminates
  | fail error => simp [Terminates]
  | ok result =>
      cases result with
      | Err error =>
          simp [Terminates,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok sourceSort =>
          cases sourceSort <;>
            simp [Terminates, core.result.Result.Insts.CoreOpsTry.branch,
              Str.Insts.AllocBorrowToOwnedString.to_owned]
          case List sourceElement =>
            apply result_bind_terminates
            · exact sort_partial_eq_terminates
                elementSort VcTermSort.Sort.Reference
            · intro isReference
              cases isReference with
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte, bind_tc_ok]
                  exact set_comprehension_finish_terminates binder sourceElement
                    mapped elementSort filter false
                    mappedTerminates filterTerminates
              | true =>
                  simp only [Bool.true_eq, ↓reduceIte]
                  apply result_bind_terminates_of_observed_output
                    (input := do
                      let exactList ←
                        VcTermSort.is_exact_nominal_reference_list source
                      let exactProjection ←
                        if exactList then
                          VcTermSort.is_reference_binder_projection mapped binder
                        else ok false
                      ok (binder, elementSort, mapped, filter, exactProjection))
                  · exact set_comprehension_reference_prelude_terminates
                      source mapped binder elementSort filter
                  · intro inputs preludeObserved
                    obtain ⟨binder1, elementSort1, mapped1, filter1,
                      exactProjection⟩ := inputs
                    have shape : binder1 = binder ∧
                        elementSort1 = elementSort ∧ mapped1 = mapped ∧
                        filter1 = filter := by
                      cases exactObserved :
                          VcTermSort.is_exact_nominal_reference_list source with
                      | div => simp [exactObserved] at preludeObserved
                      | fail error => simp [exactObserved] at preludeObserved
                      | ok exactList =>
                          cases exactList with
                          | false =>
                              simp [exactObserved] at preludeObserved
                              simp_all
                          | true =>
                              cases projectionObserved :
                                  VcTermSort.is_reference_binder_projection
                                    mapped binder with
                              | div =>
                                  simp [exactObserved, projectionObserved] at preludeObserved
                              | fail error =>
                                  simp [exactObserved, projectionObserved] at preludeObserved
                              | ok projection =>
                                  simp [exactObserved, projectionObserved] at preludeObserved
                                  simp_all
                    rcases shape with ⟨binderEq, elementSortEq, mappedEq,
                      filterEq⟩
                    subst binder1
                    subst elementSort1
                    subst mapped1
                    subst filter1
                    exact set_comprehension_finish_terminates
                      binder sourceElement mapped elementSort filter
                      exactProjection mappedTerminates filterTerminates

theorem require_dict_comprehension_chain_terminates
    (binder : String) (sourceElement : VcTermSort.Sort)
    (key value : VcTermSort.Term)
    (keySort valueSort : VcTermSort.Sort)
    (filter : Option VcTermSort.Term)
    (keyRequiredTerminates : Terminates
      (VcTermSort.require_comprehension_body
        binder sourceElement key keySort filter))
    (valueRequiredTerminates : Terminates
      (VcTermSort.require_bound_term_sort binder sourceElement value valueSort
        VcTermSort.SortContext.DictionaryValue)) :
    Terminates (do
      let r ← VcTermSort.require_comprehension_body
        binder sourceElement key keySort filter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
          let r1 ← VcTermSort.require_bound_term_sort
            binder sourceElement value valueSort VcTermSort.SortContext.DictionaryValue
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
              let clonedKey ←
                VcTermSort.Sort.Insts.CoreCloneClone.clone keySort
              let clonedValue ←
                VcTermSort.Sort.Insts.CoreCloneClone.clone valueSort
              ok (core.result.Result.Ok
                (VcTermSort.Sort.Dict clonedKey clonedValue))
          | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            VcTermSort.Sort (core.convert.FromSame VcTermSort.SortError) residual) := by
  cases keyObserved : VcTermSort.require_comprehension_body
      binder sourceElement key keySort filter with
  | div => simp [Terminates, keyObserved] at keyRequiredTerminates
  | fail error => simp [Terminates]
  | ok keyChecked =>
      cases keyChecked with
      | Err error =>
          simp [Terminates,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok checkedUnit =>
          cases valueObserved : VcTermSort.require_bound_term_sort
              binder sourceElement value valueSort
                VcTermSort.SortContext.DictionaryValue with
          | div =>
              simp [Terminates, valueObserved] at valueRequiredTerminates
          | fail error =>
              simp [Terminates, core.result.Result.Insts.CoreOpsTry.branch]
          | ok valueChecked =>
              cases valueChecked with
              | Err error =>
                  simp [Terminates,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
              | Ok checkedUnit =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    bind_tc_ok]
                  apply result_bind_terminates
                  · exact sort_clone_terminates keySort
                  · intro clonedKey
                    apply result_bind_terminates
                    · exact sort_clone_terminates valueSort
                    · intro clonedValue
                      simp [Terminates]

theorem term_sort_dict_comprehension_terminates_of_smaller
    (resultName : String) (source : VcTermSort.Term)
    (binder : String) (keySort valueSort : VcTermSort.Sort)
    (key value : VcTermSort.Term) (filter : Option VcTermSort.Term)
    (smallerTerminates : ∀ child,
      TermStrictlySmaller child
        (.DictComprehension resultName source binder keySort valueSort
          key value filter) →
      Terminates (VcTermSort.Term.sort_typed child)) :
    Terminates (VcTermSort.Term.sort_typed
      (.DictComprehension resultName source binder keySort valueSort
        key value filter)) := by
  have sourceTerminates := smallerTerminates source (by
    simp [TermStrictlySmaller] <;> omega)
  have keyTerminates := smallerTerminates key (by
    simp [TermStrictlySmaller] <;> omega)
  have valueTerminates := smallerTerminates value (by
    simp [TermStrictlySmaller] <;> omega)
  have filterTerminates : ∀ child, filter = some child →
      Terminates (VcTermSort.Term.sort_typed child) := by
    intro child present
    apply smallerTerminates child
    subst filter
    simp [TermStrictlySmaller] <;> omega
  rw [VcTermSort.Term.sort_typed.eq_def]
  simp only
  cases sourceObserved : VcTermSort.Term.sort_typed source with
  | div => simp [Terminates, sourceObserved] at sourceTerminates
  | fail error => simp [Terminates]
  | ok result =>
      cases result with
      | Err error =>
          simp [Terminates,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok sourceSort =>
          cases sourceSort <;>
            simp [Terminates, core.result.Result.Insts.CoreOpsTry.branch,
              Str.Insts.AllocBorrowToOwnedString.to_owned]
          case List sourceElement =>
            apply result_bind_terminates
            · exact is_finite_dict_key_sort_terminates keySort
            · intro keyValid
              cases keyValid with
              | false =>
                  apply result_bind_terminates
                  · exact sort_clone_terminates keySort
                  · intro clonedKey
                    apply result_bind_terminates
                    · exact sort_clone_terminates valueSort
                    · intro clonedValue
                      simp [Terminates]
              | true =>
                  apply result_bind_terminates
                  · exact is_finite_dict_value_sort_terminates valueSort
                  · intro valueValid
                    cases valueValid with
                    | false =>
                        apply result_bind_terminates
                        · exact sort_clone_terminates keySort
                        · intro clonedKey
                          apply result_bind_terminates
                          · exact sort_clone_terminates valueSort
                          · intro clonedValue
                            simp [Terminates]
                    | true =>
                        exact require_dict_comprehension_chain_terminates
                          binder sourceElement key value keySort valueSort filter
                          (require_comprehension_body_terminates
                            binder sourceElement key keySort filter
                            keyTerminates filterTerminates)
                          (require_bound_term_sort_terminates binder sourceElement
                            value valueSort VcTermSort.SortContext.DictionaryValue
                            valueTerminates)

/-- Every finite source `Term` reaches a concrete success, diagnostic error,
or modeled external failure in the exact generated `Term::sort` body; the
`partial_fixpoint` bottom alternative is unreachable on every input. -/
theorem term_sort_terminates (term : VcTermSort.Term) :
    Terminates (VcTermSort.Term.sort_typed term) := by
  apply term_strictly_smaller_well_founded.induction term
  intro current smallerTerminates
  cases current with
  | Bool value => exact term_sort_bool_terminates value
  | Int value => exact term_sort_int_terminates value
  | IntEnumValue descriptor value =>
      exact term_sort_int_enum_value_terminates_of_smaller
        descriptor value smallerTerminates
  | IntEnumProjection value =>
      exact term_sort_int_enum_projection_terminates_of_smaller
        value smallerTerminates
  | IntEnumDomain value =>
      exact term_sort_int_enum_domain_terminates_of_smaller
        value smallerTerminates
  | IntEnumIdentity left right =>
      exact term_sort_int_enum_identity_terminates_of_smaller
        left right smallerTerminates
  | String value => exact term_sort_string_terminates value
  | Bytes value => exact term_sort_bytes_terminates value
  | Range value => exact term_sort_range_terminates value
  | Unit => exact term_sort_unit_terminates
  | NullReference => exact term_sort_null_reference_terminates
  | NominalReference className objectName =>
      exact term_sort_nominal_reference_terminates className objectName
  | ClassLiteral className =>
      exact term_sort_class_literal_terminates className
  | RuntimeClass value =>
      exact term_sort_runtime_class_terminates_of_smaller
        value smallerTerminates
  | PredicateInstance predicate arguments =>
      exact term_sort_predicate_instance_terminates_of_smaller
        predicate arguments smallerTerminates
  | ClassSubtype left right =>
      exact term_sort_class_subtype_terminates_of_smaller
        left right smallerTerminates
  | Variable variableName sort =>
      exact term_sort_variable_terminates variableName sort
  | FieldRead mask receiver field sort =>
      exact term_sort_field_read_terminates_of_smaller
        mask receiver field sort smallerTerminates
  | PermissionAtLeast mask receiver field numerator denominator =>
      exact term_sort_permission_at_least_terminates_of_smaller
        mask receiver field numerator denominator smallerTerminates
  | PermissionAtMost mask receiver field numerator denominator =>
      exact term_sort_permission_at_most_terminates_of_smaller
        mask receiver field numerator denominator smallerTerminates
  | PermissionPositive mask receiver field =>
      exact term_sort_permission_positive_terminates_of_smaller
        mask receiver field smallerTerminates
  | PermissionMaskValid mask field =>
      exact term_sort_permission_mask_valid_terminates mask field
  | PermissionMaskTransition preMask postMask field consumed produced =>
      exact term_sort_permission_mask_transition_terminates_of_smaller
        preMask postMask field consumed produced smallerTerminates
  | Not value =>
      exact term_sort_not_terminates_of_smaller value smallerTerminates
  | And values =>
      exact term_sort_and_terminates_of_smaller values smallerTerminates
  | Or values =>
      exact term_sort_or_terminates_of_smaller values smallerTerminates
  | Implies left right =>
      exact term_sort_implies_terminates_of_smaller
        left right smallerTerminates
  | IfThenElse condition thenValue elseValue =>
      exact term_sort_if_then_else_terminates_of_smaller
        condition thenValue elseValue smallerTerminates
  | Equal left right =>
      exact term_sort_equal_terminates_of_smaller
        left right smallerTerminates
  | Less left right =>
      exact term_sort_less_terminates_of_smaller
        left right smallerTerminates
  | LessEqual left right =>
      exact term_sort_less_equal_terminates_of_smaller
        left right smallerTerminates
  | Greater left right =>
      exact term_sort_greater_terminates_of_smaller
        left right smallerTerminates
  | GreaterEqual left right =>
      exact term_sort_greater_equal_terminates_of_smaller
        left right smallerTerminates
  | Add left right =>
      exact term_sort_add_terminates_of_smaller
        left right smallerTerminates
  | Subtract left right =>
      exact term_sort_subtract_terminates_of_smaller
        left right smallerTerminates
  | Multiply left right =>
      exact term_sort_multiply_terminates_of_smaller
        left right smallerTerminates
  | FloorDivideByPositive value divisor =>
      exact term_sort_floor_divide_terminates_of_smaller
        value divisor smallerTerminates
  | Negate value =>
      exact term_sort_negate_terminates_of_smaller value smallerTerminates
  | StringConcat values =>
      exact term_sort_string_concat_terminates_of_smaller
        values smallerTerminates
  | StringLength value =>
      exact term_sort_string_length_terminates_of_smaller
        value smallerTerminates
  | BytesConcat values =>
      exact term_sort_bytes_concat_terminates_of_smaller
        values smallerTerminates
  | BytesLength value =>
      exact term_sort_bytes_length_terminates_of_smaller
        value smallerTerminates
  | BytesGet bytes index =>
      exact term_sort_bytes_get_terminates_of_smaller
        bytes index smallerTerminates
  | Tuple values =>
      exact term_sort_tuple_terminates_of_smaller values smallerTerminates
  | TupleGet tuple index =>
      exact term_sort_tuple_get_terminates_of_smaller
        tuple index smallerTerminates
  | VariadicTuple elementSort values =>
      exact term_sort_variadic_tuple_terminates_of_smaller
        elementSort values smallerTerminates
  | VariadicTupleLength value =>
      exact term_sort_variadic_tuple_length_terminates_of_smaller
        value smallerTerminates
  | VariadicTupleGet tuple index =>
      exact term_sort_variadic_tuple_get_terminates_of_smaller
        tuple index smallerTerminates
  | VariadicTupleSlice source lower upper step =>
      exact term_sort_variadic_tuple_slice_terminates_of_smaller
        source lower upper step smallerTerminates
  | List elementSort values =>
      exact term_sort_list_terminates_of_smaller
        elementSort values smallerTerminates
  | ListLength value =>
      exact term_sort_list_length_terminates_of_smaller
        value smallerTerminates
  | ListGet list index =>
      exact term_sort_list_get_terminates_of_smaller
        list index smallerTerminates
  | ListContains list value =>
      exact term_sort_list_contains_terminates_of_smaller
        list value smallerTerminates
  | ListSlice source lower upper step =>
      exact term_sort_list_slice_terminates_of_smaller
        source lower upper step smallerTerminates
  | ListConcat left right =>
      exact term_sort_list_concat_terminates_of_smaller
        left right smallerTerminates
  | ListSum source =>
      exact term_sort_list_sum_terminates_of_smaller source smallerTerminates
  | ListSorted source =>
      exact term_sort_list_sorted_terminates_of_smaller source smallerTerminates
  | ListComprehension resultName source binder elementSort mapped filter =>
      exact term_sort_list_comprehension_terminates_of_smaller
        resultName source binder elementSort mapped filter smallerTerminates
  | SetComprehension resultName source binder elementSort mapped filter =>
      exact term_sort_set_comprehension_terminates_of_smaller
        resultName source binder elementSort mapped filter smallerTerminates
  | SetLength value =>
      exact term_sort_set_length_terminates_of_smaller value smallerTerminates
  | SetContains set value =>
      exact term_sort_set_contains_terminates_of_smaller
        set value smallerTerminates
  | DictComprehension resultName source binder keySort valueSort key value filter =>
      exact term_sort_dict_comprehension_terminates_of_smaller
        resultName source binder keySort valueSort key value filter
        smallerTerminates
  | DictLength value =>
      exact term_sort_dict_length_terminates_of_smaller value smallerTerminates
  | DictContains dict key =>
      exact term_sort_dict_contains_terminates_of_smaller
        dict key smallerTerminates
  | DictGet dict key =>
      exact term_sort_dict_get_terminates_of_smaller dict key smallerTerminates
  | ForAll binder binderSort body =>
      exact term_sort_for_all_terminates_of_smaller
        binder binderSort body smallerTerminates
  | FiniteDict keySort valueSort entries =>
      exact term_sort_finite_dict_terminates_of_smaller
        keySort valueSort entries smallerTerminates
  | DictKeys keySort values =>
      exact term_sort_dict_keys_terminates_of_smaller
        keySort values smallerTerminates

/-- Public all-input no-divergence theorem for the exact extracted entrypoint. -/
theorem term_sort_extraction_entrypoint_terminates (term : VcTermSort.Term) :
    Terminates (VcTermSort.term_sort_extraction_entrypoint term) := by
  rw [entrypoint_is_term_sort]
  exact term_sort_terminates term

end VcTermSort.Proofs
