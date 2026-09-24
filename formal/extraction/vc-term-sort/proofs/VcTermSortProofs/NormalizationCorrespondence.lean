import VcTermSort.Code.RawFuns
import VcTermSortProofs.ConcreteLoops
import VcTermSortProofs.RecursiveTermination
import VcTermSortProofs.RawRecursiveTermination

open Aeneas Aeneas.Std Result ControlFlow Error

namespace VcTermSort.Proofs

theorem partial_loop_of_finite_trace {State Output : Type}
    (body : State → Result (ControlFlow State Output))
    {steps : Nat} {state : State} {result : Result Output}
    (trace : FiniteLoopTrace body steps state result) :
    loop body state = result := by
  induction trace with
  | done observed =>
      unfold loop
      simp [observed]
  | fail observed =>
      unfold loop
      simp [observed]
  | div observed =>
      unfold loop
      simp [observed]
  | cont observed tail induction =>
      unfold loop
      simp [observed, induction]

theorem partial_loop_eq_fuel_of_decreases {State Output : Type}
    (body : State → Result (ControlFlow State Output))
    (measure : State → Nat)
    (decreases : ∀ state next,
      body state = .ok (.cont next) → measure next < measure state)
    (state : State) :
    loop body state = VcTermSort.runLoopFuel (measure state + 1) body state := by
  obtain ⟨steps, result, bounded, trace⟩ :=
    finite_loop_trace_exists_of_decreases body measure decreases state
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  rw [fuel_eq]
  exact Eq.trans (partial_loop_of_finite_trace body trace)
    (run_loop_fuel_with_headroom_of_trace trace headroom).symm

theorem finite_loop_trace_congr_of_invariant {State Output : Type}
    (rawBody normalizedBody : State → Result (ControlFlow State Output))
    (invariant : State → Prop)
    (bodyEq : ∀ state, invariant state → rawBody state = normalizedBody state)
    (preserves : ∀ state next, invariant state →
      normalizedBody state = .ok (.cont next) → invariant next)
    {steps : Nat} {state : State} {result : Result Output}
    (holds : invariant state)
    (trace : FiniteLoopTrace normalizedBody steps state result) :
    FiniteLoopTrace rawBody steps state result := by
  induction trace with
  | done observed =>
      exact .done ((bodyEq _ holds).trans observed)
  | fail observed =>
      exact .fail ((bodyEq _ holds).trans observed)
  | div observed =>
      exact .div ((bodyEq _ holds).trans observed)
  | cont observed tail induction =>
      exact .cont ((bodyEq _ holds).trans observed)
        (induction (preserves _ _ holds observed))

theorem partial_loop_eq_fuel_of_invariant {State Output : Type}
    (rawBody normalizedBody : State → Result (ControlFlow State Output))
    (invariant : State → Prop)
    (measure : State → Nat)
    (bodyEq : ∀ state, invariant state → rawBody state = normalizedBody state)
    (preserves : ∀ state next, invariant state →
      normalizedBody state = .ok (.cont next) → invariant next)
    (decreases : ∀ state next,
      normalizedBody state = .ok (.cont next) → measure next < measure state)
    (state : State) (holds : invariant state) :
    loop rawBody state =
      VcTermSort.runLoopFuel (measure state + 1) normalizedBody state := by
  obtain ⟨steps, result, bounded, trace⟩ :=
    finite_loop_trace_exists_of_decreases normalizedBody measure decreases state
  have rawTrace := finite_loop_trace_congr_of_invariant
    rawBody normalizedBody invariant bodyEq preserves holds trace
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  rw [fuel_eq]
  exact Eq.trans (partial_loop_of_finite_trace rawBody rawTrace)
    (run_loop_fuel_with_headroom_of_trace trace headroom).symm

theorem raw_all_nominal_references_loop_eq_normalized
    (iter : core.slice.iter.Iter VcTermSort.Term) (result : Bool) :
    VcTermSortRaw.all_nominal_references_loop iter result =
      VcTermSort.all_nominal_references_loop iter result := by
  unfold VcTermSortRaw.all_nominal_references_loop
  unfold VcTermSort.all_nominal_references_loop
  exact partial_loop_eq_fuel_of_decreases
    (fun state =>
      VcTermSort.all_nominal_references_loop.body state.1 state.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact all_nominal_references_body_decreases
        state.1 next.1 state.2 next.2 observed)
    (iter, result)

theorem raw_all_nominal_reference_keys_loop_eq_normalized
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result : Bool) :
    VcTermSortRaw.all_nominal_reference_keys_loop iter result =
      VcTermSort.all_nominal_reference_keys_loop iter result := by
  unfold VcTermSortRaw.all_nominal_reference_keys_loop
  unfold VcTermSort.all_nominal_reference_keys_loop
  exact partial_loop_eq_fuel_of_decreases
    (fun state =>
      VcTermSort.all_nominal_reference_keys_loop.body state.1 state.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact all_nominal_reference_keys_body_decreases
        state.1 next.1 state.2 next.2 observed)
    (iter, result)

theorem raw_validate_int_enum_descriptor_loop_eq_normalized
    (iter : core.slice.iter.Iter (String × Std.I64))
    (names : alloc.collections.btree.set.BTreeSet String Global)
    (values : alloc.collections.btree.set.BTreeSet Std.I64 Global)
    (valid : Bool) :
    VcTermSortRaw.validate_int_enum_descriptor_loop iter names values valid =
      VcTermSort.validate_int_enum_descriptor_loop iter names values valid := by
  unfold VcTermSortRaw.validate_int_enum_descriptor_loop
  unfold VcTermSort.validate_int_enum_descriptor_loop
  exact partial_loop_eq_fuel_of_decreases
    (fun state => VcTermSort.validate_int_enum_descriptor_loop.body
      state.1 state.2.1 state.2.2.1 state.2.2.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact validate_int_enum_descriptor_body_decreases
        state.1 next.1 state.2.1 next.2.1 state.2.2.1 next.2.2.1
        state.2.2.2 next.2.2.2 observed)
    (iter, names, values, valid)

theorem raw_require_predicate_argument_sorts_loop_eq_normalized
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (result : core.result.Result Unit VcTermSort.SortError)
    (bodyEq : ∀ state : core.slice.iter.Iter VcTermSort.Term ×
        core.result.Result Unit VcTermSort.SortError,
      VcTermSortRaw.require_predicate_argument_sorts_loop.body state.1 state.2 =
        VcTermSort.require_predicate_argument_sorts_loop.body state.1 state.2) :
    VcTermSortRaw.require_predicate_argument_sorts_loop iter result =
      VcTermSort.require_predicate_argument_sorts_loop iter result := by
  unfold VcTermSortRaw.require_predicate_argument_sorts_loop
  unfold VcTermSort.require_predicate_argument_sorts_loop
  exact Eq.trans
    (congrArg (fun body => loop body (iter, result)) (funext bodyEq))
    (partial_loop_eq_fuel_of_decreases
    (fun state =>
      VcTermSort.require_predicate_argument_sorts_loop.body state.1 state.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact require_predicate_argument_sorts_body_decreases
        state.1 next.1 state.2 next.2 observed)
    (iter, result))

theorem raw_require_permission_transfer_amounts_loop_eq_normalized
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result : core.result.Result Unit VcTermSort.SortError)
    (bodyEq : ∀ state : core.slice.iter.Iter VcTermSort.PermissionTransferAmount ×
        core.result.Result Unit VcTermSort.SortError,
      VcTermSortRaw.require_permission_transfer_amounts_loop.body state.1 state.2 =
        VcTermSort.require_permission_transfer_amounts_loop.body state.1 state.2) :
    VcTermSortRaw.require_permission_transfer_amounts_loop iter result =
      VcTermSort.require_permission_transfer_amounts_loop iter result := by
  unfold VcTermSortRaw.require_permission_transfer_amounts_loop
  unfold VcTermSort.require_permission_transfer_amounts_loop
  exact Eq.trans
    (congrArg (fun body => loop body (iter, result)) (funext bodyEq))
    (partial_loop_eq_fuel_of_decreases
    (fun state => VcTermSort.require_permission_transfer_amounts_loop.body
      state.1 state.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact require_permission_transfer_amounts_body_decreases
        state.1 next.1 state.2 next.2 observed)
    (iter, result))

theorem raw_require_all_sorts_loop_eq_normalized
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (result : core.result.Result Unit VcTermSort.SortError)
    (bodyEq : ∀ state : core.slice.iter.Iter VcTermSort.Term ×
        core.result.Result Unit VcTermSort.SortError,
      VcTermSortRaw.require_all_sorts_loop.body expected context state.1 state.2 =
        VcTermSort.require_all_sorts_loop.body expected context state.1 state.2) :
    VcTermSortRaw.require_all_sorts_loop iter expected context result =
      VcTermSort.require_all_sorts_loop iter expected context result := by
  unfold VcTermSortRaw.require_all_sorts_loop
  unfold VcTermSort.require_all_sorts_loop
  exact Eq.trans
    (congrArg (fun body => loop body (iter, result)) (funext bodyEq))
    (partial_loop_eq_fuel_of_decreases
    (fun state => VcTermSort.require_all_sorts_loop.body
      expected context state.1 state.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact require_all_sorts_body_decreases expected context
        state.1 next.1 state.2 next.2 observed)
    (iter, result))

theorem raw_collect_sorts_loop_eq_normalized
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (sorts : VcTermSort.ModelVec VcTermSort.Sort)
    (error : Option VcTermSort.SortError)
    (bodyEq : ∀ state : core.slice.iter.Iter VcTermSort.Term ×
        VcTermSort.ModelVec VcTermSort.Sort × Option VcTermSort.SortError,
      VcTermSortRaw.collect_sorts_loop.body state.1 state.2.1 state.2.2 =
        VcTermSort.collect_sorts_loop.body state.1 state.2.1 state.2.2) :
    VcTermSortRaw.collect_sorts_loop iter sorts error =
      VcTermSort.collect_sorts_loop iter sorts error := by
  unfold VcTermSortRaw.collect_sorts_loop
  unfold VcTermSort.collect_sorts_loop
  exact Eq.trans
    (congrArg (fun body => loop body (iter, sorts, error)) (funext bodyEq))
    (partial_loop_eq_fuel_of_decreases
    (fun state => VcTermSort.collect_sorts_loop.body
      state.1 state.2.1 state.2.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact collect_sorts_body_decreases
        state.1 next.1 state.2.1 next.2.1 state.2.2 next.2.2 observed)
    (iter, sorts, error))

theorem raw_require_finite_dict_entry_sorts_loop_eq_normalized
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (keySort valueSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (bodyEq : ∀ state : core.slice.iter.Iter
        (VcTermSort.Term × VcTermSort.Term) ×
        core.result.Result Unit VcTermSort.SortError,
      VcTermSortRaw.require_finite_dict_entry_sorts_loop.body
          keySort valueSort state.1 state.2 =
        VcTermSort.require_finite_dict_entry_sorts_loop.body
          keySort valueSort state.1 state.2) :
    VcTermSortRaw.require_finite_dict_entry_sorts_loop
        iter keySort valueSort result =
      VcTermSort.require_finite_dict_entry_sorts_loop
        iter keySort valueSort result := by
  unfold VcTermSortRaw.require_finite_dict_entry_sorts_loop
  unfold VcTermSort.require_finite_dict_entry_sorts_loop
  exact Eq.trans
    (congrArg (fun body => loop body (iter, result)) (funext bodyEq))
    (partial_loop_eq_fuel_of_decreases
    (fun state => VcTermSort.require_finite_dict_entry_sorts_loop.body
      keySort valueSort state.1 state.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact require_finite_dict_entry_sorts_body_decreases keySort valueSort
        state.1 next.1 state.2 next.2 observed)
    (iter, result))

theorem raw_validate_bound_occurrences_all_loop_eq_normalized
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (bodyEq : ∀ state : core.slice.iter.Iter VcTermSort.Term ×
        core.result.Result Unit VcTermSort.SortError,
      VcTermSortRaw.validate_bound_occurrences.all_loop.body
          binder binderSort state.1 state.2 =
        VcTermSort.validate_bound_occurrences.all_loop.body
          binder binderSort state.1 state.2) :
    VcTermSortRaw.validate_bound_occurrences.all_loop
        iter binder binderSort result =
      VcTermSort.validate_bound_occurrences.all_loop
        iter binder binderSort result := by
  unfold VcTermSortRaw.validate_bound_occurrences.all_loop
  unfold VcTermSort.validate_bound_occurrences.all_loop
  exact Eq.trans
    (congrArg (fun body => loop body (iter, result)) (funext bodyEq))
    (partial_loop_eq_fuel_of_decreases
    (fun state => VcTermSort.validate_bound_occurrences.all_loop.body
      binder binderSort state.1 state.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact validate_bound_occurrences_all_body_decreases binder binderSort
        state.1 next.1 state.2 next.2 observed)
    (iter, result))

theorem raw_validate_bound_occurrences_all_transfers_loop_eq_normalized
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (bodyEq : ∀ state : core.slice.iter.Iter VcTermSort.PermissionTransferAmount ×
        core.result.Result Unit VcTermSort.SortError,
      VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body
          binder binderSort state.1 state.2 =
        VcTermSort.validate_bound_occurrences.all_transfers_loop.body
          binder binderSort state.1 state.2) :
    VcTermSortRaw.validate_bound_occurrences.all_transfers_loop
        iter binder binderSort result =
      VcTermSort.validate_bound_occurrences.all_transfers_loop
        iter binder binderSort result := by
  unfold VcTermSortRaw.validate_bound_occurrences.all_transfers_loop
  unfold VcTermSort.validate_bound_occurrences.all_transfers_loop
  exact Eq.trans
    (congrArg (fun body => loop body (iter, result)) (funext bodyEq))
    (partial_loop_eq_fuel_of_decreases
    (fun state => VcTermSort.validate_bound_occurrences.all_transfers_loop.body
      binder binderSort state.1 state.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact validate_bound_occurrences_all_transfers_body_decreases
        binder binderSort state.1 next.1 state.2 next.2 observed)
    (iter, result))

theorem raw_validate_bound_occurrences_all_entries_loop_eq_normalized
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (bodyEq : ∀ state : core.slice.iter.Iter
        (VcTermSort.Term × VcTermSort.Term) ×
        core.result.Result Unit VcTermSort.SortError,
      VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body
          binder binderSort state.1 state.2 =
        VcTermSort.validate_bound_occurrences.all_entries_loop.body
          binder binderSort state.1 state.2) :
    VcTermSortRaw.validate_bound_occurrences.all_entries_loop
        iter binder binderSort result =
      VcTermSort.validate_bound_occurrences.all_entries_loop
        iter binder binderSort result := by
  unfold VcTermSortRaw.validate_bound_occurrences.all_entries_loop
  unfold VcTermSort.validate_bound_occurrences.all_entries_loop
  exact Eq.trans
    (congrArg (fun body => loop body (iter, result)) (funext bodyEq))
    (partial_loop_eq_fuel_of_decreases
    (fun state => VcTermSort.validate_bound_occurrences.all_entries_loop.body
      binder binderSort state.1 state.2)
    (fun state => sliceIteratorRemaining state.1)
    (by
      intro state next observed
      exact validate_bound_occurrences_all_entries_body_decreases
        binder binderSort state.1 next.1 state.2 next.2 observed)
    (iter, result))

theorem raw_validate_one_eq_normalized_of_validate
    (term : VcTermSort.Term) (binder : String) (binderSort : VcTermSort.Sort)
    (validated : VcTermSortRaw.validate_bound_occurrences term binder binderSort =
      VcTermSort.validate_bound_occurrences term binder binderSort) :
    VcTermSortRaw.validate_bound_occurrences.one term binder binderSort =
      VcTermSort.validate_bound_occurrences.one term binder binderSort := by
  rw [VcTermSortRaw.validate_bound_occurrences.one.eq_def]
  rw [VcTermSort.validate_bound_occurrences.one.eq_def]
  exact validated

theorem raw_validate_two_eq_normalized_of_validate
    (left right : VcTermSort.Term)
    (binder : String) (binderSort : VcTermSort.Sort)
    (leftValidated : VcTermSortRaw.validate_bound_occurrences left binder binderSort =
      VcTermSort.validate_bound_occurrences left binder binderSort)
    (rightValidated : VcTermSortRaw.validate_bound_occurrences right binder binderSort =
      VcTermSort.validate_bound_occurrences right binder binderSort) :
    VcTermSortRaw.validate_bound_occurrences.two left right binder binderSort =
      VcTermSort.validate_bound_occurrences.two left right binder binderSort := by
  rw [VcTermSortRaw.validate_bound_occurrences.two.eq_def]
  rw [VcTermSort.validate_bound_occurrences.two.eq_def]
  rw [raw_validate_one_eq_normalized_of_validate left binder binderSort leftValidated]
  rw [raw_validate_one_eq_normalized_of_validate right binder binderSort rightValidated]
  rfl

theorem raw_validate_all_loop_eq_normalized_of_children
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenEq : ∀ child, child ∈ iter.slice.val →
      VcTermSortRaw.validate_bound_occurrences child binder binderSort =
        VcTermSort.validate_bound_occurrences child binder binderSort) :
    VcTermSortRaw.validate_bound_occurrences.all_loop iter binder binderSort result =
      VcTermSort.validate_bound_occurrences.all_loop iter binder binderSort result := by
  unfold VcTermSortRaw.validate_bound_occurrences.all_loop
  unfold VcTermSort.validate_bound_occurrences.all_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.validate_bound_occurrences.all_loop.body
      binder binderSort state.1 state.2)
    (fun state => VcTermSort.validate_bound_occurrences.all_loop.body
      binder binderSort state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.validate_bound_occurrences.all_loop.body.eq_def]
    rw [VcTermSort.validate_bound_occurrences.all_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail error => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeTerm, next⟩ := pair
        cases maybeTerm with
        | none => simp [observed]
        | some term =>
            have member := (slice_iterator_next_some_member
              current next term observed).1
            rw [sliceEq] at member
            have currentEq := childrenEq term member
            cases currentResult <;>
              simp [observed, raw_validate_one_eq_normalized_of_validate
                term binder binderSort currentEq]
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        validate_bound_occurrences_all_body_preserves_slice
          binder binderSort state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact validate_bound_occurrences_all_body_decreases binder binderSort
      state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_validate_all_eq_normalized_of_children
    (terms : Slice VcTermSort.Term)
    (binder : String) (binderSort : VcTermSort.Sort)
    (childrenEq : ∀ child, child ∈ terms.val →
      VcTermSortRaw.validate_bound_occurrences child binder binderSort =
        VcTermSort.validate_bound_occurrences child binder binderSort) :
    VcTermSortRaw.validate_bound_occurrences.all terms binder binderSort =
      VcTermSort.validate_bound_occurrences.all terms binder binderSort := by
  rw [VcTermSortRaw.validate_bound_occurrences.all.eq_def]
  rw [VcTermSort.validate_bound_occurrences.all.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply raw_validate_all_loop_eq_normalized_of_children
  simpa using childrenEq

theorem raw_validate_all_transfers_loop_eq_normalized_of_receivers
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (receiversEq : ∀ amount, amount ∈ iter.slice.val →
      VcTermSortRaw.validate_bound_occurrences amount.receiver binder binderSort =
        VcTermSort.validate_bound_occurrences amount.receiver binder binderSort) :
    VcTermSortRaw.validate_bound_occurrences.all_transfers_loop
        iter binder binderSort result =
      VcTermSort.validate_bound_occurrences.all_transfers_loop
        iter binder binderSort result := by
  unfold VcTermSortRaw.validate_bound_occurrences.all_transfers_loop
  unfold VcTermSort.validate_bound_occurrences.all_transfers_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body
      binder binderSort state.1 state.2)
    (fun state => VcTermSort.validate_bound_occurrences.all_transfers_loop.body
      binder binderSort state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body.eq_def]
    rw [VcTermSort.validate_bound_occurrences.all_transfers_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail error => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeAmount, next⟩ := pair
        cases maybeAmount with
        | none => simp [observed]
        | some amount =>
            have member := (slice_iterator_next_some_member
              current next amount observed).1
            rw [sliceEq] at member
            have currentEq := receiversEq amount member
            cases currentResult <;>
              simp [observed, raw_validate_one_eq_normalized_of_validate
                amount.receiver binder binderSort currentEq]
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        validate_bound_occurrences_all_transfers_body_preserves_slice
          binder binderSort state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact validate_bound_occurrences_all_transfers_body_decreases binder binderSort
      state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_validate_all_transfers_eq_normalized_of_receivers
    (amounts : Slice VcTermSort.PermissionTransferAmount)
    (binder : String) (binderSort : VcTermSort.Sort)
    (receiversEq : ∀ amount, amount ∈ amounts.val →
      VcTermSortRaw.validate_bound_occurrences amount.receiver binder binderSort =
        VcTermSort.validate_bound_occurrences amount.receiver binder binderSort) :
    VcTermSortRaw.validate_bound_occurrences.all_transfers
        amounts binder binderSort =
      VcTermSort.validate_bound_occurrences.all_transfers
        amounts binder binderSort := by
  rw [VcTermSortRaw.validate_bound_occurrences.all_transfers.eq_def]
  rw [VcTermSort.validate_bound_occurrences.all_transfers.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply raw_validate_all_transfers_loop_eq_normalized_of_receivers
  simpa using receiversEq

theorem raw_validate_all_entries_loop_eq_normalized_of_entries
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (entriesEq : ∀ entry, entry ∈ iter.slice.val →
      (VcTermSortRaw.validate_bound_occurrences entry.1 binder binderSort =
        VcTermSort.validate_bound_occurrences entry.1 binder binderSort) ∧
      (VcTermSortRaw.validate_bound_occurrences entry.2 binder binderSort =
        VcTermSort.validate_bound_occurrences entry.2 binder binderSort)) :
    VcTermSortRaw.validate_bound_occurrences.all_entries_loop
        iter binder binderSort result =
      VcTermSort.validate_bound_occurrences.all_entries_loop
        iter binder binderSort result := by
  unfold VcTermSortRaw.validate_bound_occurrences.all_entries_loop
  unfold VcTermSort.validate_bound_occurrences.all_entries_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body
      binder binderSort state.1 state.2)
    (fun state => VcTermSort.validate_bound_occurrences.all_entries_loop.body
      binder binderSort state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body.eq_def]
    rw [VcTermSort.validate_bound_occurrences.all_entries_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail error => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeEntry, next⟩ := pair
        cases maybeEntry with
        | none => simp [observed]
        | some entry =>
            obtain ⟨key, value⟩ := entry
            have member := (slice_iterator_next_some_member
              current next (key, value) observed).1
            rw [sliceEq] at member
            have currentEq := entriesEq (key, value) member
            cases currentResult <;>
              simp [observed, raw_validate_two_eq_normalized_of_validate
                key value binder binderSort currentEq.1 currentEq.2]
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        validate_bound_occurrences_all_entries_body_preserves_slice
          binder binderSort state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact validate_bound_occurrences_all_entries_body_decreases binder binderSort
      state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_validate_all_entries_eq_normalized_of_entries
    (entries : Slice (VcTermSort.Term × VcTermSort.Term))
    (binder : String) (binderSort : VcTermSort.Sort)
    (entriesEq : ∀ entry, entry ∈ entries.val →
      (VcTermSortRaw.validate_bound_occurrences entry.1 binder binderSort =
        VcTermSort.validate_bound_occurrences entry.1 binder binderSort) ∧
      (VcTermSortRaw.validate_bound_occurrences entry.2 binder binderSort =
        VcTermSort.validate_bound_occurrences entry.2 binder binderSort)) :
    VcTermSortRaw.validate_bound_occurrences.all_entries
        entries binder binderSort =
      VcTermSort.validate_bound_occurrences.all_entries
        entries binder binderSort := by
  rw [VcTermSortRaw.validate_bound_occurrences.all_entries.eq_def]
  rw [VcTermSort.validate_bound_occurrences.all_entries.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply raw_validate_all_entries_loop_eq_normalized_of_entries
  simpa using entriesEq

theorem raw_validate_bound_occurrences_eq_normalized_of_smaller
    (term : VcTermSort.Term) (binder : String) (binderSort : VcTermSort.Sort)
    (smallerEq : ∀ child, TermStrictlySmaller child term →
      VcTermSortRaw.validate_bound_occurrences child binder binderSort =
        VcTermSort.validate_bound_occurrences child binder binderSort) :
    VcTermSortRaw.validate_bound_occurrences term binder binderSort =
      VcTermSort.validate_bound_occurrences term binder binderSort := by
  rw [VcTermSortRaw.validate_bound_occurrences.eq_def term]
  rw [VcTermSort.validate_bound_occurrences.eq_def term]
  cases term <;> simp only
  all_goals first
    | rfl
    | apply raw_validate_one_eq_normalized_of_validate
      apply smallerEq
      simp [TermStrictlySmaller] <;> omega
    | apply raw_validate_two_eq_normalized_of_validate <;>
        apply smallerEq <;> simp [TermStrictlySmaller] <;> omega
    | skip
  all_goals first
    | apply raw_validate_all_eq_normalized_of_children
      intro child member
      apply smallerEq child
      change child ∈ List.take Usize.max
        (show List VcTermSort.Term from _) at member
      have sourceMember := List.mem_of_mem_take member
      unfold TermStrictlySmaller
      have childBelow := List.sizeOf_lt_of_mem sourceMember
      simp at childBelow ⊢
      omega
    | skip
  case PermissionMaskTransition preMask postMask field consumed produced =>
    have consumedEq :
        VcTermSortRaw.validate_bound_occurrences.all_transfers
            (VcTermSort.ModelVec.deref consumed) binder binderSort =
          VcTermSort.validate_bound_occurrences.all_transfers
            (VcTermSort.ModelVec.deref consumed) binder binderSort := by
      apply raw_validate_all_transfers_eq_normalized_of_receivers
      intro amount member
      apply smallerEq amount.receiver
      change amount ∈ List.take Usize.max
        (show List VcTermSort.PermissionTransferAmount from consumed) at member
      have sourceMember := List.mem_of_mem_take member
      exact permission_receiver_strictly_smaller amount consumed
        (.PermissionMaskTransition preMask postMask field consumed produced)
        sourceMember (by simp <;> omega)
    have producedEq :
        VcTermSortRaw.validate_bound_occurrences.all_transfers
            (VcTermSort.ModelVec.deref produced) binder binderSort =
          VcTermSort.validate_bound_occurrences.all_transfers
            (VcTermSort.ModelVec.deref produced) binder binderSort := by
      apply raw_validate_all_transfers_eq_normalized_of_receivers
      intro amount member
      apply smallerEq amount.receiver
      change amount ∈ List.take Usize.max
        (show List VcTermSort.PermissionTransferAmount from produced) at member
      have sourceMember := List.mem_of_mem_take member
      exact permission_receiver_strictly_smaller amount produced
        (.PermissionMaskTransition preMask postMask field consumed produced)
        sourceMember (by simp <;> omega)
    rw [consumedEq, producedEq]
    rfl
  case IfThenElse condition thenValue elseValue =>
    have conditionEq := raw_validate_one_eq_normalized_of_validate
      condition binder binderSort (smallerEq condition (by
        simp [TermStrictlySmaller] <;> omega))
    have thenEq := raw_validate_one_eq_normalized_of_validate
      thenValue binder binderSort (smallerEq thenValue (by
        simp [TermStrictlySmaller] <;> omega))
    have elseEq := raw_validate_one_eq_normalized_of_validate
      elseValue binder binderSort (smallerEq elseValue (by
        simp [TermStrictlySmaller] <;> omega))
    rw [conditionEq, thenEq, elseEq]
    rfl
  case ListComprehension resultName source nested nestedSort mapped filter =>
    have sourceEq := raw_validate_one_eq_normalized_of_validate
      source binder binderSort (smallerEq source (by
        simp [TermStrictlySmaller] <;> omega))
    have mappedEq := raw_validate_one_eq_normalized_of_validate
      mapped binder binderSort (smallerEq mapped (by
        simp [TermStrictlySmaller] <;> omega))
    rw [sourceEq, mappedEq]
    cases filter with
    | none => rfl
    | some filterTerm =>
        have filterEq := raw_validate_one_eq_normalized_of_validate
          filterTerm binder binderSort (smallerEq filterTerm (by
            simp [TermStrictlySmaller] <;> omega))
        simp only
        rw [filterEq]
        rfl
  case SetComprehension resultName source nested nestedSort mapped filter =>
    have sourceEq := raw_validate_one_eq_normalized_of_validate
      source binder binderSort (smallerEq source (by
        simp [TermStrictlySmaller] <;> omega))
    have mappedEq := raw_validate_one_eq_normalized_of_validate
      mapped binder binderSort (smallerEq mapped (by
        simp [TermStrictlySmaller] <;> omega))
    rw [sourceEq, mappedEq]
    cases filter with
    | none => rfl
    | some filterTerm =>
        have filterEq := raw_validate_one_eq_normalized_of_validate
          filterTerm binder binderSort (smallerEq filterTerm (by
            simp [TermStrictlySmaller] <;> omega))
        simp only
        rw [filterEq]
        rfl
  case DictComprehension resultName source nested nestedSort keySort key value filter =>
    have sourceEq := raw_validate_one_eq_normalized_of_validate
      source binder binderSort (smallerEq source (by
        simp [TermStrictlySmaller] <;> omega))
    have pairEq := raw_validate_two_eq_normalized_of_validate
      key value binder binderSort
      (smallerEq key (by simp [TermStrictlySmaller] <;> omega))
      (smallerEq value (by simp [TermStrictlySmaller] <;> omega))
    rw [sourceEq, pairEq]
    cases filter with
    | none => rfl
    | some filterTerm =>
        have filterEq := raw_validate_one_eq_normalized_of_validate
          filterTerm binder binderSort (smallerEq filterTerm (by
            simp [TermStrictlySmaller] <;> omega))
        simp only
        rw [filterEq]
        rfl
  case ForAll nested nestedSort body =>
    have bodyEq := raw_validate_one_eq_normalized_of_validate
      body binder binderSort (smallerEq body (by
        simp [TermStrictlySmaller]))
    rw [bodyEq]
  case FiniteDict keySort valueSort entries =>
    apply raw_validate_all_entries_eq_normalized_of_entries
    intro entry member
    change entry ∈ List.take Usize.max
      (show List (VcTermSort.Term × VcTermSort.Term) from entries) at member
    have sourceMember := List.mem_of_mem_take member
    constructor
    · apply smallerEq entry.1
      exact finite_dict_key_strictly_smaller entry entries
        (.FiniteDict keySort valueSort entries) sourceMember (by simp)
    · apply smallerEq entry.2
      exact finite_dict_value_strictly_smaller entry entries
        (.FiniteDict keySort valueSort entries) sourceMember (by simp)

theorem raw_validate_bound_occurrences_eq_normalized
    (term : VcTermSort.Term) (binder : String) (binderSort : VcTermSort.Sort) :
    VcTermSortRaw.validate_bound_occurrences term binder binderSort =
      VcTermSort.validate_bound_occurrences term binder binderSort := by
  apply term_strictly_smaller_well_founded.induction term
  intro current smallerEq
  exact raw_validate_bound_occurrences_eq_normalized_of_smaller
    current binder binderSort smallerEq

theorem model_vec_deref_member {T : Type} {value : T}
    {values : VcTermSort.ModelVec T}
    (member : value ∈ (VcTermSort.ModelVec.deref values).val) :
    value ∈ (show List T from values) := by
  change value ∈ List.take Usize.max values at member
  exact List.mem_of_mem_take member

theorem raw_require_sort_eq_normalized_of_sort
    (term : VcTermSort.Term) (expected : VcTermSort.Sort)
    (context : VcTermSort.SortContext)
    (sortEq : VcTermSortRaw.Term.sort_typed term =
      VcTermSort.Term.sort_typed term) :
    VcTermSortRaw.require_sort term expected context =
      VcTermSort.require_sort term expected context := by
  rw [VcTermSortRaw.require_sort.eq_def]
  rw [VcTermSort.require_sort.eq_def]
  rw [sortEq]
  rfl

theorem raw_all_nominal_references_eq_normalized
    (values : Slice VcTermSort.Term) :
    VcTermSortRaw.all_nominal_references values =
      VcTermSort.all_nominal_references values := by
  rw [VcTermSortRaw.all_nominal_references.eq_def]
  rw [VcTermSort.all_nominal_references.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  exact raw_all_nominal_references_loop_eq_normalized ⟨values, 0⟩ true

theorem raw_all_nominal_reference_keys_eq_normalized
    (entries : Slice (VcTermSort.Term × VcTermSort.Term)) :
    VcTermSortRaw.all_nominal_reference_keys entries =
      VcTermSort.all_nominal_reference_keys entries := by
  rw [VcTermSortRaw.all_nominal_reference_keys.eq_def]
  rw [VcTermSort.all_nominal_reference_keys.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  exact raw_all_nominal_reference_keys_loop_eq_normalized ⟨entries, 0⟩ true

theorem raw_validate_int_enum_descriptor_eq_normalized
    (descriptor : VcTermSort.IntEnumDescriptor) :
    VcTermSortRaw.validate_int_enum_descriptor descriptor =
      VcTermSort.validate_int_enum_descriptor descriptor := by
  rw [VcTermSortRaw.validate_int_enum_descriptor.eq_def]
  rw [VcTermSort.validate_int_enum_descriptor.eq_def]
  simp_rw [raw_validate_int_enum_descriptor_loop_eq_normalized]

theorem raw_all_list_element_sorts_loop_eq_normalized_of_children
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool)
    (childrenEq : ∀ child, child ∈ iter.slice.val →
      VcTermSortRaw.is_list_element_sort child =
        VcTermSort.is_list_element_sort child) :
    VcTermSortRaw.all_list_element_sorts_loop iter result =
      VcTermSort.all_list_element_sorts_loop iter result := by
  unfold VcTermSortRaw.all_list_element_sorts_loop
  unfold VcTermSort.all_list_element_sorts_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.all_list_element_sorts_loop.body
      state.1 state.2)
    (fun state => VcTermSort.all_list_element_sorts_loop.body
      state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.all_list_element_sorts_loop.body.eq_def]
    rw [VcTermSort.all_list_element_sorts_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail error => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeElement, next⟩ := pair
        cases maybeElement with
        | none => simp [observed]
        | some element =>
            have member := (slice_iterator_next_some_member
              current next element observed).1
            rw [sliceEq] at member
            cases currentResult <;> simp [observed, childrenEq element member]
  · intro state next sliceEq continued
    have normalizedContinued := continued
    rw [VcTermSort.all_list_element_sorts_loop.body.eq_def] at normalizedContinued
    calc
      next.1.slice = state.1.slice := sort_bool_accumulator_body_preserves_slice
        VcTermSort.is_list_element_sort state.1 next.1 state.2 next.2
        normalizedContinued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact all_list_element_sorts_body_decreases
      state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_all_finite_dict_key_sorts_loop_eq_normalized_of_children
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool)
    (childrenEq : ∀ child, child ∈ iter.slice.val →
      VcTermSortRaw.is_finite_dict_key_sort child =
        VcTermSort.is_finite_dict_key_sort child) :
    VcTermSortRaw.all_finite_dict_key_sorts_loop iter result =
      VcTermSort.all_finite_dict_key_sorts_loop iter result := by
  unfold VcTermSortRaw.all_finite_dict_key_sorts_loop
  unfold VcTermSort.all_finite_dict_key_sorts_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.all_finite_dict_key_sorts_loop.body
      state.1 state.2)
    (fun state => VcTermSort.all_finite_dict_key_sorts_loop.body
      state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.all_finite_dict_key_sorts_loop.body.eq_def]
    rw [VcTermSort.all_finite_dict_key_sorts_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail error => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeElement, next⟩ := pair
        cases maybeElement with
        | none => simp [observed]
        | some element =>
            have member := (slice_iterator_next_some_member
              current next element observed).1
            rw [sliceEq] at member
            cases currentResult <;> simp [observed, childrenEq element member]
  · intro state next sliceEq continued
    have normalizedContinued := continued
    rw [VcTermSort.all_finite_dict_key_sorts_loop.body.eq_def] at normalizedContinued
    calc
      next.1.slice = state.1.slice := sort_bool_accumulator_body_preserves_slice
        VcTermSort.is_finite_dict_key_sort state.1 next.1 state.2 next.2
        normalizedContinued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact all_finite_dict_key_sorts_body_decreases
      state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_all_finite_dict_value_sorts_loop_eq_normalized_of_children
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool)
    (childrenEq : ∀ child, child ∈ iter.slice.val →
      VcTermSortRaw.is_finite_dict_value_sort child =
        VcTermSort.is_finite_dict_value_sort child) :
    VcTermSortRaw.all_finite_dict_value_sorts_loop iter result =
      VcTermSort.all_finite_dict_value_sorts_loop iter result := by
  unfold VcTermSortRaw.all_finite_dict_value_sorts_loop
  unfold VcTermSort.all_finite_dict_value_sorts_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.all_finite_dict_value_sorts_loop.body
      state.1 state.2)
    (fun state => VcTermSort.all_finite_dict_value_sorts_loop.body
      state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.all_finite_dict_value_sorts_loop.body.eq_def]
    rw [VcTermSort.all_finite_dict_value_sorts_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail error => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeElement, next⟩ := pair
        cases maybeElement with
        | none => simp [observed]
        | some element =>
            have member := (slice_iterator_next_some_member
              current next element observed).1
            rw [sliceEq] at member
            cases currentResult <;> simp [observed, childrenEq element member]
  · intro state next sliceEq continued
    have normalizedContinued := continued
    rw [VcTermSort.all_finite_dict_value_sorts_loop.body.eq_def] at normalizedContinued
    calc
      next.1.slice = state.1.slice := sort_bool_accumulator_body_preserves_slice
        VcTermSort.is_finite_dict_value_sort state.1 next.1 state.2 next.2
        normalizedContinued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact all_finite_dict_value_sorts_body_decreases
      state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_all_list_element_sorts_eq_normalized_of_children
    (values : Slice VcTermSort.Sort)
    (childrenEq : ∀ child, child ∈ values.val →
      VcTermSortRaw.is_list_element_sort child =
        VcTermSort.is_list_element_sort child) :
    VcTermSortRaw.all_list_element_sorts values =
      VcTermSort.all_list_element_sorts values := by
  rw [VcTermSortRaw.all_list_element_sorts.eq_def]
  rw [VcTermSort.all_list_element_sorts.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  exact raw_all_list_element_sorts_loop_eq_normalized_of_children
    ⟨values, 0⟩ true childrenEq

theorem raw_all_finite_dict_key_sorts_eq_normalized_of_children
    (values : Slice VcTermSort.Sort)
    (childrenEq : ∀ child, child ∈ values.val →
      VcTermSortRaw.is_finite_dict_key_sort child =
        VcTermSort.is_finite_dict_key_sort child) :
    VcTermSortRaw.all_finite_dict_key_sorts values =
      VcTermSort.all_finite_dict_key_sorts values := by
  rw [VcTermSortRaw.all_finite_dict_key_sorts.eq_def]
  rw [VcTermSort.all_finite_dict_key_sorts.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  exact raw_all_finite_dict_key_sorts_loop_eq_normalized_of_children
    ⟨values, 0⟩ true childrenEq

theorem raw_all_finite_dict_value_sorts_eq_normalized_of_children
    (values : Slice VcTermSort.Sort)
    (childrenEq : ∀ child, child ∈ values.val →
      VcTermSortRaw.is_finite_dict_value_sort child =
        VcTermSort.is_finite_dict_value_sort child) :
    VcTermSortRaw.all_finite_dict_value_sorts values =
      VcTermSort.all_finite_dict_value_sorts values := by
  rw [VcTermSortRaw.all_finite_dict_value_sorts.eq_def]
  rw [VcTermSort.all_finite_dict_value_sorts.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  exact raw_all_finite_dict_value_sorts_loop_eq_normalized_of_children
    ⟨values, 0⟩ true childrenEq

def SortPredicatesCorrespond (sort : VcTermSort.Sort) : Prop :=
  VcTermSortRaw.is_list_element_sort sort =
      VcTermSort.is_list_element_sort sort ∧
  VcTermSortRaw.is_finite_dict_key_sort sort =
      VcTermSort.is_finite_dict_key_sort sort ∧
  VcTermSortRaw.is_finite_dict_value_sort sort =
      VcTermSort.is_finite_dict_value_sort sort ∧
  VcTermSortRaw.is_variadic_tuple_element_sort sort =
      VcTermSort.is_variadic_tuple_element_sort sort

local macro "solve_sort_predicate_base" : tactic =>
  `(tactic| simp [SortPredicatesCorrespond,
    VcTermSortRaw.is_list_element_sort.eq_def,
    VcTermSort.is_list_element_sort.eq_def,
    VcTermSortRaw.is_finite_dict_key_sort.eq_def,
    VcTermSort.is_finite_dict_key_sort.eq_def,
    VcTermSortRaw.is_finite_dict_value_sort.eq_def,
    VcTermSort.is_finite_dict_value_sort.eq_def,
    VcTermSortRaw.is_variadic_tuple_element_sort.eq_def,
    VcTermSort.is_variadic_tuple_element_sort.eq_def])

theorem raw_sort_predicates_eq_normalized (sort : VcTermSort.Sort) :
    SortPredicatesCorrespond sort := by
  refine VcTermSort.Sort.rec
    (motive_1 := SortPredicatesCorrespond)
    (motive_2 := fun elements =>
      ∀ child, child ∈ elements → SortPredicatesCorrespond child)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sort
  · unfold SortPredicatesCorrespond
    constructor
    · rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      simp
    · constructor
      · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
        rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      · constructor
        · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
          rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp
        · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSortRaw.is_list_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp
  · unfold SortPredicatesCorrespond
    constructor
    · rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      simp
    · constructor
      · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
        rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      · constructor
        · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
          rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp
        · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSortRaw.is_list_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp
  · unfold SortPredicatesCorrespond
    constructor
    · rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      simp
    · constructor
      · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
        rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      · constructor
        · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
          rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp
        · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSortRaw.is_list_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp
  · unfold SortPredicatesCorrespond
    constructor
    · rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      simp
    · constructor
      · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
        rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      · constructor
        · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
          rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp
        · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSortRaw.is_list_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp
  · unfold SortPredicatesCorrespond
    constructor
    · rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      simp
    · constructor
      · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
        rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      · constructor
        · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
          rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp
        · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSortRaw.is_list_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp
  · unfold SortPredicatesCorrespond
    constructor
    · rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      simp
    · constructor
      · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
        rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      · constructor
        · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
          rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp
        · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSortRaw.is_list_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp
  · unfold SortPredicatesCorrespond
    constructor
    · rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      simp
    · constructor
      · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
        rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      · constructor
        · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
          rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp
        · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSortRaw.is_list_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp
  · unfold SortPredicatesCorrespond
    constructor
    · rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      simp
    · constructor
      · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
        rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      · constructor
        · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
          rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp
        · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSortRaw.is_list_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp
  · unfold SortPredicatesCorrespond
    constructor
    · rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      simp
    · constructor
      · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
        rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      · constructor
        · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
          rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp
        · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSortRaw.is_list_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp
  · intro elements childrenEq
    unfold VcTermSort.ModelVec at *
    have listEq := raw_all_list_element_sorts_eq_normalized_of_children
      (VcTermSort.ModelVec.deref elements) (by
        intro child member
        exact (childrenEq child (List.mem_of_mem_take member)).1)
    have keyEq := raw_all_finite_dict_key_sorts_eq_normalized_of_children
      (VcTermSort.ModelVec.deref elements) (by
        intro child member
        exact (childrenEq child (List.mem_of_mem_take member)).2.1)
    have valueEq := raw_all_finite_dict_value_sorts_eq_normalized_of_children
      (VcTermSort.ModelVec.deref elements) (by
        intro child member
        exact (childrenEq child (List.mem_of_mem_take member)).2.2.1)
    unfold SortPredicatesCorrespond
    have tupleListEq :
        VcTermSortRaw.is_list_element_sort (.Tuple elements) =
          VcTermSort.is_list_element_sort (.Tuple elements) := by
      rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases rawObserved : VcTermSortRaw.all_list_element_sorts
          (VcTermSort.ModelVec.deref elements) <;>
        cases normalizedObserved : VcTermSort.all_list_element_sorts
          (VcTermSort.ModelVec.deref elements) <;>
        simp [rawObserved, normalizedObserved] at listEq ⊢ <;>
        subst_vars <;> rfl
    refine ⟨tupleListEq, ?_, ?_, ?_⟩
    · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
      rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      cases rawObserved : VcTermSortRaw.all_finite_dict_key_sorts
          (VcTermSort.ModelVec.deref elements) <;>
        cases normalizedObserved : VcTermSort.all_finite_dict_key_sorts
          (VcTermSort.ModelVec.deref elements) <;>
        simp [rawObserved, normalizedObserved] at keyEq ⊢ <;>
        subst_vars <;> rfl
    · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases rawObserved : VcTermSortRaw.all_finite_dict_value_sorts
          (VcTermSort.ModelVec.deref elements) <;>
        cases normalizedObserved : VcTermSort.all_finite_dict_value_sorts
          (VcTermSort.ModelVec.deref elements) <;>
        simp [rawObserved, normalizedObserved] at valueEq ⊢ <;>
        subst_vars <;> rfl
    · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
      rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
      rw [tupleListEq]
  · intro element childEq
    rcases childEq with ⟨listEq, keyEq, valueEq, variadicEq⟩
    unfold SortPredicatesCorrespond
    have wholeListEq :
        VcTermSortRaw.is_list_element_sort (.VariadicTuple element) =
          VcTermSort.is_list_element_sort (.VariadicTuple element) := by
      rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases rawObserved : VcTermSortRaw.is_list_element_sort element <;>
        cases normalizedObserved : VcTermSort.is_list_element_sort element <;>
        simp [rawObserved, normalizedObserved] at listEq ⊢ <;>
        subst_vars <;> rfl
    refine ⟨wholeListEq, ?_, ?_, ?_⟩
    · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
      rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      cases rawObserved : VcTermSortRaw.is_finite_dict_key_sort element <;>
        cases normalizedObserved : VcTermSort.is_finite_dict_key_sort element <;>
        simp [rawObserved, normalizedObserved] at keyEq ⊢ <;>
        subst_vars <;> rfl
    · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases rawObserved : VcTermSortRaw.is_finite_dict_value_sort element <;>
        cases normalizedObserved : VcTermSort.is_finite_dict_value_sort element <;>
        simp [rawObserved, normalizedObserved] at valueEq ⊢ <;>
        subst_vars <;> rfl
    · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
      rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
      cases rawListObserved : VcTermSortRaw.is_list_element_sort
          (.VariadicTuple element) <;>
        cases normalizedListObserved : VcTermSort.is_list_element_sort
          (.VariadicTuple element) <;>
        simp [rawListObserved, normalizedListObserved] at wholeListEq ⊢ <;>
        subst_vars
      all_goals try rfl
      cases rawObserved : VcTermSortRaw.is_variadic_tuple_element_sort element <;>
        cases normalizedObserved : VcTermSort.is_variadic_tuple_element_sort element <;>
        simp [rawObserved, normalizedObserved] at variadicEq ⊢ <;>
        subst_vars <;> rfl
  · intro element childEq
    rcases childEq with ⟨listEq, keyEq, valueEq, variadicEq⟩
    unfold SortPredicatesCorrespond
    have wholeListEq :
        VcTermSortRaw.is_list_element_sort (.List element) =
          VcTermSort.is_list_element_sort (.List element) := by
      rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases rawObserved : VcTermSortRaw.is_list_element_sort element <;>
        cases normalizedObserved : VcTermSort.is_list_element_sort element <;>
        simp [rawObserved, normalizedObserved] at listEq ⊢ <;>
        subst_vars <;> rfl
    refine ⟨wholeListEq, ?_, ?_, ?_⟩
    · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
      rw [VcTermSort.is_finite_dict_key_sort.eq_def]
    · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases rawObserved : VcTermSortRaw.is_finite_dict_value_sort element <;>
        cases normalizedObserved : VcTermSort.is_finite_dict_value_sort element <;>
        simp [rawObserved, normalizedObserved] at valueEq ⊢ <;>
        subst_vars <;> rfl
    · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
      rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
      rw [wholeListEq]
  · intro element childEq
    rcases childEq with ⟨listEq, keyEq, valueEq, variadicEq⟩
    unfold SortPredicatesCorrespond
    have wholeListEq :
        VcTermSortRaw.is_list_element_sort (.Set element) =
          VcTermSort.is_list_element_sort (.Set element) := by
      rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases rawObserved : VcTermSortRaw.is_finite_dict_key_sort element <;>
        cases normalizedObserved : VcTermSort.is_finite_dict_key_sort element <;>
        simp [rawObserved, normalizedObserved] at keyEq ⊢ <;>
        subst_vars <;> rfl
    refine ⟨wholeListEq, ?_, ?_, ?_⟩
    · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
      rw [VcTermSort.is_finite_dict_key_sort.eq_def]
    · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases rawObserved : VcTermSortRaw.is_finite_dict_key_sort element <;>
        cases normalizedObserved : VcTermSort.is_finite_dict_key_sort element <;>
        simp [rawObserved, normalizedObserved] at keyEq ⊢ <;>
        subst_vars <;> rfl
    · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
      rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
      rw [wholeListEq]
  · intro key value keyEq valueEq
    rcases keyEq with ⟨keyListEq, keyKeyEq, keyValueEq, keyVariadicEq⟩
    rcases valueEq with
      ⟨valueListEq, valueKeyEq, valueValueEq, valueVariadicEq⟩
    unfold SortPredicatesCorrespond
    have wholeListEq :
        VcTermSortRaw.is_list_element_sort (.Dict key value) =
          VcTermSort.is_list_element_sort (.Dict key value) := by
      rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases rawKeyObserved : VcTermSortRaw.is_finite_dict_key_sort key <;>
        cases normalizedKeyObserved : VcTermSort.is_finite_dict_key_sort key <;>
        simp [rawKeyObserved, normalizedKeyObserved] at keyKeyEq ⊢ <;>
        subst_vars
      all_goals try rfl
      cases rawValueObserved : VcTermSortRaw.is_list_element_sort value <;>
        cases normalizedValueObserved : VcTermSort.is_list_element_sort value <;>
        simp [rawValueObserved, normalizedValueObserved] at valueListEq ⊢ <;>
        subst_vars <;> rfl
    refine ⟨wholeListEq, ?_, ?_, ?_⟩
    · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
      rw [VcTermSort.is_finite_dict_key_sort.eq_def]
    · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases rawKeyObserved : VcTermSortRaw.is_finite_dict_key_sort key <;>
        cases normalizedKeyObserved : VcTermSort.is_finite_dict_key_sort key <;>
        simp [rawKeyObserved, normalizedKeyObserved] at keyKeyEq ⊢ <;>
        subst_vars
      all_goals try rfl
      cases rawValueObserved : VcTermSortRaw.is_finite_dict_value_sort value <;>
        cases normalizedValueObserved :
          VcTermSort.is_finite_dict_value_sort value <;>
        simp [rawValueObserved, normalizedValueObserved] at valueValueEq ⊢ <;>
        subst_vars <;> rfl
    · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
      rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
      rw [wholeListEq]
  · intro key value keyEq valueEq
    rcases keyEq with ⟨keyListEq, keyKeyEq, keyValueEq, keyVariadicEq⟩
    rcases valueEq with
      ⟨valueListEq, valueKeyEq, valueValueEq, valueVariadicEq⟩
    unfold SortPredicatesCorrespond
    have wholeListEq :
        VcTermSortRaw.is_list_element_sort (.FiniteDict key value) =
          VcTermSort.is_list_element_sort (.FiniteDict key value) := by
      rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      cases rawKeyObserved : VcTermSortRaw.is_finite_dict_key_sort key <;>
        cases normalizedKeyObserved : VcTermSort.is_finite_dict_key_sort key <;>
        simp [rawKeyObserved, normalizedKeyObserved] at keyKeyEq ⊢ <;>
        subst_vars
      all_goals try rfl
      cases rawValueObserved : VcTermSortRaw.is_list_element_sort value <;>
        cases normalizedValueObserved : VcTermSort.is_list_element_sort value <;>
        simp [rawValueObserved, normalizedValueObserved] at valueListEq ⊢ <;>
        subst_vars <;> rfl
    refine ⟨wholeListEq, ?_, ?_, ?_⟩
    · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
      rw [VcTermSort.is_finite_dict_key_sort.eq_def]
    · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
      rw [VcTermSort.is_finite_dict_value_sort.eq_def]
      cases rawKeyObserved : VcTermSortRaw.is_finite_dict_key_sort key <;>
        cases normalizedKeyObserved : VcTermSort.is_finite_dict_key_sort key <;>
        simp [rawKeyObserved, normalizedKeyObserved] at keyKeyEq ⊢ <;>
        subst_vars
      all_goals try rfl
      cases rawValueObserved : VcTermSortRaw.is_finite_dict_value_sort value <;>
        cases normalizedValueObserved :
          VcTermSort.is_finite_dict_value_sort value <;>
        simp [rawValueObserved, normalizedValueObserved] at valueValueEq ⊢ <;>
        subst_vars <;> rfl
    · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
      rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
      rw [wholeListEq]
  · intro key keyEq
    unfold SortPredicatesCorrespond
    constructor
    · rw [VcTermSortRaw.is_list_element_sort.eq_def]
      rw [VcTermSort.is_list_element_sort.eq_def]
      simp
    · constructor
      · rw [VcTermSortRaw.is_finite_dict_key_sort.eq_def]
        rw [VcTermSort.is_finite_dict_key_sort.eq_def]
      · constructor
        · rw [VcTermSortRaw.is_finite_dict_value_sort.eq_def]
          rw [VcTermSort.is_finite_dict_value_sort.eq_def]
          simp
        · rw [VcTermSortRaw.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSort.is_variadic_tuple_element_sort.eq_def]
          rw [VcTermSortRaw.is_list_element_sort.eq_def]
          rw [VcTermSort.is_list_element_sort.eq_def]
          simp
  · intro child member
    simp at member
  · intro head tail headEq tailEq child member
    simp at member
    rcases member with rfl | member
    · exact headEq
    · exact tailEq child member

theorem raw_is_finite_dict_value_sort_eq_normalized
    (sort : VcTermSort.Sort) :
    VcTermSortRaw.is_finite_dict_value_sort sort =
      VcTermSort.is_finite_dict_value_sort sort :=
  (raw_sort_predicates_eq_normalized sort).2.2.1

theorem raw_is_finite_dict_key_sort_eq_normalized
    (sort : VcTermSort.Sort) :
    VcTermSortRaw.is_finite_dict_key_sort sort =
      VcTermSort.is_finite_dict_key_sort sort :=
  (raw_sort_predicates_eq_normalized sort).2.1

theorem raw_is_list_element_sort_eq_normalized
    (sort : VcTermSort.Sort) :
    VcTermSortRaw.is_list_element_sort sort =
      VcTermSort.is_list_element_sort sort :=
  (raw_sort_predicates_eq_normalized sort).1

theorem raw_is_variadic_tuple_element_sort_eq_normalized
    (sort : VcTermSort.Sort) :
    VcTermSortRaw.is_variadic_tuple_element_sort sort =
      VcTermSort.is_variadic_tuple_element_sort sort :=
  (raw_sort_predicates_eq_normalized sort).2.2.2

theorem raw_is_reference_binder_projection_eq_normalized
    (mapped : VcTermSort.Term) (binder : String) :
    VcTermSortRaw.is_reference_binder_projection mapped binder =
      VcTermSort.is_reference_binder_projection mapped binder := by
  rfl

theorem raw_is_exact_nominal_reference_list_eq_normalized
    (source : VcTermSort.Term) :
    VcTermSortRaw.is_exact_nominal_reference_list source =
      VcTermSort.is_exact_nominal_reference_list source := by
  rw [VcTermSortRaw.is_exact_nominal_reference_list.eq_def]
  rw [VcTermSort.is_exact_nominal_reference_list.eq_def]
  cases source <;> try rfl
  case List sort values =>
    cases sort <;> simp [raw_all_nominal_references_eq_normalized]

theorem raw_require_bound_term_sort_eq_normalized_of_sort
    (binder : String) (binderSort : VcTermSort.Sort)
    (term : VcTermSort.Term) (expected : VcTermSort.Sort)
    (context : VcTermSort.SortContext)
    (sortEq : VcTermSortRaw.Term.sort_typed term =
      VcTermSort.Term.sort_typed term) :
    VcTermSortRaw.require_bound_term_sort binder binderSort term expected context =
      VcTermSort.require_bound_term_sort binder binderSort term expected context := by
  rw [VcTermSortRaw.require_bound_term_sort.eq_def]
  rw [VcTermSort.require_bound_term_sort.eq_def]
  rw [raw_validate_bound_occurrences_eq_normalized term binder binderSort]
  have requireEq : ∀ currentExpected,
      VcTermSortRaw.require_sort term currentExpected context =
        VcTermSort.require_sort term currentExpected context := by
    intro currentExpected
    exact raw_require_sort_eq_normalized_of_sort
      term currentExpected context sortEq
  simp_rw [requireEq]
  rfl

theorem raw_require_comprehension_body_eq_normalized_of_sorts
    (binder : String) (binderSort : VcTermSort.Sort)
    (mapped : VcTermSort.Term) (mappedSort : VcTermSort.Sort)
    (filter : Option VcTermSort.Term)
    (mappedEq : VcTermSortRaw.Term.sort_typed mapped =
      VcTermSort.Term.sort_typed mapped)
    (filterEq : ∀ child, filter = some child →
      VcTermSortRaw.Term.sort_typed child = VcTermSort.Term.sort_typed child) :
    VcTermSortRaw.require_comprehension_body
        binder binderSort mapped mappedSort filter =
      VcTermSort.require_comprehension_body
        binder binderSort mapped mappedSort filter := by
  rw [VcTermSortRaw.require_comprehension_body.eq_def]
  rw [VcTermSort.require_comprehension_body.eq_def]
  rw [raw_require_bound_term_sort_eq_normalized_of_sort
    binder binderSort mapped mappedSort
    VcTermSort.SortContext.ComprehensionMapper mappedEq]
  cases filter with
  | none => rfl
  | some filterTerm =>
      simp only
      rw [raw_require_bound_term_sort_eq_normalized_of_sort
        binder binderSort filterTerm VcTermSort.Sort.Bool
        VcTermSort.SortContext.ComprehensionFilter (filterEq filterTerm rfl)]
      rfl

theorem raw_require_predicate_argument_sorts_loop_eq_normalized_of_children
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenEq : ∀ child, child ∈ iter.slice.val →
      VcTermSortRaw.Term.sort_typed child =
        VcTermSort.Term.sort_typed child) :
    VcTermSortRaw.require_predicate_argument_sorts_loop iter result =
      VcTermSort.require_predicate_argument_sorts_loop iter result := by
  unfold VcTermSortRaw.require_predicate_argument_sorts_loop
  unfold VcTermSort.require_predicate_argument_sorts_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.require_predicate_argument_sorts_loop.body
      state.1 state.2)
    (fun state => VcTermSort.require_predicate_argument_sorts_loop.body
      state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.require_predicate_argument_sorts_loop.body.eq_def]
    rw [VcTermSort.require_predicate_argument_sorts_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail error => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeArgument, next⟩ := pair
        cases maybeArgument with
        | none => simp [observed]
        | some argument =>
            have member := (slice_iterator_next_some_member
              current next argument observed).1
            rw [sliceEq] at member
            have currentEq := childrenEq argument member
            cases currentResult with
            | Err error => simp [core.result.Result.is_ok]
            | Ok unit =>
                simp only [core.result.Result.is_ok]
                simp [currentEq]
                intro value observedValue
                rfl
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        require_predicate_argument_sorts_body_preserves_slice
          state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact require_predicate_argument_sorts_body_decreases
      state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_require_predicate_argument_sorts_eq_normalized_of_children
    (arguments : Slice VcTermSort.Term)
    (childrenEq : ∀ child, child ∈ arguments.val →
      VcTermSortRaw.Term.sort_typed child =
        VcTermSort.Term.sort_typed child) :
    VcTermSortRaw.require_predicate_argument_sorts arguments =
      VcTermSort.require_predicate_argument_sorts arguments := by
  rw [VcTermSortRaw.require_predicate_argument_sorts.eq_def]
  rw [VcTermSort.require_predicate_argument_sorts.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply raw_require_predicate_argument_sorts_loop_eq_normalized_of_children
  simpa using childrenEq

theorem raw_require_permission_transfer_amounts_loop_eq_normalized_of_receivers
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result : core.result.Result Unit VcTermSort.SortError)
    (receiversEq : ∀ amount, amount ∈ iter.slice.val →
      VcTermSortRaw.Term.sort_typed amount.receiver =
        VcTermSort.Term.sort_typed amount.receiver) :
    VcTermSortRaw.require_permission_transfer_amounts_loop iter result =
      VcTermSort.require_permission_transfer_amounts_loop iter result := by
  unfold VcTermSortRaw.require_permission_transfer_amounts_loop
  unfold VcTermSort.require_permission_transfer_amounts_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.require_permission_transfer_amounts_loop.body
      state.1 state.2)
    (fun state => VcTermSort.require_permission_transfer_amounts_loop.body
      state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.require_permission_transfer_amounts_loop.body.eq_def]
    rw [VcTermSort.require_permission_transfer_amounts_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail error => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeAmount, next⟩ := pair
        cases maybeAmount with
        | none => simp [observed]
        | some amount =>
            have member := (slice_iterator_next_some_member
              current next amount observed).1
            rw [sliceEq] at member
            have receiverEq := receiversEq amount member
            have requiredEq := raw_require_sort_eq_normalized_of_sort
              amount.receiver VcTermSort.Sort.Reference
              VcTermSort.SortContext.PermissionTransferReceiver receiverEq
            cases currentResult with
            | Err error => simp [core.result.Result.is_ok]
            | Ok unit =>
                simp only [core.result.Result.is_ok]
                simp [requiredEq]
                intro value observedValue
                rfl
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        require_permission_transfer_amounts_body_preserves_slice
          state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact require_permission_transfer_amounts_body_decreases
      state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_require_permission_transfer_amounts_eq_normalized_of_receivers
    (amounts : Slice VcTermSort.PermissionTransferAmount)
    (receiversEq : ∀ amount, amount ∈ amounts.val →
      VcTermSortRaw.Term.sort_typed amount.receiver =
        VcTermSort.Term.sort_typed amount.receiver) :
    VcTermSortRaw.require_permission_transfer_amounts amounts =
      VcTermSort.require_permission_transfer_amounts amounts := by
  rw [VcTermSortRaw.require_permission_transfer_amounts.eq_def]
  rw [VcTermSort.require_permission_transfer_amounts.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply raw_require_permission_transfer_amounts_loop_eq_normalized_of_receivers
  simpa using receiversEq

theorem raw_require_all_sorts_loop_eq_normalized_of_children
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenEq : ∀ child, child ∈ iter.slice.val →
      VcTermSortRaw.Term.sort_typed child =
        VcTermSort.Term.sort_typed child) :
    VcTermSortRaw.require_all_sorts_loop iter expected context result =
      VcTermSort.require_all_sorts_loop iter expected context result := by
  unfold VcTermSortRaw.require_all_sorts_loop
  unfold VcTermSort.require_all_sorts_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.require_all_sorts_loop.body
      expected context state.1 state.2)
    (fun state => VcTermSort.require_all_sorts_loop.body
      expected context state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.require_all_sorts_loop.body.eq_def]
    rw [VcTermSort.require_all_sorts_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail error => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeValue, next⟩ := pair
        cases maybeValue with
        | none => simp [observed]
        | some value =>
            have member := (slice_iterator_next_some_member
              current next value observed).1
            rw [sliceEq] at member
            have currentEq := childrenEq value member
            have requiredEq : ∀ currentExpected,
                VcTermSortRaw.require_sort value currentExpected context =
                  VcTermSort.require_sort value currentExpected context := by
              intro currentExpected
              exact raw_require_sort_eq_normalized_of_sort
                value currentExpected context currentEq
            cases currentResult with
            | Err error => simp [core.result.Result.is_ok]
            | Ok unit =>
                simp only [core.result.Result.is_ok]
                simp [requiredEq]
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        require_all_sorts_body_preserves_slice expected context
          state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact require_all_sorts_body_decreases expected context
      state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_require_all_sorts_eq_normalized_of_children
    (values : Slice VcTermSort.Term)
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (childrenEq : ∀ child, child ∈ values.val →
      VcTermSortRaw.Term.sort_typed child =
        VcTermSort.Term.sort_typed child) :
    VcTermSortRaw.require_all_sorts values expected context =
      VcTermSort.require_all_sorts values expected context := by
  rw [VcTermSortRaw.require_all_sorts.eq_def]
  rw [VcTermSort.require_all_sorts.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply raw_require_all_sorts_loop_eq_normalized_of_children
  simpa using childrenEq

theorem raw_require_variadic_tuple_element_sorts_loop_eq_normalized_of_children
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (expected : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (childrenEq : ∀ child, child ∈ iter.slice.val →
      VcTermSortRaw.Term.sort_typed child =
        VcTermSort.Term.sort_typed child) :
    VcTermSortRaw.require_variadic_tuple_element_sorts_loop
        iter expected result =
      VcTermSort.require_variadic_tuple_element_sorts_loop
        iter expected result := by
  unfold VcTermSortRaw.require_variadic_tuple_element_sorts_loop
  unfold VcTermSort.require_variadic_tuple_element_sorts_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state =>
      VcTermSortRaw.require_variadic_tuple_element_sorts_loop.body
        expected state.1 state.2)
    (fun state =>
      VcTermSort.require_variadic_tuple_element_sorts_loop.body
        expected state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.require_variadic_tuple_element_sorts_loop.body.eq_def]
    rw [VcTermSort.require_variadic_tuple_element_sorts_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail error => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeValue, next⟩ := pair
        cases maybeValue with
        | none => simp [observed]
        | some value =>
            have member := (slice_iterator_next_some_member
              current next value observed).1
            rw [sliceEq] at member
            have currentEq := childrenEq value member
            cases currentResult with
            | Err error => simp [core.result.Result.is_ok]
            | Ok unit =>
                simp only [core.result.Result.is_ok]
                simp [currentEq]
                intro valueResult observedValue
                rfl
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        require_variadic_tuple_element_sorts_body_preserves_slice
          expected state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact require_variadic_tuple_element_sorts_body_decreases
      expected state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_require_variadic_tuple_element_sorts_eq_normalized_of_children
    (values : Slice VcTermSort.Term)
    (expected : VcTermSort.Sort)
    (childrenEq : ∀ child, child ∈ values.val →
      VcTermSortRaw.Term.sort_typed child =
        VcTermSort.Term.sort_typed child) :
    VcTermSortRaw.require_variadic_tuple_element_sorts values expected =
      VcTermSort.require_variadic_tuple_element_sorts values expected := by
  rw [VcTermSortRaw.require_variadic_tuple_element_sorts.eq_def]
  rw [VcTermSort.require_variadic_tuple_element_sorts.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply raw_require_variadic_tuple_element_sorts_loop_eq_normalized_of_children
  simpa using childrenEq

theorem raw_collect_sorts_loop_eq_normalized_of_children
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (sorts : VcTermSort.ModelVec VcTermSort.Sort)
    (error : Option VcTermSort.SortError)
    (childrenEq : ∀ child, child ∈ iter.slice.val →
      VcTermSortRaw.Term.sort_typed child =
        VcTermSort.Term.sort_typed child) :
    VcTermSortRaw.collect_sorts_loop iter sorts error =
      VcTermSort.collect_sorts_loop iter sorts error := by
  unfold VcTermSortRaw.collect_sorts_loop
  unfold VcTermSort.collect_sorts_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.collect_sorts_loop.body
      state.1 state.2.1 state.2.2)
    (fun state => VcTermSort.collect_sorts_loop.body
      state.1 state.2.1 state.2.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentSorts, currentError⟩ := state
    rw [VcTermSortRaw.collect_sorts_loop.body.eq_def]
    rw [VcTermSort.collect_sorts_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail iteratorError => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeValue, next⟩ := pair
        cases maybeValue with
        | none => simp [observed]
        | some value =>
            have member := (slice_iterator_next_some_member
              current next value observed).1
            rw [sliceEq] at member
            have currentEq := childrenEq value member
            cases currentError with
            | some current => simp [core.option.Option.is_none]
            | none =>
                simp only [core.option.Option.is_none]
                simp [currentEq]
                intro checked observedChecked
                rfl
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        collect_sorts_body_preserves_slice
          state.1 next.1 state.2.1 next.2.1 state.2.2 next.2.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact collect_sorts_body_decreases
      state.1 next.1 state.2.1 next.2.1 state.2.2 next.2.2 continued
  · rfl

theorem raw_collect_sorts_eq_normalized_of_children
    (values : Slice VcTermSort.Term)
    (childrenEq : ∀ child, child ∈ values.val →
      VcTermSortRaw.Term.sort_typed child =
        VcTermSort.Term.sort_typed child) :
    VcTermSortRaw.collect_sorts values =
      VcTermSort.collect_sorts values := by
  rw [VcTermSortRaw.collect_sorts.eq_def]
  rw [VcTermSort.collect_sorts.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  rw [raw_collect_sorts_loop_eq_normalized_of_children]
  · rfl
  · simpa using childrenEq

theorem raw_require_finite_dict_entry_sorts_loop_eq_normalized_of_entries
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (keySort valueSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError)
    (entriesEq : ∀ entry, entry ∈ iter.slice.val →
      (VcTermSortRaw.Term.sort_typed entry.1 =
        VcTermSort.Term.sort_typed entry.1) ∧
      (VcTermSortRaw.Term.sort_typed entry.2 =
        VcTermSort.Term.sort_typed entry.2)) :
    VcTermSortRaw.require_finite_dict_entry_sorts_loop
        iter keySort valueSort result =
      VcTermSort.require_finite_dict_entry_sorts_loop
        iter keySort valueSort result := by
  unfold VcTermSortRaw.require_finite_dict_entry_sorts_loop
  unfold VcTermSort.require_finite_dict_entry_sorts_loop
  apply partial_loop_eq_fuel_of_invariant
    (fun state => VcTermSortRaw.require_finite_dict_entry_sorts_loop.body
      keySort valueSort state.1 state.2)
    (fun state => VcTermSort.require_finite_dict_entry_sorts_loop.body
      keySort valueSort state.1 state.2)
    (fun state => state.1.slice = iter.slice)
    (fun state => sliceIteratorRemaining state.1)
  · intro state sliceEq
    obtain ⟨current, currentResult⟩ := state
    rw [VcTermSortRaw.require_finite_dict_entry_sorts_loop.body.eq_def]
    rw [VcTermSort.require_finite_dict_entry_sorts_loop.body.eq_def]
    cases observed : core.slice.iter.IteratorSliceIter.next current with
    | fail iteratorError => simp [observed]
    | div => simp [observed]
    | ok pair =>
        obtain ⟨maybeEntry, next⟩ := pair
        cases maybeEntry with
        | none => simp [observed]
        | some entry =>
            obtain ⟨key, value⟩ := entry
            have member := (slice_iterator_next_some_member
              current next (key, value) observed).1
            rw [sliceEq] at member
            have currentEq := entriesEq (key, value) member
            have keyRequiredEq : ∀ currentExpected,
                VcTermSortRaw.require_sort key currentExpected
                    VcTermSort.SortContext.FiniteDictionaryKey =
                  VcTermSort.require_sort key currentExpected
                    VcTermSort.SortContext.FiniteDictionaryKey := by
              intro currentExpected
              exact raw_require_sort_eq_normalized_of_sort key currentExpected
                VcTermSort.SortContext.FiniteDictionaryKey currentEq.1
            have valueRequiredEq : ∀ currentExpected,
                VcTermSortRaw.require_sort value currentExpected
                    VcTermSort.SortContext.FiniteDictionaryValue =
                  VcTermSort.require_sort value currentExpected
                    VcTermSort.SortContext.FiniteDictionaryValue := by
              intro currentExpected
              exact raw_require_sort_eq_normalized_of_sort value currentExpected
                VcTermSort.SortContext.FiniteDictionaryValue currentEq.2
            cases currentResult with
            | Err error => simp [core.result.Result.is_ok]
            | Ok unit =>
                simp only [core.result.Result.is_ok]
                simp [keyRequiredEq, valueRequiredEq]
                intro clonedKey keyCloneObserved keyResult keyObserved
                rfl
  · intro state next sliceEq continued
    calc
      next.1.slice = state.1.slice :=
        require_finite_dict_entry_sorts_body_preserves_slice keySort valueSort
          state.1 next.1 state.2 next.2 continued
      _ = iter.slice := sliceEq
  · intro state next continued
    exact require_finite_dict_entry_sorts_body_decreases keySort valueSort
      state.1 next.1 state.2 next.2 continued
  · rfl

theorem raw_require_finite_dict_entry_sorts_eq_normalized_of_entries
    (entries : Slice (VcTermSort.Term × VcTermSort.Term))
    (keySort valueSort : VcTermSort.Sort)
    (entriesEq : ∀ entry, entry ∈ entries.val →
      (VcTermSortRaw.Term.sort_typed entry.1 =
        VcTermSort.Term.sort_typed entry.1) ∧
      (VcTermSortRaw.Term.sort_typed entry.2 =
        VcTermSort.Term.sort_typed entry.2)) :
    VcTermSortRaw.require_finite_dict_entry_sorts entries keySort valueSort =
      VcTermSort.require_finite_dict_entry_sorts entries keySort valueSort := by
  rw [VcTermSortRaw.require_finite_dict_entry_sorts.eq_def]
  rw [VcTermSort.require_finite_dict_entry_sorts.eq_def]
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok]
  apply raw_require_finite_dict_entry_sorts_loop_eq_normalized_of_entries
  simpa using entriesEq

theorem set_comprehension_tuple_prefix_preserved
    (source mapped : VcTermSort.Term) (binder : String)
    (elementSort : VcTermSort.Sort) (filter : Option VcTermSort.Term)
    (outBinder : String) (outElementSort : VcTermSort.Sort)
    (outMapped : VcTermSort.Term) (outFilter : Option VcTermSort.Term)
    (outExact : Bool)
    (observed : (do
      let exactReference ← VcTermSort.is_exact_nominal_reference_list source
      let exactIdentity ← if exactReference = true then
          VcTermSort.is_reference_binder_projection mapped binder
        else ok false
      ok (binder, elementSort, mapped, filter, exactIdentity)) =
        ok (outBinder, outElementSort, outMapped, outFilter, outExact)) :
    outBinder = binder ∧ outElementSort = elementSort ∧
      outMapped = mapped ∧ outFilter = filter := by
  cases exactObserved : VcTermSort.is_exact_nominal_reference_list source with
  | fail error => simp [exactObserved] at observed
  | div => simp [exactObserved] at observed
  | ok exactReference =>
      cases exactReference with
      | false =>
          simp [exactObserved] at observed
          simp_all
      | true =>
          cases projectionObserved :
              VcTermSort.is_reference_binder_projection mapped binder with
          | fail error => simp [exactObserved, projectionObserved] at observed
          | div => simp [exactObserved, projectionObserved] at observed
          | ok projection =>
              simp [exactObserved, projectionObserved] at observed
              simp_all

set_option maxHeartbeats 1000000 in
theorem raw_term_sort_typed_eq_normalized (term : VcTermSort.Term) :
    VcTermSortRaw.Term.sort_typed term = VcTermSort.Term.sort_typed term := by
  apply term_strictly_smaller_well_founded.induction term
  intro current smallerEq
  rw [VcTermSortRaw.Term.sort_typed.eq_def]
  rw [VcTermSort.Term.sort_typed.eq_def]
  cases current <;>
    simp_all [TermStrictlySmaller,
      raw_validate_int_enum_descriptor_eq_normalized,
      raw_all_nominal_references_eq_normalized,
      raw_all_nominal_reference_keys_eq_normalized,
      raw_is_finite_dict_value_sort_eq_normalized,
      raw_is_finite_dict_key_sort_eq_normalized,
      raw_is_list_element_sort_eq_normalized,
      raw_is_variadic_tuple_element_sort_eq_normalized,
      raw_is_reference_binder_projection_eq_normalized,
      raw_is_exact_nominal_reference_list_eq_normalized,
      raw_require_sort_eq_normalized_of_sort,
      raw_require_bound_term_sort_eq_normalized_of_sort,
      raw_require_comprehension_body_eq_normalized_of_sorts,
      raw_require_predicate_argument_sorts_eq_normalized_of_children,
      raw_require_permission_transfer_amounts_eq_normalized_of_receivers,
      raw_require_all_sorts_eq_normalized_of_children,
      raw_require_variadic_tuple_element_sorts_eq_normalized_of_children,
      raw_collect_sorts_eq_normalized_of_children,
      raw_require_finite_dict_entry_sorts_eq_normalized_of_entries,
      box_ne_refines, core.cmp.PartialEq.ne.trait_default,
      core.cmp.PartialEq.ne.default, VcTermSort.sortPartialEqModel]
  all_goals intros
  all_goals repeat' rw [smallerEq _ (by omega)]
  all_goals repeat' rw [raw_require_sort_eq_normalized_of_sort
    _ _ _ (smallerEq _ (by omega))]
  all_goals repeat' rw [raw_require_bound_term_sort_eq_normalized_of_sort
    _ _ _ _ _ (smallerEq _ (by omega))]
  all_goals repeat' rw [raw_require_comprehension_body_eq_normalized_of_sorts
    _ _ _ _ _ (smallerEq _ (by omega)) (by
      intro child present
      apply smallerEq
      have presentSize := congrArg sizeOf present
      simp at presentSize
      omega)]
  all_goals try simp_rw [raw_require_comprehension_body_eq_normalized_of_sorts
    _ _ _ _ _ (smallerEq _ (by omega)) (by
      intro child present
      apply smallerEq
      have presentSize := congrArg sizeOf present
      simp at presentSize
      omega)]
  all_goals repeat' rw [raw_require_predicate_argument_sorts_eq_normalized_of_children
    _ (by
      intro child member
      apply smallerEq
      have childBelow := List.sizeOf_lt_of_mem (model_vec_deref_member member)
      simp at childBelow
      omega)]
  all_goals repeat' rw [raw_require_all_sorts_eq_normalized_of_children
    _ _ _ (by
      intro child member
      apply smallerEq
      have childBelow := List.sizeOf_lt_of_mem (model_vec_deref_member member)
      simp at childBelow
      omega)]
  all_goals repeat' rw [raw_require_variadic_tuple_element_sorts_eq_normalized_of_children
    _ _ (by
      intro child member
      apply smallerEq
      have childBelow := List.sizeOf_lt_of_mem (model_vec_deref_member member)
      simp at childBelow
      omega)]
  all_goals repeat' rw [raw_collect_sorts_eq_normalized_of_children
    _ (by
      intro child member
      apply smallerEq
      have childBelow := List.sizeOf_lt_of_mem (model_vec_deref_member member)
      simp at childBelow
      omega)]
  all_goals repeat' rw [raw_require_permission_transfer_amounts_eq_normalized_of_receivers
    _ (by
      intro amount member
      apply smallerEq
      have amountBelow := List.sizeOf_lt_of_mem (model_vec_deref_member member)
      simp at amountBelow
      cases amount
      simp at amountBelow ⊢
      omega)]
  all_goals repeat' rw [raw_require_finite_dict_entry_sorts_eq_normalized_of_entries
    _ _ _ (by
      intro entry member
      have entryBelow := List.sizeOf_lt_of_mem (model_vec_deref_member member)
      simp at entryBelow
      rcases entry with ⟨key, value⟩
      constructor <;> apply smallerEq <;>
        simp at entryBelow ⊢ <;> omega)]
  all_goals try simp_rw [raw_require_finite_dict_entry_sorts_eq_normalized_of_entries
    _ _ _ (by
      intro entry member
      have entryBelow := List.sizeOf_lt_of_mem (model_vec_deref_member member)
      simp at entryBelow
      rcases entry with ⟨key, value⟩
      constructor <;> apply smallerEq <;>
        simp at entryBelow ⊢ <;> omega)]
  all_goals try rfl
  case ListComprehension resultName source binder elementSort mapped filter =>
    have bodyEq : ∀ sourceElement,
        VcTermSortRaw.require_comprehension_body
            binder sourceElement mapped elementSort filter =
          VcTermSort.require_comprehension_body
            binder sourceElement mapped elementSort filter := by
      intro sourceElement
      apply raw_require_comprehension_body_eq_normalized_of_sorts
      · apply smallerEq
        omega
      · intro child present
        apply smallerEq
        have presentSize := congrArg sizeOf present
        simp at presentSize
        omega
    cases sourceObserved : VcTermSort.Term.sort_typed source with
    | fail error => simp [sourceObserved]
    | div => simp [sourceObserved]
    | ok sourceResult =>
        cases sourceResult with
        | Err error =>
            simp [sourceObserved,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        | Ok sourceSort =>
            cases sourceSort <;>
              simp [sourceObserved,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                bodyEq]
            all_goals aesop
  case SetComprehension resultName source binder elementSort mapped filter =>
    have bodyEq : ∀ sourceElement,
        VcTermSortRaw.require_comprehension_body
            binder sourceElement mapped elementSort filter =
          VcTermSort.require_comprehension_body
            binder sourceElement mapped elementSort filter := by
      intro sourceElement
      apply raw_require_comprehension_body_eq_normalized_of_sorts
      · apply smallerEq
        omega
      · intro child present
        apply smallerEq
        have presentSize := congrArg sizeOf present
        simp at presentSize
        omega
    cases sourceObserved : VcTermSort.Term.sort_typed source with
    | fail error => simp [sourceObserved]
    | div => simp [sourceObserved]
    | ok sourceResult =>
        cases sourceResult with
        | Err error =>
            simp [sourceObserved,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        | Ok sourceSort =>
            cases sourceSort <;>
              simp [sourceObserved,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                bodyEq]
            all_goals aesop
            all_goals
              have fields := set_comprehension_tuple_prefix_preserved
                source mapped binder elementSort filter _ _ _ _ _ (by assumption)
              rcases fields with ⟨binderEq, elementSortEq, mappedEq, filterEq⟩
              simp_all [bodyEq]
            all_goals intros <;> subst_vars <;> rfl
  case DictComprehension resultName source binder keySort valueSort key value filter =>
    have bodyEq : ∀ sourceElement,
        VcTermSortRaw.require_comprehension_body
            binder sourceElement key keySort filter =
          VcTermSort.require_comprehension_body
            binder sourceElement key keySort filter := by
      intro sourceElement
      apply raw_require_comprehension_body_eq_normalized_of_sorts
      · apply smallerEq
        omega
      · intro child present
        apply smallerEq
        have presentSize := congrArg sizeOf present
        simp at presentSize
        omega
    have valueEq : ∀ sourceElement,
        VcTermSortRaw.require_bound_term_sort
            binder sourceElement value valueSort VcTermSort.SortContext.DictionaryValue =
          VcTermSort.require_bound_term_sort
            binder sourceElement value valueSort VcTermSort.SortContext.DictionaryValue := by
      intro sourceElement
      apply raw_require_bound_term_sort_eq_normalized_of_sort
      apply smallerEq
      omega
    cases sourceObserved : VcTermSort.Term.sort_typed source with
    | fail error => simp [sourceObserved]
    | div => simp [sourceObserved]
    | ok sourceResult =>
        cases sourceResult with
        | Err error =>
            simp [sourceObserved,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        | Ok sourceSort =>
            cases sourceSort <;>
              simp [sourceObserved,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                bodyEq, valueEq]
            all_goals aesop
  case FiniteDict => aesop

theorem raw_term_sort_extraction_entrypoint_eq_normalized
    (term : VcTermSort.Term) :
    VcTermSortRaw.term_sort_extraction_entrypoint term =
      VcTermSort.term_sort_extraction_entrypoint term := by
  rw [VcTermSortRaw.term_sort_extraction_entrypoint.eq_def]
  rw [VcTermSort.term_sort_extraction_entrypoint.eq_def]
  exact raw_term_sort_typed_eq_normalized term

end VcTermSort.Proofs
